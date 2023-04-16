// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"fmt"
)

type loop struct {
	header *Block // The header node of this (reducible) loop
	outer  *loop  // loop containing this loop

	// By default, children, exits, and depth are not initialized.
	children []*loop  // loops nested directly within this loop. Initialized by assembleChildren().
	exits    []*Block // exits records blocks reached by exits from this loop. Initialized by findExits().

	// Next three fields used by regalloc and/or
	// aid in computation of inner-ness and list of blocks.
	nBlocks int32 // Number of blocks in this loop but not within inner loops
	depth   int16 // Nesting depth of the loop; 1 is outermost. Initialized by calculateDepths().
	isInner bool  // True if never discovered to contain a loop		不包含其他循环,表示当前循环是最内层的循环

	// register allocation uses this.
	containsUnavoidableCall bool // True if all paths through the loop have a call
}

// outerinner records that outer contains inner
func (sdom SparseTree) outerinner(outer, inner *loop) {
	// There could be other outer loops found in some random order,
	// locate the new outer loop appropriately among them.

	// Outer loop headers dominate inner loop headers.
	// Use this to put the "new" "outer" loop in the right place.
	oldouter := inner.outer                                                 // 获取inner之前记录的外部循环
	for oldouter != nil && sdom.isAncestor(outer.header, oldouter.header) { // outer包含之前的外部循环
		// outer -> oldouter -> inner,只要记录outer包含oldouter即可,这里还要注意outer != oldouter
		inner = oldouter
		oldouter = inner.outer
	}
	if outer == oldouter { // 说明outer已经记录了包含inner
		return
	}
	if oldouter != nil { // oldouter不为nil也不等于outer,说明oldouter包含outer且outer包含inner
		sdom.outerinner(oldouter, outer) // 记录oldouter包含outer
	}

	inner.outer = outer // records that outer contains inner
	outer.isInner = false
}

func checkContainsCall(bb *Block) bool {
	if bb.Kind == BlockDefer {
		return true
	}
	for _, v := range bb.Values {
		if opcodeTable[v.Op].call {
			return true
		}
	}
	return false
}

type loopnest struct {
	f              *Func
	b2l            []*loop  // 块ID对应一个loop结构体,块在这个循环内
	po             []*Block // 倒序遍历的块
	sdom           SparseTree
	loops          []*loop
	hasIrreducible bool // TODO current treatment of irreducible loops is very flaky, if accurate loops are needed, must punt at function level.

	// Record which of the lazily initialized fields have actually been initialized.
	initializedChildren, initializedDepth, initializedExits bool
}

func min8(a, b int8) int8 {
	if a < b {
		return a
	}
	return b
}

func max8(a, b int8) int8 {
	if a > b {
		return a
	}
	return b
}

const (
	blDEFAULT = 0
	blMin     = blDEFAULT
	blCALL    = 1
	blRET     = 2
	blEXIT    = 3
)

var bllikelies = [4]string{"default", "call", "ret", "exit"}

func describePredictionAgrees(b *Block, prediction BranchPrediction) string {
	s := ""
	if prediction == b.Likely {
		s = " (agrees with previous)"
	} else if b.Likely != BranchUnknown {
		s = " (disagrees with previous, ignored)"
	}
	return s
}

func describeBranchPrediction(f *Func, b *Block, likely, not int8, prediction BranchPrediction) {
	f.Warnl(b.Pos, "Branch prediction rule %s < %s%s",
		bllikelies[likely-blMin], bllikelies[not-blMin], describePredictionAgrees(b, prediction))
}

func likelyadjust(f *Func) {
	// The values assigned to certain and local only matter
	// in their rank order.  0 is default, more positive
	// is less likely. It's possible to assign a negative
	// unlikeliness (though not currently the case).
	certain := make([]int8, f.NumBlocks()) // In the long run, all outcomes are at least this bad. Mainly for Exit
	local := make([]int8, f.NumBlocks())   // for our immediate predecessors.

	po := f.postorder()  // 倒序遍历块的列表
	nest := f.loopnest() // 函数中的循环信息
	b2l := nest.b2l

	for _, b := range po {
		switch b.Kind {
		case BlockExit:
			// Very unlikely.
			local[b.ID] = blEXIT
			certain[b.ID] = blEXIT

			// Ret, it depends.
		case BlockRet, BlockRetJmp:
			local[b.ID] = blRET
			certain[b.ID] = blRET

			// Calls. TODO not all calls are equal, names give useful clues.
			// Any name-based heuristics are only relative to other calls,
			// and less influential than inferences from loop structure.
		case BlockDefer:
			local[b.ID] = blCALL
			certain[b.ID] = max8(blCALL, certain[b.Succs[0].b.ID])

		default:
			if len(b.Succs) == 1 {
				certain[b.ID] = certain[b.Succs[0].b.ID]
			} else if len(b.Succs) == 2 { // if块
				// If successor is an unvisited backedge, it's in loop and we don't care.
				// Its default unlikely is also zero which is consistent with favoring loop edges.
				// Notice that this can act like a "reset" on unlikeliness at loops; the
				// default "everything returns" unlikeliness is erased by min with the
				// backedge likeliness; however a loop with calls on every path will be
				// tagged with call cost. Net effect is that loop entry is favored.
				b0 := b.Succs[0].b.ID
				b1 := b.Succs[1].b.ID
				certain[b.ID] = min8(certain[b0], certain[b1]) // 取较小的

				l := b2l[b.ID] // 获取三个块的循环结构体
				l0 := b2l[b0]
				l1 := b2l[b1]

				prediction := b.Likely
				// Weak loop heuristic -- both source and at least one dest are in loops,
				// and there is a difference in the destinations.
				// TODO what is best arrangement for nested loops?
				if l != nil && l0 != l1 { // b块是循环头且两个分支可能存在循环
					noprediction := false
					switch {
					// prefer not to exit loops
					case l1 == nil: // false分支不是循环
						prediction = BranchLikely
					case l0 == nil: // true分支不是循环
						prediction = BranchUnlikely

						// prefer to stay in loop, not exit to outer.
					case l == l0: // b块判断为true时自循环
						prediction = BranchLikely
					case l == l1: // b块判断为fasle时自循环
						prediction = BranchUnlikely
					default:
						noprediction = true
					}
					if f.pass.debug > 0 && !noprediction {
						f.Warnl(b.Pos, "Branch prediction rule stay in loop%s",
							describePredictionAgrees(b, prediction))
					}

				} else {
					// Lacking loop structure, fall back on heuristics.
					if certain[b1] > certain[b0] {
						prediction = BranchLikely
						if f.pass.debug > 0 {
							describeBranchPrediction(f, b, certain[b0], certain[b1], prediction)
						}
					} else if certain[b0] > certain[b1] {
						prediction = BranchUnlikely
						if f.pass.debug > 0 {
							describeBranchPrediction(f, b, certain[b1], certain[b0], prediction)
						}
					} else if local[b1] > local[b0] {
						prediction = BranchLikely
						if f.pass.debug > 0 {
							describeBranchPrediction(f, b, local[b0], local[b1], prediction)
						}
					} else if local[b0] > local[b1] {
						prediction = BranchUnlikely
						if f.pass.debug > 0 {
							describeBranchPrediction(f, b, local[b1], local[b0], prediction)
						}
					}
				}
				if b.Likely != prediction {
					if b.Likely == BranchUnknown {
						b.Likely = prediction
					}
				}
			}
			// Look for calls in the block.  If there is one, make this block unlikely.
			for _, v := range b.Values {
				if opcodeTable[v.Op].call {
					local[b.ID] = blCALL
					certain[b.ID] = max8(blCALL, certain[b.Succs[0].b.ID])
				}
			}
		}
		if f.pass.debug > 2 {
			f.Warnl(b.Pos, "BP: Block %s, local=%s, certain=%s", b, bllikelies[local[b.ID]-blMin], bllikelies[certain[b.ID]-blMin])
		}

	}
}

func (l *loop) String() string {
	return fmt.Sprintf("hdr:%s", l.header)
}

func (l *loop) LongString() string {
	i := ""
	o := ""
	if l.isInner {
		i = ", INNER"
	}
	if l.outer != nil {
		o = ", o=" + l.outer.header.String()
	}
	return fmt.Sprintf("hdr:%s%s%s", l.header, i, o)
}

func (l *loop) isWithinOrEq(ll *loop) bool {
	if ll == nil { // nil means whole program
		return true
	}
	for ; l != nil; l = l.outer {
		if l == ll {
			return true
		}
	}
	return false
}

// nearestOuterLoop returns the outer loop of loop most nearly
// containing block b; the header must dominate b.  loop itself
// is assumed to not be that loop. For acceptable performance,
// we're relying on loop nests to not be terribly deep.
func (l *loop) nearestOuterLoop(sdom SparseTree, b *Block) *loop {
	var o *loop
	for o = l.outer; o != nil && !sdom.IsAncestorEq(o.header, b); o = o.outer {
	}
	return o
}

func loopnestfor(f *Func) *loopnest {
	po := f.postorder()
	sdom := f.Sdom()
	b2l := make([]*loop, f.NumBlocks())    // 循环头的块ID对应一个loop结构体
	loops := make([]*loop, 0)              // 保存所有的loop结构体
	visited := make([]bool, f.NumBlocks()) // 标记一个块是否被访问过
	sawIrred := false

	if f.pass.debug > 2 {
		fmt.Printf("loop finding in %s\n", f.Name)
	}

	// Reducible-loop-nest-finding.
	for _, b := range po { // 倒序遍历所有块
		if f.pass != nil && f.pass.debug > 3 {
			fmt.Printf("loop finding at %s\n", b)
		}

		var innermost *loop // innermost header reachable from this block

		// IF any successor s of b is in a loop headed by h
		// AND h dominates b
		// THEN b is in the loop headed by h.
		//
		// Choose the first/innermost such h.
		//
		// IF s itself dominates b, then s is a loop header;
		// and there may be more than one such s.
		// Since there's at most 2 successors, the inner/outer ordering
		// between them can be established with simple comparisons.
		for _, e := range b.Succs { // 遍历b的后继
			bb := e.b       // 获取后继块
			l := b2l[bb.ID] // 获取后继块ID对应的loop结构体指针
			// bb是b的后继还是b的支配节点,这种情况下bb必定是一个循环头部,b是一个循环的尾部块
			if sdom.IsAncestorEq(bb, b) { // Found a loop header
				if f.pass != nil && f.pass.debug > 4 {
					fmt.Printf("loop finding    succ %s of %s is header\n", bb.String(), b.String())
				}
				if l == nil { // 这是一个新发现的循环
					l = &loop{header: bb, isInner: true}
					loops = append(loops, l)
					b2l[bb.ID] = l
				}
			} else if !visited[bb.ID] { // Found an irreducible loop
				// 所有的块是倒序遍历的,一个块的后继都访问完毕后才会添加到列表中,所以bb应该在b之前被访问,这种情况应该不会发生
				sawIrred = true
				if f.pass != nil && f.pass.debug > 4 {
					fmt.Printf("loop finding    succ %s of %s is IRRED, in %s\n", bb.String(), b.String(), f.Name)
				}
			} else if l != nil { // 当前块已经找到了一个循环头了
				// TODO handle case where l is irreducible.
				// Perhaps a loop header is inherited.
				// is there any loop containing our successor whose
				// header dominates b?
				if !sdom.IsAncestorEq(l.header, b) { // 已存在的循环头不是b的祖先
					l = l.nearestOuterLoop(sdom, b) // 获取最近的支配b块的外层循环
				}
				if f.pass != nil && f.pass.debug > 4 {
					if l == nil {
						fmt.Printf("loop finding    succ %s of %s has no loop\n", bb.String(), b.String())
					} else {
						fmt.Printf("loop finding    succ %s of %s provides loop with header %s\n", bb.String(), b.String(), l.header.String())
					}
				}
			} else { // No loop
				if f.pass != nil && f.pass.debug > 4 {
					fmt.Printf("loop finding    succ %s of %s has no loop\n", bb.String(), b.String())
				}

			}

			if l == nil || innermost == l { // bb块不是一个循环的头结点或者l不是一个新的循环
				continue
			}
			// l不为nil且innermost == nil
			// 到这里表示找到了一个新的循环
			if innermost == nil { // 记录innermost为当前找到的loop
				innermost = l
				continue
			}
			// 处理innermost与l这两个不同循环的嵌套关系
			if sdom.isAncestor(innermost.header, l.header) { // innermost支配l,说明innermost循环包含l循环
				sdom.outerinner(innermost, l) // 记录innermost包含l
				innermost = l                 // 标记l是最内层的循环
			} else if sdom.isAncestor(l.header, innermost.header) {
				sdom.outerinner(l, innermost) // 记录l包含innermost
			}
		}

		if innermost != nil {
			// 块是倒序遍历的,所以某个循环尾部的b块可以找到一个循环,之后访问前面的b的前驱块时会在上面的l := b2l[bb.ID]中获取相同的loop结构体指针
			b2l[b.ID] = innermost // 记录b块所在的循环
			innermost.nBlocks++
		}
		visited[b.ID] = true
	}

	ln := &loopnest{f: f, b2l: b2l, po: po, sdom: sdom, loops: loops, hasIrreducible: sawIrred}

	// Calculate containsUnavoidableCall for regalloc
	dominatedByCall := make([]bool, f.NumBlocks()) // 记录某个块中有函数调用
	for _, b := range po {
		if checkContainsCall(b) {
			dominatedByCall[b.ID] = true
		}
	}
	// Run dfs to find path through the loop that avoids all calls.
	// Such path either escapes loop or return back to header.
	// It isn't enough to have exit not dominated by any call, for example:
	// ... some loop
	// call1   call2
	//   \      /
	//     exit
	// ...
	// exit is not dominated by any call, but we don't have call-free path to it.
	for _, l := range loops { // 遍历当前函数中的所有循环
		// Header contains call.
		if dominatedByCall[l.header.ID] { // 循环头有函数调用
			l.containsUnavoidableCall = true
			continue
		}
		callfreepath := false
		tovisit := make([]*Block, 0, len(l.header.Succs)) // 保存循环包含的块
		// Push all non-loop non-exit successors of header onto toVisit.
		for _, s := range l.header.Succs {
			nb := s.Block() // 获取循环头的后继块
			// This corresponds to loop with zero iterations.
			if !l.iterationEnd(nb, b2l) { // 块nb不能代表l循环的结束
				tovisit = append(tovisit, nb)
			}
		}
		for len(tovisit) > 0 {
			cur := tovisit[len(tovisit)-1]
			tovisit = tovisit[:len(tovisit)-1] // tovisit中弹出最后一项
			if dominatedByCall[cur.ID] {       // 当前的块有函数调用
				continue
			}
			// Record visited in dominatedByCall.
			dominatedByCall[cur.ID] = true
			for _, s := range cur.Succs {
				nb := s.Block()              // 当前块的后继块
				if l.iterationEnd(nb, b2l) { // nb是l循环的末尾,表示有办法通过这个循环而不会有函数调用
					callfreepath = true // 感觉这一行下面可以加上break
				}
				if !dominatedByCall[nb.ID] { // 后继块没有函数调用就加入到tovisit继续进行遍历
					tovisit = append(tovisit, nb)
				}

			}
			if callfreepath {
				break
			}
		}
		if !callfreepath {
			l.containsUnavoidableCall = true
		}
	}

	// Curious about the loopiness? "-d=ssa/likelyadjust/stats"
	if f.pass != nil && f.pass.stats > 0 && len(loops) > 0 {
		ln.assembleChildren()
		ln.calculateDepths()
		ln.findExits()

		// Note stats for non-innermost loops are slightly flawed because
		// they don't account for inner loop exits that span multiple levels.

		for _, l := range loops { // 这个循环主要用于打印状态信息
			x := len(l.exits)
			cf := 0
			if !l.containsUnavoidableCall {
				cf = 1
			}
			inner := 0
			if l.isInner {
				inner++
			}

			f.LogStat("loopstats:",
				l.depth, "depth", x, "exits",
				inner, "is_inner", cf, "always_calls", l.nBlocks, "n_blocks")
		}
	}

	if f.pass != nil && f.pass.debug > 1 && len(loops) > 0 {
		fmt.Printf("Loops in %s:\n", f.Name)
		for _, l := range loops {
			fmt.Printf("%s, b=", l.LongString())
			for _, b := range f.Blocks {
				if b2l[b.ID] == l {
					fmt.Printf(" %s", b)
				}
			}
			fmt.Print("\n")
		}
		fmt.Printf("Nonloop blocks in %s:", f.Name)
		for _, b := range f.Blocks {
			if b2l[b.ID] == nil {
				fmt.Printf(" %s", b)
			}
		}
		fmt.Print("\n")
	}
	return ln
}

// assembleChildren initializes the children field of each
// loop in the nest.  Loop A is a child of loop B if A is
// directly nested within B (based on the reducible-loops
// detection above)
func (ln *loopnest) assembleChildren() { // 构建父子循环关系
	if ln.initializedChildren {
		return
	}
	for _, l := range ln.loops {
		if l.outer != nil { // 有外层循环
			l.outer.children = append(l.outer.children, l) // 当前的循环作为外层循环的孩子
		}
	}
	ln.initializedChildren = true
}

// calculateDepths uses the children field of loops
// to determine the nesting depth (outer=1) of each
// loop.  This is helpful for finding exit edges.
func (ln *loopnest) calculateDepths() { // 设置最外层的循环的depth为1
	if ln.initializedDepth {
		return
	}
	ln.assembleChildren() // 构建父子关系
	for _, l := range ln.loops {
		if l.outer == nil { // 最外层的循环
			l.setDepth(1)
		}
	}
	ln.initializedDepth = true
}

// findExits uses loop depth information to find the
// exits from a loop.
func (ln *loopnest) findExits() {
	if ln.initializedExits {
		return
	}
	ln.calculateDepths()
	b2l := ln.b2l
	for _, b := range ln.po {
		l := b2l[b.ID] // 获取块对应的loop结构体
		if l != nil && len(b.Succs) == 2 {
			sl := b2l[b.Succs[0].b.ID] // 后继块也是一个循环
			if recordIfExit(l, sl, b.Succs[0].b) {
				continue
			}
			sl = b2l[b.Succs[1].b.ID]
			if recordIfExit(l, sl, b.Succs[1].b) {
				continue
			}
		}
	}
	ln.initializedExits = true
}

// depth returns the loop nesting level of block b.
func (ln *loopnest) depth(b ID) int16 {
	if l := ln.b2l[b]; l != nil {
		return l.depth
	}
	return 0
}

// recordIfExit checks sl (the loop containing b) to see if it
// is outside of loop l, and if so, records b as an exit block
// from l and returns true.
func recordIfExit(l, sl *loop, b *Block) bool { // l是外层循环,sl是内层循环,b是对应sl的block
	if sl != l { // s1与l不是一个循环
		if sl == nil || sl.depth <= l.depth { // sl是循环l的外部代码块或者sl是l的外层循环
			l.exits = append(l.exits, b) // 说明b块是一个循环的退出块
			return true
		}
		// sl is not nil, and is deeper than l
		// it's possible for this to be a goto into an irreducible loop made from gotos.
		for sl.depth > l.depth { // goto
			sl = sl.outer
		}
		if sl != l {
			l.exits = append(l.exits, b)
			return true
		}
	}
	return false
}

func (l *loop) setDepth(d int16) {
	l.depth = d
	for _, c := range l.children {
		c.setDepth(d + 1)
	}
}

// iterationEnd checks if block b ends iteration of loop l.
// Ending iteration means either escaping to outer loop/code or
// going back to header
func (l *loop) iterationEnd(b *Block, b2l []*loop) bool {
	// b就是l记载的循环头的后继块,相当于已经结束了一次循环
	// 块b不在循环中,说明跳到了外部的代码
	// b属于l外部的一个循环
	return b == l.header || b2l[b.ID] == nil || (b2l[b.ID] != l && b2l[b.ID].depth <= l.depth)
}

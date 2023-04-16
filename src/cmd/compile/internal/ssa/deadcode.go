// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/internal/src"
)

// findlive returns the reachable blocks and live values in f.
// The caller should call f.retDeadcodeLive(live) when it is done with it.
func findlive(f *Func) (reachable []bool, live []bool) {
	reachable = ReachableBlocks(f)
	var order []*Value
	live, order = liveValues(f, reachable)
	f.retDeadcodeLiveOrderStmts(order)
	return
}
// 根据函数起始不断寻找后继块,遍历到的块的ID会作为返回数组中的索引,值为true
// ReachableBlocks returns the reachable blocks in f.
func ReachableBlocks(f *Func) []bool {
	reachable := make([]bool, f.NumBlocks())
	reachable[f.Entry.ID] = true
	p := make([]*Block, 0, 64) // stack-like worklist
	p = append(p, f.Entry)
	for len(p) > 0 {
		// Pop a reachable block
		b := p[len(p)-1]
		p = p[:len(p)-1]
		// Mark successors as reachable
		s := b.Succs	// 获取后继块
		if b.Kind == BlockFirst {
			s = s[:1]
		}
		for _, e := range s {	// 遍历后继块
			c := e.b
			if int(c.ID) >= len(reachable) {
				f.Fatalf("block %s >= f.NumBlocks()=%d?", c, len(reachable))
			}
			if !reachable[c.ID] {
				reachable[c.ID] = true
				p = append(p, c) // push		继续遍历可达块
			}
		}
	}
	return reachable
}

// liveValues returns the live values in f and a list of values that are eligible
// to be statements in reversed data flow order.
// The second result is used to help conserve statement boundaries for debugging.
// reachable is a map from block ID to whether the block is reachable.
// The caller should call f.retDeadcodeLive(live) and f.retDeadcodeLiveOrderStmts(liveOrderStmts)
// when they are done with the return values.
func liveValues(f *Func, reachable []bool) (live []bool, liveOrderStmts []*Value) {
	live = f.newDeadcodeLive()	// 记录Value是否存活
	if cap(live) < f.NumValues() {
		live = make([]bool, f.NumValues())
	} else {
		live = live[:f.NumValues()]
		for i := range live {
			live[i] = false
		}
	}

	liveOrderStmts = f.newDeadcodeLiveOrderStmts()	// values need special treatment for statement boundaries
	liveOrderStmts = liveOrderStmts[:0]

	// After regalloc, consider all values to be live.
	// See the comment at the top of regalloc.go and in deadcode for details.
	if f.RegAlloc != nil {
		for i := range live {
			live[i] = true
		}
		return
	}

	// Record all the inline indexes we need
	var liveInlIdx map[int]bool
	pt := f.Config.ctxt.PosTable
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			i := pt.Pos(v.Pos).Base().InliningIndex()	// 获取内联树中的索引号
			if i < 0 {
				continue
			}
			if liveInlIdx == nil {
				liveInlIdx = map[int]bool{}
			}
			liveInlIdx[i] = true
		}
		i := pt.Pos(b.Pos).Base().InliningIndex()
		if i < 0 {
			continue
		}
		if liveInlIdx == nil {
			liveInlIdx = map[int]bool{}
		}
		liveInlIdx[i] = true
	}

	// Find all live values
	q := f.Cache.deadcode.q[:0]
	defer func() { f.Cache.deadcode.q = q }()

	// Starting set: all control values of reachable blocks are live.
	// Calls are live (because callee can observe the memory state).
	for _, b := range f.Blocks {
		if !reachable[b.ID] {	// 只处理可抵达的块
			continue
		}
		for _, v := range b.ControlValues() {	// 遍历用于跳转的语句
			if !live[v.ID] {	// 控制语句必然存活
				live[v.ID] = true
				q = append(q, v)	// 添加到存活列表中
				if v.Pos.IsStmt() != src.PosNotStmt {	// 是statement语句
					liveOrderStmts = append(liveOrderStmts, v)
				}
			}
		}
		for _, v := range b.Values {	// 遍历块中的所有Value
			if (opcodeTable[v.Op].call || opcodeTable[v.Op].hasSideEffects) && !live[v.ID] {
				live[v.ID] = true
				q = append(q, v)
				if v.Pos.IsStmt() != src.PosNotStmt {
					liveOrderStmts = append(liveOrderStmts, v)
				}
			}
			if v.Type.IsVoid() && !live[v.ID] {
				// The only Void ops are nil checks and inline marks.  We must keep these.
				if v.Op == OpInlMark && !liveInlIdx[int(v.AuxInt)] {
					// We don't need marks for bodies that
					// have been completely optimized away.
					// TODO: save marks only for bodies which
					// have a faulting instruction or a call?
					continue
				}
				live[v.ID] = true
				q = append(q, v)
				if v.Pos.IsStmt() != src.PosNotStmt {
					liveOrderStmts = append(liveOrderStmts, v)
				}
			}
		}
	}

	// Compute transitive closure of live values.
	for len(q) > 0 {
		// pop a reachable value
		v := q[len(q)-1]
		q = q[:len(q)-1]
		for i, x := range v.Args {
			if v.Op == OpPhi && !reachable[v.Block.Preds[i].b.ID] {	// 对于一个phi函数来说,它的参数对应的前驱块不可达
				continue
			}
			if !live[x.ID] {
				live[x.ID] = true
				q = append(q, x) // push
				if x.Pos.IsStmt() != src.PosNotStmt {
					liveOrderStmts = append(liveOrderStmts, x)
				}
			}
		}
	}

	return
}

// deadcode removes dead code from f.
func deadcode(f *Func) {
	// deadcode after regalloc is forbidden for now. Regalloc
	// doesn't quite generate legal SSA which will lead to some
	// required moves being eliminated. See the comment at the
	// top of regalloc.go for details.
	if f.RegAlloc != nil {
		f.Fatalf("deadcode after regalloc")
	}

	// Find reachable blocks.
	reachable := ReachableBlocks(f)

	// Get rid of edges from dead to live code.
	for _, b := range f.Blocks {
		if reachable[b.ID] {	// 该块可以抵达就跳过
			continue
		}
		for i := 0; i < len(b.Succs); {	// 遍历死代码块的后继块并删除到可达后继块的边
			e := b.Succs[i]
			if reachable[e.b.ID] {	// 后继块可达
				b.removeEdge(i)	// 删除死代码块到可达边的路径
			} else {	// 后继块不可达的话就看下一个后继块是否可达
				i++
			}
		}
	}

	// Get rid of dead edges from live code.
	for _, b := range f.Blocks {
		if !reachable[b.ID] {	// 不可抵达的块就跳过
			continue
		}
		if b.Kind != BlockFirst {
			continue
		}
		// 将第二条边删掉
		b.removeEdge(1)
		b.Kind = BlockPlain
		b.Likely = BranchUnknown
	}

	// Splice out any copies introduced during dead block removal.
	copyelim(f)

	// Find live values.
	live, order := liveValues(f, reachable)	// order是存活且代表statement的Value		live中为内联函数对应的内联树中的索引号,可抵达块中的控制语句,函数调用或者有副作用的value ID
	defer f.retDeadcodeLive(live)
	defer f.retDeadcodeLiveOrderStmts(order)

	// Remove dead & duplicate entries from namedValues map.
	s := f.newSparseSet(f.NumValues())
	defer f.retSparseSet(s)
	i := 0
	for _, name := range f.Names {
		j := 0
		s.clear()
		values := f.NamedValues[name]
		for _, v := range values {
			if live[v.ID] && !s.contains(v.ID) {
				values[j] = v
				j++
				s.add(v.ID)
			}
		}
		if j == 0 {
			delete(f.NamedValues, name)
		} else {
			f.Names[i] = name
			i++
			for k := len(values) - 1; k >= j; k-- {
				values[k] = nil
			}
			f.NamedValues[name] = values[:j]
		}
	}
	clearNames := f.Names[i:]
	for j := range clearNames {
		clearNames[j] = LocalSlot{}
	}
	f.Names = f.Names[:i]

	pendingLines := f.cachedLineStarts // Holds statement boundaries that need to be moved to a new value/block
	pendingLines.clear()

	// Unlink values and conserve statement boundaries
	for i, b := range f.Blocks {
		if !reachable[b.ID] {
			// TODO what if control is statement boundary? Too late here.
			b.ResetControls()
		}
		for _, v := range b.Values {
			if !live[v.ID] {
				v.resetArgs()	// 清除该value,将所有的Arg的Use减一
				if v.Pos.IsStmt() == src.PosIsStmt && reachable[b.ID] {	// value是一个statement且value所在的块可达
					pendingLines.set(v.Pos, int32(i)) // TODO could be more than one pos for a line
				}
			}
		}
	}

	// Find new homes for lost lines -- require earliest in data flow with same line that is also in same block
	for i := len(order) - 1; i >= 0; i-- {
		w := order[i]	// 获取存活且为statement边界的value
		if j := pendingLines.get(w.Pos); j > -1 && f.Blocks[j] == w.Block {
			w.Pos = w.Pos.WithIsStmt()
			pendingLines.remove(w.Pos)
		}
	}

	// Any boundary that failed to match a live value can move to a block end
	pendingLines.foreachEntry(func(j int32, l uint, bi int32) {
		b := f.Blocks[bi]	// 根据块编号获取块结构体
		if b.Pos.Line() == l && b.Pos.FileIndex() == j {	// 块的行号与文件index与之前记录的相同
			b.Pos = b.Pos.WithIsStmt()
		}
	})

	// Remove dead values from blocks' value list. Return dead
	// values to the allocator.
	for _, b := range f.Blocks {
		i := 0
		for _, v := range b.Values {
			if live[v.ID] {	// 活跃的Value
				b.Values[i] = v	// 这一步操作将活跃的value向前移
				i++
			} else {
				f.freeValue(v)
			}
		}
		b.truncateValues(i)
	}

	// Remove dead blocks from WBLoads list.
	i = 0
	for _, b := range f.WBLoads {
		if reachable[b.ID] {
			f.WBLoads[i] = b
			i++
		}
	}
	clearWBLoads := f.WBLoads[i:]
	for j := range clearWBLoads {
		clearWBLoads[j] = nil
	}
	f.WBLoads = f.WBLoads[:i]

	// Remove unreachable blocks. Return dead blocks to allocator.
	i = 0
	for _, b := range f.Blocks {
		if reachable[b.ID] {
			f.Blocks[i] = b
			i++
		} else {
			if len(b.Values) > 0 {
				b.Fatalf("live values in unreachable block %v: %v", b, b.Values)
			}
			f.freeBlock(b)
		}
	}
	// zero remainder to help GC
	tail := f.Blocks[i:]
	for j := range tail {
		tail[j] = nil
	}
	f.Blocks = f.Blocks[:i]
}

// removeEdge removes the i'th outgoing edge from b (and
// the corresponding incoming edge from b.Succs[i].b).
func (b *Block) removeEdge(i int) {
	e := b.Succs[i]	// 第i条后继边
	c := e.b	// 获取后继块
	j := e.i	// b是c的第j个前驱

	// Adjust b.Succs
	b.removeSucc(i)

	// Adjust c.Preds
	c.removePred(j)

	// Remove phi args from c's phis.	b块到c块的边被删除了
	n := len(c.Preds)
	for _, v := range c.Values {
		if v.Op != OpPhi {
			continue
		}
		v.Args[j].Uses--
		v.Args[j] = v.Args[n]
		v.Args[n] = nil
		v.Args = v.Args[:n]
		phielimValue(v)
		// Note: this is trickier than it looks. Replacing
		// a Phi with a Copy can in general cause problems because
		// Phi and Copy don't have exactly the same semantics.
		// Phi arguments always come from a predecessor block,
		// whereas copies don't. This matters in loops like:
		// 1: x = (Phi y)
		//    y = (Add x 1)
		//    goto 1
		// If we replace Phi->Copy, we get
		// 1: x = (Copy y)
		//    y = (Add x 1)
		//    goto 1
		// (Phi y) refers to the *previous* value of y, whereas
		// (Copy y) refers to the *current* value of y.
		// The modified code has a cycle and the scheduler
		// will barf on it.
		//
		// Fortunately, this situation can only happen for dead
		// code loops. We know the code we're working with is
		// not dead, so we're ok.
		// Proof: If we have a potential bad cycle, we have a
		// situation like this:
		//   x = (Phi z)
		//   y = (op1 x ...)
		//   z = (op2 y ...)
		// Where opX are not Phi ops. But such a situation
		// implies a cycle in the dominator graph. In the
		// example, x.Block dominates y.Block, y.Block dominates
		// z.Block, and z.Block dominates x.Block (treating
		// "dominates" as reflexive).  Cycles in the dominator
		// graph can only happen in an unreachable cycle.
	}
}

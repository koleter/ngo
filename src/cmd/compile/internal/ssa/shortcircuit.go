// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// Shortcircuit finds situations where branch directions
// are always correlated and rewrites the CFG to take
// advantage of that fact.
// This optimization is useful for compiling && and || expressions.
func shortcircuit(f *Func) {
	// Step 1: Replace a phi arg with a constant if that arg
	// is the control value of a preceding If block.
	// b1:
	//    If a goto b2 else b3
	// b2: <- b1 ...
	//    x = phi(a, ...)
	//
	// We can replace the "a" in the phi with the constant true.
	var ct, cf *Value
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if v.Op != OpPhi {	// 定位到phi
				continue
			}
			if !v.Type.IsBoolean() {	// phi中是一个布尔值
				continue
			}
			for i, a := range v.Args {
				e := b.Preds[i]
				p := e.b	// 获取对应参数a的前驱块
				if p.Kind != BlockIf {	// 前驱块是if块
					continue
				}
				if p.Controls[0] != a {	// 前驱块的第一个控制流需要是a
					continue
				}
				if e.i == 0 {	// 块b是块p的第一个后继, 表示为true时会从块p到块b
					if ct == nil {
						ct = f.ConstBool(f.Config.Types.Bool, true)
					}
					v.SetArg(i, ct)	// 将phi替换为布尔常量
				} else {
					if cf == nil {
						cf = f.ConstBool(f.Config.Types.Bool, false)
					}
					v.SetArg(i, cf)
				}
			}
		}
	}

	// Step 2: Redirect control flow around known branches.
	// p:
	//   ... goto b ...
	// b: <- p ...
	//   v = phi(true, ...)
	//   if v goto t else u
	// We can redirect p to go directly to t instead of b.
	// (If v is not live after b).
	fuse(f, fuseTypePlain|fuseTypeShortCircuit)
}

// shortcircuitBlock checks for a CFG in which an If block
// has as its control value a Phi that has a ConstBool arg.
// In some such cases, we can rewrite the CFG into a flatter form.
//
// (1) Look for a CFG of the form
//
//   p   other pred(s)
//    \ /
//     b
//    / \
//   t   other succ
//
// in which b is an If block containing a single phi value with a single use (b's Control),
// which has a ConstBool arg.
// p is the predecessor corresponding to the argument slot in which the ConstBool is found.
// t is the successor corresponding to the value of the ConstBool arg.
//
// Rewrite this into
//
//   p   other pred(s)
//   |  /
//   | b
//   |/ \
//   t   u
//
// and remove the appropriate phi arg(s).
//
// (2) Look for a CFG of the form
//
//   p   q
//    \ /
//     b
//    / \
//   t   u
//
// in which b is as described in (1).
// However, b may also contain other phi values.
// The CFG will be modified as described in (1).
// However, in order to handle those other phi values,
// for each other phi value w, we must be able to eliminate w from b.
// We can do that though a combination of moving w to a different block
// and rewriting uses of w to use a different value instead.
// See shortcircuitPhiPlan for details.
func shortcircuitBlock(b *Block) bool {
	if b.Kind != BlockIf {
		return false
	}
	// Look for control values of the form Copy(Not(Copy(Phi(const, ...)))).
	// Those must be the only values in the b, and they each must be used only by b.
	// Track the negations so that we can swap successors as needed later.
	ctl := b.Controls[0]
	nval := 1 // the control value
	var swap int64
	for ctl.Uses == 1 && ctl.Block == b && (ctl.Op == OpCopy || ctl.Op == OpNot) {	// 不断解除外部的OpCopy与OpNot
		if ctl.Op == OpNot {
			swap = 1 ^ swap
		}
		ctl = ctl.Args[0]
		nval++ // wrapper around control value
	}
	if ctl.Op != OpPhi || ctl.Block != b || ctl.Uses != 1 {
		return false
	}
	nOtherPhi := 0	// 记录在b块中与ctl不同的phi的数量
	for _, w := range b.Values {
		if w.Op == OpPhi && w != ctl {
			nOtherPhi++
		}
	}
	if nOtherPhi > 0 && len(b.Preds) != 2 {
		// We rely on b having exactly two preds in shortcircuitPhiPlan
		// to reason about the values of phis.
		return false
	}
	if len(b.Values) != nval+nOtherPhi {
		return false
	}

	// Locate index of first const phi arg.
	cidx := -1
	for i, a := range ctl.Args {
		if a.Op == OpConstBool {
			cidx = i
			break
		}
	}
	if cidx == -1 {	// 无布尔常量返回false
		return false
	}

	// p is the predecessor corresponding to cidx.
	pe := b.Preds[cidx]
	p := pe.b	// 常量对应的前驱块
	pi := pe.i

	// t is the "taken" branch: the successor we always go to when coming in from p.
	ti := 1 ^ ctl.Args[cidx].AuxInt ^ swap	// 确定跳转true分支还是false分支,值为0或1
	te := b.Succs[ti]	// 跳转的分支
	t := te.b	// 跳转该分支进入的块
	if p == b || t == b {	// 按理说应该是p->b->t,但如果是循环的话就未必是这个层级关系了
		// This is an infinite loop; we can't remove it. See issue 33903.
		return false
	}

	var fixPhi func(*Value, int)
	if nOtherPhi > 0 {
		fixPhi = shortcircuitPhiPlan(b, ctl, cidx, ti)
		if fixPhi == nil {
			return false
		}
	}

	// We're committed. Update CFG and Phis.
	// If you modify this section, update shortcircuitPhiPlan corresponding.

	// Remove b's incoming edge from p.
	b.removePred(cidx)
	n := len(b.Preds)	// 移除p->b的边后b的前驱数量
	ctl.Args[cidx].Uses--
	ctl.Args[cidx] = ctl.Args[n]	// 最后一个参数替换掉指定参数
	ctl.Args[n] = nil
	ctl.Args = ctl.Args[:n]

	// Redirect p's outgoing edge to t.
	p.Succs[pi] = Edge{t, len(t.Preds)}

	// Fix up t to have one more predecessor.
	t.Preds = append(t.Preds, Edge{p, pi})	// t添加p为前驱
	for _, v := range t.Values {	// 为t的phi函数添加一个参数
		if v.Op != OpPhi {
			continue
		}
		v.AddArg(v.Args[te.i])
	}

	if nOtherPhi != 0 {
		// Adjust all other phis as necessary.
		// Use a plain for loop instead of range because fixPhi may move phis,
		// thus modifying b.Values.
		for i := 0; i < len(b.Values); i++ {
			phi := b.Values[i]
			if phi.Uses == 0 || phi == ctl || phi.Op != OpPhi {
				continue
			}
			fixPhi(phi, i)
			if phi.Block == b {	// 这个phi还是属于b块,没有移动到其他的块中
				continue
			}
			// phi got moved to a different block with v.moveTo.
			// Adjust phi values in this new block that refer
			// to phi to refer to the corresponding phi arg instead.
			// phi used to be evaluated prior to this block,
			// and now it is evaluated in this block.
			for _, v := range phi.Block.Values {
				if v.Op != OpPhi || v == phi {
					continue
				}
				for j, a := range v.Args {
					if a == phi {	// 找到某个value中参数为这个被移动的phi的参数
						v.SetArg(j, phi.Args[j])	// 将布尔参数直接替换掉原来的参数
					}
				}
			}
			if phi.Uses != 0 {
				phielimValue(phi)
			} else {
				phi.reset(OpInvalid)
			}
			i-- // v.moveTo put a new value at index i; reprocess
		}

		// We may have left behind some phi values with no uses
		// but the wrong number of arguments. Eliminate those.
		for _, v := range b.Values {
			if v.Uses == 0 {
				v.reset(OpInvalid)
			}
		}
	}

	if len(b.Preds) == 0 {
		// Block is now dead.
		b.Kind = BlockInvalid
	}

	phielimValue(ctl)
	return true
}

// shortcircuitPhiPlan returns a function to handle non-ctl phi values in b,
// where b is as described in shortcircuitBlock.
// The returned function accepts a value v
// and the index i of v in v.Block: v.Block.Values[i] == v.
// If the returned function moves v to a different block, it will use v.moveTo.
// cidx is the index in ctl of the ConstBool arg.
// ti is the index in b.Succs of the always taken branch when arriving from p.
// If shortcircuitPhiPlan returns nil, there is no plan available,
// and the CFG modifications must not proceed.
// The returned function assumes that shortcircuitBlock has completed its CFG modifications.
func shortcircuitPhiPlan(b *Block, ctl *Value, cidx int, ti int64) func(*Value, int) {
	const go115shortcircuitPhis = true
	if !go115shortcircuitPhis {
		return nil
	}

	// t is the "taken" branch: the successor we always go to when coming in from p.
	t := b.Succs[ti].b
	// u is the "untaken" branch: the successor we never go to when coming in from p.
	u := b.Succs[1^ti].b

	// Look for some common CFG structures
	// in which the outbound paths from b merge,
	// with no other preds joining them.
	// In these cases, we can reconstruct what the value
	// of any phi in b must be in the successor blocks.

	if len(t.Preds) == 1 && len(t.Succs) == 1 &&
		len(u.Preds) == 1 && len(u.Succs) == 1 &&
		t.Succs[0].b == u.Succs[0].b && len(t.Succs[0].b.Preds) == 2 {
		// p   q
		//  \ /
		//   b
		//  / \
		// t   u
		//  \ /
		//   m
		//
		// After the CFG modifications, this will look like
		//
		// p   q
		// |  /
		// | b
		// |/ \
		// t   u
		//  \ /
		//   m
		//
		// NB: t.Preds is (b, p), not (p, b).
		m := t.Succs[0].b
		return func(v *Value, i int) {
			// Replace any uses of v in t and u with the value v must have,
			// given that we have arrived at that block.
			// Then move v to m and adjust its value accordingly;
			// this handles all other uses of v.
			argP, argQ := v.Args[cidx], v.Args[1^cidx]	// 获取phi函数的两个参数
			u.replaceUses(v, argQ)	// u中出现的phi函数通过变量argQ替换掉
			phi := t.Func.newValue(OpPhi, v.Type, t, v.Pos)
			phi.AddArg2(argQ, argP)	// t.Preds is (b, p)
			t.replaceUses(v, phi)	// 替换从b过来的phi函数
			if v.Uses == 0 {
				return
			}
			v.moveTo(m, i)	// b的前驱只有一个了,所以phi应该移动到m
			// The phi in m belongs to whichever pred idx corresponds to t.
			if m.Preds[0].b == t {
				v.SetArgs2(phi, argQ)
			} else {
				v.SetArgs2(argQ, phi)
			}
		}
	}

	if len(t.Preds) == 2 && len(u.Preds) == 1 && len(u.Succs) == 1 && u.Succs[0].b == t {
		// p   q
		//  \ /
		//   b
		//   |\
		//   | u
		//   |/
		//   t
		//
		// After the CFG modifications, this will look like
		//
		//     q
		//    /
		//   b
		//   |\
		// p | u
		//  \|/
		//   t
		//
		// NB: t.Preds is (b or u, b or u, p).
		return func(v *Value, i int) {	// 这里为什么没有调整边?
			// Replace any uses of v in u. Then move v to t.
			argP, argQ := v.Args[cidx], v.Args[1^cidx]
			u.replaceUses(v, argQ)	// 将v中的phi替换为argQ
			v.moveTo(t, i)
			v.SetArgs3(argQ, argQ, argP)
		}
	}

	if len(u.Preds) == 2 && len(t.Preds) == 1 && len(t.Succs) == 1 && t.Succs[0].b == u {
		// p   q
		//  \ /
		//   b
		//  /|
		// t |
		//  \|
		//   u
		//
		// After the CFG modifications, this will look like
		//
		// p   q
		// |  /
		// | b
		// |/|
		// t |
		//  \|
		//   u
		//
		// NB: t.Preds is (b, p), not (p, b).
		return func(v *Value, i int) {
			// Replace any uses of v in t. Then move v to u.
			argP, argQ := v.Args[cidx], v.Args[1^cidx]
			phi := t.Func.newValue(OpPhi, v.Type, t, v.Pos)
			phi.AddArg2(argQ, argP)	// t.Preds is (b, p)
			t.replaceUses(v, phi)
			if v.Uses == 0 {
				return
			}
			v.moveTo(u, i)
			v.SetArgs2(argQ, phi)
		}
	}

	// Look for some common CFG structures
	// in which one outbound path from b exits,
	// with no other preds joining.
	// In these cases, we can reconstruct what the value
	// of any phi in b must be in the path leading to exit,
	// and move the phi to the non-exit path.

	if len(t.Preds) == 1 && len(u.Preds) == 1 && len(t.Succs) == 0 {
		// p   q
		//  \ /
		//   b
		//  / \
		// t   u
		//
		// where t is an Exit/Ret block.
		//
		// After the CFG modifications, this will look like
		//
		// p   q
		// |  /
		// | b
		// |/ \
		// t   u
		//
		// NB: t.Preds is (b, p), not (p, b).
		return func(v *Value, i int) {
			// Replace any uses of v in t and x. Then move v to u.
			argP, argQ := v.Args[cidx], v.Args[1^cidx]
			// If there are no uses of v in t or x, this phi will be unused.
			// That's OK; it's not worth the cost to prevent that.
			phi := t.Func.newValue(OpPhi, v.Type, t, v.Pos)
			phi.AddArg2(argQ, argP)	// t.Preds is (b, p)
			t.replaceUses(v, phi)
			if v.Uses == 0 {
				return
			}
			v.moveTo(u, i)
			v.SetArgs1(argQ)
		}
	}

	if len(u.Preds) == 1 && len(t.Preds) == 1 && len(u.Succs) == 0 {
		// p   q
		//  \ /
		//   b
		//  / \
		// t   u
		//
		// where u is an Exit/Ret block.
		//
		// After the CFG modifications, this will look like
		//
		// p   q
		// |  /
		// | b
		// |/ \
		// t   u
		//
		// NB: t.Preds is (b, p), not (p, b).
		return func(v *Value, i int) {
			// Replace any uses of v in u (and x). Then move v to t.
			argP, argQ := v.Args[cidx], v.Args[1^cidx]
			u.replaceUses(v, argQ)
			v.moveTo(t, i)
			v.SetArgs2(argQ, argP)	// t.Preds is (b, p)
		}
	}

	// TODO: handle more cases; shortcircuit optimizations turn out to be reasonably high impact
	return nil
}

// replaceUses replaces all uses of old in b with new.
func (b *Block) replaceUses(old, new *Value) {
	for _, v := range b.Values {	// 先将一个块中所有value的参数替换
		for i, a := range v.Args {
			if a == old {
				v.SetArg(i, new)
			}
		}
	}
	for i, v := range b.ControlValues() {	// 找到控制value并进行替换
		if v == old {
			b.ReplaceControl(i, new)
		}
	}
}

// moveTo moves v to dst, adjusting the appropriate Block.Values slices.
// The caller is responsible for ensuring that this is safe.
// i is the index of v in v.Block.Values.
func (v *Value) moveTo(dst *Block, i int) {
	if dst.Func.scheduled {
		v.Fatalf("moveTo after scheduling")
	}
	src := v.Block
	if src.Values[i] != v {
		v.Fatalf("moveTo bad index %d", v, i)
	}
	if src == dst {
		return
	}
	v.Block = dst	// value的block设置为dst
	dst.Values = append(dst.Values, v)
	last := len(src.Values) - 1
	src.Values[i] = src.Values[last]
	src.Values[last] = nil
	src.Values = src.Values[:last]
}

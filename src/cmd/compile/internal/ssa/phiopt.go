// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// phiopt eliminates boolean Phis based on the previous if.
//
// Main use case is to transform:
//   x := false
//   if b {
//     x = true
//   }
// into x = b.
//
// In SSA code this appears as
//
// b0
//   If b -> b1 b2
// b1
//   Plain -> b2
// b2
//   x = (OpPhi (ConstBool [true]) (ConstBool [false]))
//
// In this case we can replace x with a copy of b.
func phiopt(f *Func) {
	sdom := f.Sdom()
	for _, b := range f.Blocks {
		if len(b.Preds) != 2 || len(b.Values) == 0 {	// 这里希望找到上方注释中的b2
			// TODO: handle more than 2 predecessors, e.g. a || b || c.
			continue
		}
		// b0相当于上方注释中的b0
		pb0, b0 := b, b.Preds[0].b
		for len(b0.Succs) == 1 && len(b0.Preds) == 1 {	// b0是一个基本块,说明这里找到的b0应该是b1,这个循环用于找到非基本块
			pb0, b0 = b0, b0.Preds[0].b	// 确保b0为上方注释中的b0
		}
		if b0.Kind != BlockIf {
			continue
		}
		pb1, b1 := b, b.Preds[1].b
		for len(b1.Succs) == 1 && len(b1.Preds) == 1 {	// b1是一个基本块
			pb1, b1 = b1, b1.Preds[0].b	// 确保b1为上方注释中的b0
		}
		if b1 != b0 {
			continue
		}
		// b0 is the if block giving the boolean value.
		// pb0与pb1分别为b0的两个后继
		// reverse is the predecessor from which the truth value comes.
		var reverse int	// b.Preds[reverse]就是b0.Succs[0]
		if b0.Succs[0].b == pb0 && b0.Succs[1].b == pb1 {	// b0判断为true时进入pb0块,而pb0是b块的第一个前驱
			reverse = 0
		} else if b0.Succs[0].b == pb1 && b0.Succs[1].b == pb0 {
			reverse = 1
		} else {
			b.Fatalf("invalid predecessors\n")
		}

		for _, v := range b.Values {
			if v.Op != OpPhi {
				continue
			}

			// Look for conversions from bool to 0/1.
			if v.Type.IsInteger() {
				phioptint(v, b0, reverse)
			}

			if !v.Type.IsBoolean() {
				continue
			}
			// 到这里找到了布尔类型的phi函数
			// Replaces
			//   if a { x = true } else { x = false } with x = a
			// and
			//   if a { x = false } else { x = true } with x = !a
			if v.Args[0].Op == OpConstBool && v.Args[1].Op == OpConstBool {	// phi函数中都是布尔常量
				if v.Args[reverse].AuxInt != v.Args[1-reverse].AuxInt {	// phi函数中的布尔常量参数的值不同
					ops := [2]Op{OpNot, OpCopy}
					// b.Preds[reverse]就是b0.Succs[0],这里v.Args[reverse].AuxInt是获取了if块判断为true时的分支中为x赋的值
					v.reset(ops[v.Args[reverse].AuxInt])
					v.AddArg(b0.Controls[0])
					if f.pass.debug > 0 {
						f.Warnl(b.Pos, "converted OpPhi to %v", v.Op)
					}
					continue
				}
			}

			// Replaces
			//   if a { x = true } else { x = value } with x = a || value.
			// Requires that value dominates x, meaning that regardless of a,
			// value is always computed. This guarantees that the side effects
			// of value are not seen if a is false.
			if v.Args[reverse].Op == OpConstBool && v.Args[reverse].AuxInt == 1 {	// b0的true分支中定义x = true
				// 定义value的块支配phi函数所在块
				if tmp := v.Args[1-reverse]; sdom.IsAncestorEq(tmp.Block, b) {
					v.reset(OpOrB)
					v.SetArgs2(b0.Controls[0], tmp)	// x = a || value
					if f.pass.debug > 0 {
						f.Warnl(b.Pos, "converted OpPhi to %v", v.Op)
					}
					continue
				}
			}

			// Replaces
			//   if a { x = value } else { x = false } with x = a && value.
			// Requires that value dominates x, meaning that regardless of a,
			// value is always computed. This guarantees that the side effects
			// of value are not seen if a is false.
			if v.Args[1-reverse].Op == OpConstBool && v.Args[1-reverse].AuxInt == 0 {
				if tmp := v.Args[reverse]; sdom.IsAncestorEq(tmp.Block, b) {	// value dominates x
					v.reset(OpAndB)
					v.SetArgs2(b0.Controls[0], tmp)	// x = a && value
					if f.pass.debug > 0 {
						f.Warnl(b.Pos, "converted OpPhi to %v", v.Op)
					}
					continue
				}
			}
		}
	}
}
/*
v: 一个类型为整型的phi函数
b0: v.block的上一个if块
reverse: 表示v.block块中phi函数的true值是从第几个前驱边进入的
*/
func phioptint(v *Value, b0 *Block, reverse int) {
	a0 := v.Args[0]	// 第一个前驱边传入的参数
	a1 := v.Args[1] // 第二个前驱边传入的参数
	if a0.Op != a1.Op {
		return
	}

	switch a0.Op {
	case OpConst8, OpConst16, OpConst32, OpConst64:
	default:
		return
	}

	negate := false
	switch {
	case a0.AuxInt == 0 && a1.AuxInt == 1:	// 第一个前驱边传入false,第二个前驱边传入true
		negate = true
	case a0.AuxInt == 1 && a1.AuxInt == 0:
	default:
		return
	}

	if reverse == 1 {	// 第二个前驱边传入true
		negate = !negate	// 总之就是想要第一个前驱边传入true
	}

	a := b0.Controls[0]	// b0的控制value
	if negate {
		a = v.Block.NewValue1(v.Pos, OpNot, a.Type, a)	// 相当于在if判断上为结果取反了
	}
	v.AddArg(a)

	cvt := v.Block.NewValue1(v.Pos, OpCvtBoolToUint8, v.Block.Func.Config.Types.UInt8, a)	// 将a从布尔转为uint8类型

	switch v.Type.Size() {
	case 1:
		v.reset(OpCopy)
	case 2:
		v.reset(OpZeroExt8to16)
	case 4:
		v.reset(OpZeroExt8to32)
	case 8:
		v.reset(OpZeroExt8to64)
	default:
		v.Fatalf("bad int size %d", v.Type.Size())
	}
	v.AddArg(cvt)	// 布尔转int类型的Op作为v的参数

	f := b0.Func
	if f.pass.debug > 0 {
		f.Warnl(v.Block.Pos, "converted OpPhi bool -> int%d", v.Type.Size()*8)
	}
}

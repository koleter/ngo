// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"fmt"
	"math"
)

type indVarFlags uint8

const (
	indVarMinExc indVarFlags = 1 << iota // minimum value is exclusive (default: inclusive)
	indVarMaxInc                         // maximum value is inclusive (default: exclusive)
)

type indVar struct {
	ind   *Value // induction variable
	min   *Value // minimum value, inclusive/exclusive depends on flags
	max   *Value // maximum value, inclusive/exclusive depends on flags
	entry *Block // entry block in the loop.
	flags indVarFlags
	// Invariant: for all blocks strictly dominated by entry:
	//	min <= ind <  max    [if flags == 0]
	//	min <  ind <  max    [if flags == indVarMinExc]
	//	min <= ind <= max    [if flags == indVarMaxInc]
	//	min <  ind <= max    [if flags == indVarMinExc|indVarMaxInc]
}

// parseIndVar checks whether the SSA value passed as argument is a valid induction
// variable, and, if so, extracts:
//   * the minimum bound
//   * the increment value
//   * the "next" value (SSA value that is Phi'd into the induction variable every loop)
// Currently, we detect induction variables that match (Phi min nxt),
// with nxt being (Add inc ind).
// If it can't parse the induction variable correctly, it returns (nil, nil, nil).
func parseIndVar(ind *Value) (min, inc, nxt *Value) {
	if ind.Op != OpPhi {
		return
	}

	if n := ind.Args[0]; n.Op == OpAdd64 && (n.Args[0] == ind || n.Args[1] == ind) {	// 判断iter语句,类似于i++这样的,phi函数的Args[0]是iter语句,那么Args[1]必定是初始化时的最小值
		min, nxt = ind.Args[1], n
	} else if n := ind.Args[1]; n.Op == OpAdd64 && (n.Args[0] == ind || n.Args[1] == ind) {
		min, nxt = ind.Args[0], n
	} else {
		// Not a recognized induction variable.
		return
	}

	if nxt.Args[0] == ind { // nxt = ind + inc
		inc = nxt.Args[1]
	} else if nxt.Args[1] == ind { // nxt = inc + ind
		inc = nxt.Args[0]
	} else {
		panic("unreachable") // one of the cases must be true from the above.
	}

	return
}

// findIndVar finds induction variables in a function.
//
// Look for variables and blocks that satisfy the following
//
// loop:
//   ind = (Phi min nxt),
//   if ind < max
//     then goto enter_loop
//     else goto exit_loop
//
//   enter_loop:
//	do something
//      nxt = inc + ind
//	goto loop
//
// exit_loop:
//
//
// TODO: handle 32 bit operations
func findIndVar(f *Func) []indVar {
	var iv []indVar
	sdom := f.Sdom()

	for _, b := range f.Blocks {
		if b.Kind != BlockIf || len(b.Preds) != 2 {
			continue
		}
		// 找到一个拥有两个前驱的if块,这里可能是希望找到循环中的判断,但是不在循环中的判断也有符合情况的,区分这种情况就在于,if块的判断语句中是一个phi函数
		var flags indVarFlags
		var ind, max *Value // induction, and maximum

		// Check thet the control if it either ind </<= max or max >/>= ind.
		// TODO: Handle 32-bit comparisons.
		// TODO: Handle unsigned comparisons?
		c := b.Controls[0]	// 获取判断value
		switch c.Op {
		case OpLeq64:	// <=
			flags |= indVarMaxInc	// 标记包含最大值
			fallthrough
		case OpLess64:	// <
			ind, max = c.Args[0], c.Args[1]
		default:	// 为什么这里直接continue了???? 还有各种比较的类型比如int32,int8等也应该判断吧,还有大于的情况不考虑了吗????
			continue
		}

		// See if this is really an induction variable
		less := true
		// min表示循环的最小值,inc表示每次迭代时归纳变量递增的值,nxt表示iter语句
		min, inc, nxt := parseIndVar(ind)
		if min == nil {
			// We failed to parse the induction variable. Before punting, we want to check
			// whether the control op was written with arguments in non-idiomatic order,
			// so that we believe being "max" (the upper bound) is actually the induction
			// variable itself. This would happen for code like:
			//     for i := 0; len(n) > i; i++
			min, inc, nxt = parseIndVar(max)	// 尝试将max当做归纳变量进行解析
			if min == nil {
				// No recognied induction variable on either operand
				continue
			}

			// Ok, the arguments were reversed. Swap them, and remember that we're
			// looking at a ind >/>= loop (so the induction must be decrementing).
			ind, max = max, ind
			less = false
		}

		// Expect the increment to be a nonzero constant.
		if inc.Op != OpConst64 {
			continue
		}
		step := inc.AuxInt
		if step == 0 {
			continue
		}

		// Increment sign must match comparison direction.
		// When incrementing, the termination comparison must be ind </<= max.
		// When decrementing, the termination comparison must be ind >/>= max.
		// See issue 26116.
		if step > 0 && !less {	// 归纳变量是递增的但是比较关系却是大于,这会导致循环一直持续下去直到overflow
			continue
		}
		if step < 0 && less {	// 归纳变量是递减的但是比较关系却是小于,这会导致循环一直持续下去直到underflow
			continue
		}

		// If the increment is negative, swap min/max and their flags
		if step < 0 {
			min, max = max, min
			oldf := flags
			flags = indVarMaxInc
			if oldf&indVarMaxInc == 0 {	// 不包含最大值,表示不是比较是小于或者大于而不是<=或者>=
				flags |= indVarMinExc	// 不包含最小值
			}
			step = -step
		}

		// Up to now we extracted the induction variable (ind),
		// the increment delta (inc), the temporary sum (nxt),
		// the mininum value (min) and the maximum value (max).
		//
		// We also know that ind has the form (Phi min nxt) where
		// nxt is (Add inc nxt) which means: 1) inc dominates nxt
		// and 2) there is a loop starting at inc and containing nxt.
		//
		// We need to prove that the induction variable is incremented
		// only when it's smaller than the maximum value.
		// Two conditions must happen listed below to accept ind
		// as an induction variable.

		// First condition: loop entry has a single predecessor, which
		// is the header block.  This implies that b.Succs[0] is
		// reached if ind < max.
		if len(b.Succs[0].b.Preds) != 1 {
			// b.Succs[1] must exit the loop.
			continue
		}

		// Second condition: b.Succs[0] dominates nxt so that
		// nxt is computed when inc < max, meaning nxt <= max.
		if !sdom.IsAncestorEq(b.Succs[0].b, nxt.Block) {
			// inc+ind can only be reached through the branch that enters the loop.
			continue
		}

		// We can only guarantee that the loop runs within limits of induction variable
		// if (one of)
		// (1) the increment is ±1
		// (2) the limits are constants
		// (3) loop is of the form k0 upto Known_not_negative-k inclusive, step <= k
		// (4) loop is of the form k0 upto Known_not_negative-k exclusive, step <= k+1
		// (5) loop is of the form Known_not_negative downto k0, minint+step < k0
		if step > 1 {	// 如果步进是负数的话上面会更改步进的符号为正数,
			ok := false	// 如果ok为true,表示这个循环的上下边界是有意义的,循环体有可能会进入
			if min.Op == OpConst64 && max.Op == OpConst64 {	// 归纳变量的上下边界都是int常量
				if max.AuxInt > min.AuxInt && max.AuxInt%step == min.AuxInt%step { // handle overflow		归纳变量上边界大于下边界且从min可以通过步进刚好到达max
					ok = true
				}
			}
			// Handle induction variables of these forms.
			// KNN is known-not-negative.
			// SIGNED ARITHMETIC ONLY. (see switch on c above)
			// Possibilities for KNN are len and cap; perhaps we can infer others.
			// for i := 0; i <= KNN-k    ; i += k
			// for i := 0; i <  KNN-(k-1); i += k
			// Also handle decreasing.

			// "Proof" copied from https://go-review.googlesource.com/c/go/+/104041/10/src/cmd/compile/internal/ssa/loopbce.go#164
			//
			//	In the case of
			//	// PC is Positive Constant
			//	L := len(A)-PC
			//	for i := 0; i < L; i = i+PC
			//
			//	we know:
			//
			//	0 + PC does not over/underflow.
			//	len(A)-PC does not over/underflow
			//	maximum value for L is MaxInt-PC
			//	i < L <= MaxInt-PC means i + PC < MaxInt hence no overflow.

			// To match in SSA:
			// if  (a) min.Op == OpConst64(k0)
			// and (b) k0 >= MININT + step
			// and (c) max.Op == OpSubtract(Op{StringLen,SliceLen,SliceCap}, k)
			// or  (c) max.Op == OpAdd(Op{StringLen,SliceLen,SliceCap}, -k)
			// or  (c) max.Op == Op{StringLen,SliceLen,SliceCap}
			// and (d) if upto loop, require indVarMaxInc && step <= k or !indVarMaxInc && step-1 <= k

			if min.Op == OpConst64 && min.AuxInt >= step+math.MinInt64 {
				knn := max
				k := int64(0)	// 记录max中的常量
				var kArg *Value

				switch max.Op {
				case OpSub64:	// cond语句是i <= KNN-k或i < KNN-(k-1)
					knn = max.Args[0]
					kArg = max.Args[1]

				case OpAdd64:
					knn = max.Args[0]
					kArg = max.Args[1]
					if knn.Op == OpConst64 {
						knn, kArg = kArg, knn
					}
				}
				switch knn.Op {
				case OpSliceLen, OpStringLen, OpSliceCap:
				default:
					knn = nil
				}

				if kArg != nil && kArg.Op == OpConst64 {
					k = kArg.AuxInt
					if max.Op == OpAdd64 {	// 处理-k+len(slice)这种形式
						k = -k	// k变成了正数
					}
				}
				if k >= 0 && knn != nil {	// knn+(-k)或者knn-k这种形式才会导致k >= 0, knn.Op是OpSliceLen || OpStringLen || OpSliceCap会使得knn != nil
					if inc.AuxInt > 0 { // increasing iteration
						// The concern for the relation between step and k is to ensure that iv never exceeds knn
						// i.e., iv < knn-(K-1) ==> iv + K <= knn; iv <= knn-K ==> iv +K < knn
						if step <= k || flags&indVarMaxInc == 0 && step-1 == k {	// step小于等于k,或许是保证循环必定有用,循环体会执行2次以上
							ok = true
						}
					} else { // decreasing iteration
						// Will be decrementing from max towards min; max is knn-k; will only attempt decrement if
						// knn-k >[=] min; underflow is only a concern if min-step is not smaller than min.
						// This all assumes signed integer arithmetic
						// This is already assured by the test above: min.AuxInt >= step+math.MinInt64
						ok = true
					}
				}
			}

			// TODO: other unrolling idioms
			// for i := 0; i < KNN - KNN % k ; i += k
			// for i := 0; i < KNN&^(k-1) ; i += k // k a power of 2
			// for i := 0; i < KNN&(-k) ; i += k // k a power of 2

			if !ok {
				continue
			}
		}

		if f.pass.debug >= 1 {
			printIndVar(b, ind, min, max, step, flags)
		}

		iv = append(iv, indVar{
			ind:   ind,
			min:   min,
			max:   max,
			entry: b.Succs[0].b,
			flags: flags,
		})
		b.Logf("found induction variable %v (inc = %v, min = %v, max = %v)\n", ind, inc, min, max)
	}

	return iv
}

func dropAdd64(v *Value) (*Value, int64) {
	if v.Op == OpAdd64 && v.Args[0].Op == OpConst64 {
		return v.Args[1], v.Args[0].AuxInt
	}
	if v.Op == OpAdd64 && v.Args[1].Op == OpConst64 {
		return v.Args[0], v.Args[1].AuxInt
	}
	return v, 0
}

func printIndVar(b *Block, i, min, max *Value, inc int64, flags indVarFlags) {
	mb1, mb2 := "[", "]"
	if flags&indVarMinExc != 0 {
		mb1 = "("
	}
	if flags&indVarMaxInc == 0 {
		mb2 = ")"
	}

	mlim1, mlim2 := fmt.Sprint(min.AuxInt), fmt.Sprint(max.AuxInt)
	if !min.IsGenericIntConst() {
		if b.Func.pass.debug >= 2 {
			mlim1 = fmt.Sprint(min)
		} else {
			mlim1 = "?"
		}
	}
	if !max.IsGenericIntConst() {
		if b.Func.pass.debug >= 2 {
			mlim2 = fmt.Sprint(max)
		} else {
			mlim2 = "?"
		}
	}
	extra := ""
	if b.Func.pass.debug >= 2 {
		extra = fmt.Sprintf(" (%s)", i)
	}
	b.Func.Warnl(b.Pos, "Induction variable: limits %v%v,%v%v, increment %d%s", mb1, mlim1, mlim2, mb2, inc, extra)
}

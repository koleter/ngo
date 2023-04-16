// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/internal/objabi"
	"cmd/internal/src"
)

// nilcheckelim eliminates unnecessary nil checks.
// runs on machine-independent code.
func nilcheckelim(f *Func) {
	// A nil check is redundant if the same nil check was successful in a
	// dominating block. The efficacy of this pass depends heavily on the
	// efficacy of the cse pass.
	sdom := f.Sdom()

	// TODO: Eliminate more nil checks.
	// We can recursively remove any chain of fixed offset calculations,
	// i.e. struct fields and array elements, even with non-constant
	// indices: x is non-nil iff x.a.b[i].c is.

	type walkState int
	const (
		Work     walkState = iota // process nil checks and traverse to dominees
		ClearPtr                  // forget the fact that ptr is nil
	)

	type bp struct {
		block *Block // block, or nil in ClearPtr state
		ptr   *Value // if non-nil, ptr that is to be cleared in ClearPtr state
		op    walkState
	}

	work := make([]bp, 0, 256)
	work = append(work, bp{block: f.Entry}) // 从入口块开始遍历并消除nil check

	// map from value ID to bool indicating if value is known to be non-nil
	// in the current dominator path being walked. This slice is updated by
	// walkStates to maintain the known non-nil values.
	nonNilValues := make([]bool, f.NumValues())

	// make an initial pass identifying any non-nil values
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			// a value resulting from taking the address of a
			// value, or a value constructed from an offset of a
			// non-nil ptr (OpAddPtr) implies it is non-nil
			// We also assume unsafe pointer arithmetic generates non-nil pointers. See #27180.
			// We assume that SlicePtr is non-nil because we do a bounds check
			// before the slice access (and all cap>0 slices have a non-nil ptr). See #30366.
			if v.Op == OpAddr || v.Op == OpLocalAddr || v.Op == OpAddPtr || v.Op == OpOffPtr || v.Op == OpAdd32 || v.Op == OpAdd64 || v.Op == OpSub32 || v.Op == OpSub64 || v.Op == OpSlicePtr {
				nonNilValues[v.ID] = true // 通过记录某个value的ID下标为true标记这个value不为nil
			}
		}
	}

	for changed := true; changed; {
		changed = false
		for _, b := range f.Blocks {
			for _, v := range b.Values {
				// phis whose arguments are all non-nil
				// are non-nil
				if v.Op == OpPhi { // 对于一个phi函数来说,如果这个phi函数的所有参数都不为nil,那么这个phi函数也不为nil
					argsNonNil := true         // 如果为true,表示一个phi的所有参数都不为nil
					for _, a := range v.Args { // 遍历phi的所有参数并判断是否都不为nil
						if !nonNilValues[a.ID] {
							argsNonNil = false
							break
						}
					}
					if argsNonNil { // 一个phi的所有参数都不为nil
						if !nonNilValues[v.ID] { // 标记这个phi函数未被标记过不为nil
							changed = true // 重新遍历所有的块
						}
						nonNilValues[v.ID] = true // 将当前的这个phi函数添加到nonNilValues中并标记为true
					}
				}
			}
		}
	}

	// allocate auxiliary date structures for computing store order
	sset := f.newSparseSet(f.NumValues())
	defer f.retSparseSet(sset)
	storeNumber := make([]int32, f.NumValues())

	// perform a depth first walk of the dominee tree
	for len(work) > 0 {
		node := work[len(work)-1] // 这两行代码弹出最后一项
		work = work[:len(work)-1]

		switch node.op {
		case Work:
			b := node.block // 获取当前处理的块

			// First, see if we're dominated by an explicit nil check.
			if len(b.Preds) == 1 { // 将明确存在nil判断的那个指针添加到nonNilValues中
				p := b.Preds[0].b
				if p.Kind == BlockIf && p.Controls[0].Op == OpIsNonNil && p.Succs[0].b == b { // if var != nil
					if ptr := p.Controls[0].Args[0]; !nonNilValues[ptr.ID] { // 到这里表示p块中的Controls[0].Args[0]不为nil
						nonNilValues[ptr.ID] = true                     // 有明确的非空检查,将该value设置为非空
						work = append(work, bp{op: ClearPtr, ptr: ptr}) // 用于深度遍历的回退
					}
				}
			}

			// Next, order values in the current block w.r.t. stores.
			b.Values = storeOrder(b.Values, sset, storeNumber)

			pendingLines := f.cachedLineStarts // Holds statement boundaries that need to be moved to a new value/block
			pendingLines.clear()

			// Next, process values in the block.
			i := 0
			for _, v := range b.Values {
				b.Values[i] = v
				i++
				switch v.Op {
				case OpIsNonNil:
					ptr := v.Args[0]          // 获取指针
					if nonNilValues[ptr.ID] { // 已经标记过该value,确定该指针不为nil,不需要判断,可以直接设置为true
						if v.Pos.IsStmt() == src.PosIsStmt { // Boolean true is a terrible statement boundary.
							pendingLines.add(v.Pos) // pendingLines中记录pos
							v.Pos = v.Pos.WithNotStmt()
						}
						// This is a redundant explicit nil check.
						v.reset(OpConstBool)
						v.AuxInt = 1 // true
					}
				case OpNilCheck:
					ptr := v.Args[0]          // 获取待判断的指针
					if nonNilValues[ptr.ID] { // 指针不为nil
						// This is a redundant implicit nil check.
						// Logging in the style of the former compiler -- and omit line 1,
						// which is usually in generated code.
						if f.fe.Debug_checknil() && v.Pos.Line() > 1 {
							f.Warnl(v.Pos, "removed nil check")
						}
						if v.Pos.IsStmt() == src.PosIsStmt { // About to lose a statement boundary
							pendingLines.add(v.Pos) // 保存丢失的语句边界
						}
						v.reset(OpUnknown)
						f.freeValue(v) // 移除空指针检查判断
						i--
						continue
					}
					// Record the fact that we know ptr is non nil, and remember to
					// undo that information when this dominator subtree is done.
					nonNilValues[ptr.ID] = true // nil检查之后,在所有被支配节点中这个指针不为nil
					work = append(work, bp{op: ClearPtr, ptr: ptr})
					fallthrough // a non-eliminated nil check might be a good place for a statement boundary.
				default:
					if v.Pos.IsStmt() != src.PosNotStmt && !isPoorStatementOp(v.Op) && pendingLines.contains(v.Pos) { // 将以前是语句的OpIsNonNil或者OpNilCheck所记录的语句边界赋给新的value
						v.Pos = v.Pos.WithIsStmt()
						pendingLines.remove(v.Pos)
					}
				}
			}
			// This reduces the lost statement count in "go" by 5 (out of 500 total).
			for j := 0; j < i; j++ { // is this an ordering problem?
				v := b.Values[j]
				if v.Pos.IsStmt() != src.PosNotStmt && !isPoorStatementOp(v.Op) && pendingLines.contains(v.Pos) {
					v.Pos = v.Pos.WithIsStmt()
					pendingLines.remove(v.Pos)
				}
			}
			if pendingLines.contains(b.Pos) {
				b.Pos = b.Pos.WithIsStmt()
				pendingLines.remove(b.Pos)
			}
			b.truncateValues(i)

			// Add all dominated blocks to the work list.
			for w := sdom[node.block.ID].child; w != nil; w = sdom[w.ID].sibling { // 将被支配的所有直接子节点添加到队列中进行遍历
				work = append(work, bp{op: Work, block: w})
			}

		case ClearPtr: // 当到了这里,这个节点以及其支配的所有节点都已经处理过了
			nonNilValues[node.ptr.ID] = false
			continue
		}
	}
}

// All platforms are guaranteed to fault if we load/store to anything smaller than this address.
//
// This should agree with minLegalPointer in the runtime.
const minZeroPage = 4096

// faultOnLoad is true if a load to an address below minZeroPage will trigger a SIGSEGV.
var faultOnLoad = objabi.GOOS != "aix"

// nilcheckelim2 eliminates unnecessary nil checks.
// Runs after lowering and scheduling.
func nilcheckelim2(f *Func) {
	unnecessary := f.newSparseMap(f.NumValues()) // map from pointer that will be dereferenced to index of dereferencing value in b.Values[]
	defer f.retSparseMap(unnecessary)

	pendingLines := f.cachedLineStarts // Holds statement boundaries that need to be moved to a new value/block

	for _, b := range f.Blocks {
		// Walk the block backwards. Find instructions that will fault if their
		// input pointer is nil. Remove nil checks on those pointers, as the
		// faulting instruction effectively does the nil check for free.
		unnecessary.clear()
		pendingLines.clear()
		// Optimization: keep track of removed nilcheck with smallest index
		firstToRemove := len(b.Values)
		for i := len(b.Values) - 1; i >= 0; i-- { // 倒序遍历当前块的values,找到指针参数可能为nil且为nil就必定会报错的value,删除对于这些指针的nil检查
			v := b.Values[i]
			if opcodeTable[v.Op].nilCheck && unnecessary.contains(v.Args[0].ID) {
				if f.fe.Debug_checknil() && v.Pos.Line() > 1 {
					f.Warnl(v.Pos, "removed nil check")
				}
				// For bug 33724, policy is that we might choose to bump an existing position
				// off the faulting load/store in favor of the one from the nil check.

				// Iteration order means that first nilcheck in the chain wins, others
				// are bumped into the ordinary statement preservation algorithm.
				u := b.Values[unnecessary.get(v.Args[0].ID)] // 获取之前判断出不需要nil检查的value ID
				if !u.Pos.SameFileAndLine(v.Pos) {           // 与当前的nil检查value不是相同的源码位置
					if u.Pos.IsStmt() == src.PosIsStmt {
						pendingLines.add(u.Pos)
					}
					u.Pos = v.Pos // 之前的指针操作的pos改为当前的nil检查的位置
				} else if v.Pos.IsStmt() == src.PosIsStmt {
					pendingLines.add(v.Pos)
				}

				v.reset(OpUnknown) // 消除这个nil check
				firstToRemove = i
				continue
			}
			if v.Type.IsMemory() || v.Type.IsTuple() && v.Type.FieldType(1).IsMemory() {
				if v.Op == OpVarKill || v.Op == OpVarLive || (v.Op == OpVarDef && !v.Aux.(GCNode).Typ().HasPointers()) {
					// These ops don't really change memory.
					continue
					// Note: OpVarDef requires that the defined variable not have pointers.
					// We need to make sure that there's no possible faulting
					// instruction between a VarDef and that variable being
					// fully initialized. If there was, then anything scanning
					// the stack during the handling of that fault will see
					// a live but uninitialized pointer variable on the stack.
					//
					// If we have:
					//
					//   NilCheck p
					//   VarDef x
					//   x = *p
					//
					// We can't rewrite that to
					//
					//   VarDef x
					//   NilCheck p
					//   x = *p
					//
					// Particularly, even though *p faults on p==nil, we still
					// have to do the explicit nil check before the VarDef.
					// See issue #32288.
				}
				// This op changes memory.  Any faulting instruction after v that
				// we've recorded in the unnecessary map is now obsolete.
				unnecessary.clear()
			}

			// Find any pointers that this op is guaranteed to fault on if nil.
			var ptrstore [2]*Value
			ptrs := ptrstore[:0]
			if opcodeTable[v.Op].faultOnNilArg0 && (faultOnLoad || v.Type.IsMemory()) {
				// On AIX, only writing will fault.
				ptrs = append(ptrs, v.Args[0]) // 记录如果为nil就必定会报错的value
			}
			if opcodeTable[v.Op].faultOnNilArg1 && (faultOnLoad || (v.Type.IsMemory() && v.Op != OpPPC64LoweredMove)) {
				// On AIX, only writing will fault.
				// LoweredMove is a special case because it's considered as a "mem" as it stores on arg0 but arg1 is accessed as a load and should be checked.
				ptrs = append(ptrs, v.Args[1])
			}

			for _, ptr := range ptrs { // 遍历为nil就会报错的指针
				// Check to make sure the offset is small.
				switch opcodeTable[v.Op].auxType {
				case auxSym: // aux is a symbol (a *gc.Node for locals, an *obj.LSym for globals, or nil for none)
					if v.Aux != nil { // 局部变量或者全局变量的指针,这必定不为nil
						continue
					}
				case auxSymOff: // aux is a symbol, auxInt is an offset
					if v.Aux != nil || v.AuxInt < 0 || v.AuxInt >= minZeroPage {
						continue
					}
				case auxSymValAndOff: // aux is a symbol, auxInt is a ValAndOff
					off := ValAndOff(v.AuxInt).Off()
					if v.Aux != nil || off < 0 || off >= minZeroPage {
						continue
					}
				case auxInt32: // auxInt is a 32-bit integer
					// Mips uses this auxType for atomic add constant. It does not affect the effective address.
				case auxInt64: // auxInt is a 64-bit integer
					// ARM uses this auxType for duffcopy/duffzero/alignment info.
					// It does not affect the effective address.
				case auxNone:
					// offset is zero.
				default:
					v.Fatalf("can't handle aux %s (type %d) yet\n", v.auxString(), int(opcodeTable[v.Op].auxType))
				}
				// This instruction is guaranteed to fault if ptr is nil.
				// Any previous nil check op is unnecessary.
				unnecessary.set(ptr.ID, int32(i), src.NoXPos)
			}
		}
		// Remove values we've clobbered with OpUnknown.
		i := firstToRemove
		for j := i; j < len(b.Values); j++ {
			v := b.Values[j]
			if v.Op != OpUnknown {
				if !notStmtBoundary(v.Op) && pendingLines.contains(v.Pos) { // Late in compilation, so any remaining NotStmt values are probably okay now.
					v.Pos = v.Pos.WithIsStmt()
					pendingLines.remove(v.Pos)
				}
				b.Values[i] = v
				i++
			}
		}

		if pendingLines.contains(b.Pos) {
			b.Pos = b.Pos.WithIsStmt()
		}

		b.truncateValues(i)

		// TODO: if b.Kind == BlockPlain, start the analysis in the subsequent block to find
		// more unnecessary nil checks.  Would fix test/nilptr3.go:159.
	}
}

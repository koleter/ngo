// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/compile/internal/types"
	"cmd/internal/src"
)

// dse does dead-store elimination on the Function.
// Dead stores are those which are unconditionally followed by
// another store to the same location, with no intervening load.
// This implementation only works within a basic block. TODO: use something more global.
func dse(f *Func) {
	var stores []*Value	// 存储所有类型为memory的values
	loadUse := f.newSparseSet(f.NumValues())	// 被load的内存参数
	defer f.retSparseSet(loadUse)
	storeUse := f.newSparseSet(f.NumValues())	// 存储在同一个块中非phi的被其他store使用的内存类型的value ID
	defer f.retSparseSet(storeUse)
	shadowed := f.newSparseMap(f.NumValues())	// 存储value ID与OpStore或OpZero操作涉及到的内存字节数
	defer f.retSparseMap(shadowed)
	for _, b := range f.Blocks {	// 遍历所有的块
		// Find all the stores in this block. Categorize their uses:
		//  loadUse contains stores which are used by a subsequent load.
		//  storeUse contains stores which are used by a subsequent store.
		loadUse.clear()
		storeUse.clear()
		stores = stores[:0]
		for _, v := range b.Values {
			if v.Op == OpPhi {
				// Ignore phis - they will always be first and can't be eliminated
				continue
			}
			if v.Type.IsMemory() {
				stores = append(stores, v)
				for _, a := range v.Args {	// 遍历内存类型的所有参数
					if a.Block == b && a.Type.IsMemory() {	// 参数a与v在同一个块中且a也是内存类型
						storeUse.add(a.ID)
						if v.Op != OpStore && v.Op != OpZero && v.Op != OpVarDef && v.Op != OpVarKill {
							// CALL, DUFFCOPY, etc. are both
							// reads and writes.
							loadUse.add(a.ID)
						}
					}
				}
			} else {
				for _, a := range v.Args {
					if a.Block == b && a.Type.IsMemory() {
						loadUse.add(a.ID)
					}
				}
			}
		}
		if len(stores) == 0 {
			continue
		}

		// find last store in the block
		var last *Value
		for _, v := range stores {
			if storeUse.contains(v.ID) {	// 最后一个store应该是没有被使用的
				continue
			}
			if last != nil {
				b.Fatalf("two final stores - simultaneous live stores %s %s", last.LongString(), v.LongString())
			}
			last = v
		}
		if last == nil {
			b.Fatalf("no last store found - cycle?")
		}

		// Walk backwards looking for dead stores. Keep track of shadowed addresses.
		// A "shadowed address" is a pointer and a size describing a memory region that
		// is known to be written. We keep track of shadowed addresses in the shadowed
		// map, mapping the ID of the address to the size of the shadowed region.
		// Since we're walking backwards, writes to a shadowed region are useless,
		// as they will be immediately overwritten.
		shadowed.clear()
		v := last

	walkloop:
		if loadUse.contains(v.ID) {	// 有load操作,可能会读内存数据,将shadowed清空防止脏读
			// Someone might be reading this memory state.
			// Clear all shadowed addresses.
			shadowed.clear()
		}
		if v.Op == OpStore || v.Op == OpZero {	// v是store或者内存清零的操作
			var sz int64	// 此次操作的内存字节数
			if v.Op == OpStore {
				sz = v.Aux.(*types.Type).Size()
			} else { // OpZero
				sz = v.AuxInt
			}
			// 该内存状态在之后会被存储或者赋零值且覆盖了本次的影响范围
			if shadowedSize := int64(shadowed.get(v.Args[0].ID)); shadowedSize != -1 && shadowedSize >= sz {
				// Modify the store/zero into a copy of the memory state,
				// effectively eliding the store operation.
				if v.Op == OpStore {	// 没有必要在本次存储了,因为之后的存储会覆盖本次的操作影响
					// store addr value mem
					v.SetArgs1(v.Args[2])
				} else {
					// zero addr mem
					v.SetArgs1(v.Args[1])
				}
				v.Aux = nil
				v.AuxInt = 0
				v.Op = OpCopy
			} else {
				if sz > 0x7fffffff { // work around sparseMap's int32 value type
					sz = 0x7fffffff
				}
				shadowed.set(v.Args[0].ID, int32(sz), src.NoXPos)
			}
		}
		// walk to previous store
		if v.Op == OpPhi {
			// At start of block.  Move on to next block.
			// The memory phi, if it exists, is always
			// the first logical store in the block.
			// (Even if it isn't the first in the current b.Values order.)
			continue
		}
		for _, a := range v.Args {
			if a.Block == b && a.Type.IsMemory() {	// 找到之前的memory value
				v = a
				goto walkloop
			}
		}
	}
}

// elimDeadAutosGeneric deletes autos that are never accessed. To achieve this
// we track the operations that the address of each auto reaches and if it only
// reaches stores then we delete all the stores. The other operations will then
// be eliminated by the dead code elimination pass.
func elimDeadAutosGeneric(f *Func) {
	addr := make(map[*Value]GCNode) // values that the address of the auto reaches
	elim := make(map[*Value]GCNode) // values that could be eliminated if the auto is
	used := make(map[GCNode]bool)   // used autos that must be kept

	// visit the value and report whether any of the maps are updated
	visit := func(v *Value) (changed bool) {
		args := v.Args
		switch v.Op {
		case OpAddr, OpLocalAddr:
			// Propagate the address if it points to an auto.
			n, ok := v.Aux.(GCNode)
			if !ok || n.StorageClass() != ClassAuto {	// 不是GCNode结构体或者不是局部变量就返回
				return
			}
			if addr[v] == nil {
				addr[v] = n	// 记录取了哪个变量的地址
				changed = true
			}
			return
		case OpVarDef, OpVarKill:
			// v should be eliminated if we eliminate the auto.
			n, ok := v.Aux.(GCNode)
			if !ok || n.StorageClass() != ClassAuto {
				return
			}
			if elim[v] == nil {
				elim[v] = n
				changed = true
			}
			return
		case OpVarLive:
			// Don't delete the auto if it needs to be kept alive.

			// We depend on this check to keep the autotmp stack slots
			// for open-coded defers from being removed (since they
			// may not be used by the inline code, but will be used by
			// panic processing).
			n, ok := v.Aux.(GCNode)
			if !ok || n.StorageClass() != ClassAuto {
				return
			}
			if !used[n] {
				used[n] = true
				changed = true
			}
			return
		case OpStore, OpMove, OpZero:
			// v should be eliminated if we eliminate the auto.
			n, ok := addr[args[0]]	// 存储,move或清零了一个指针
			if ok && elim[v] == nil {	// 取过变量n的地址
				elim[v] = n
				changed = true
			}
			// Other args might hold pointers to autos.
			args = args[1:]
		}

		// The code below assumes that we have handled all the ops
		// with sym effects already. Sanity check that here.
		// Ignore Args since they can't be autos.
		if v.Op.SymEffect() != SymNone && v.Op != OpArg {
			panic("unhandled op with sym effect")
		}

		if v.Uses == 0 && v.Op != OpNilCheck || len(args) == 0 {
			// Nil check has no use, but we need to keep it.
			return
		}
		// (被使用的变量或者OpNilCheck)且有参数
		// If the address of the auto reaches a memory or control
		// operation not covered above then we probably need to keep it.
		// We also need to keep autos if they reach Phis (issue #26153).		因为存储到phi的其他参数可能对程序可见
		if v.Type.IsMemory() || v.Type.IsFlags() || v.Op == OpPhi || v.MemoryArg() != nil {	// 保留内存操作,flag,phi
			for _, a := range args {
				if n, ok := addr[a]; ok {
					if !used[n] {
						used[n] = true
						changed = true
					}
				}
			}
			return
		}

		// Propagate any auto addresses through v.
		node := GCNode(nil)
		for _, a := range args {
			if n, ok := addr[a]; ok && !used[n] {	// a是取地址操作且n没有被使用
				if node == nil {
					node = n
				} else if node != n {	// 至少两个参数是不一样的
					// Most of the time we only see one pointer
					// reaching an op, but some ops can take
					// multiple pointers (e.g. NeqPtr, Phi etc.).
					// This is rare, so just propagate the first
					// value to keep things simple.
					used[n] = true	// 这里貌似是保留了第二个指针
					changed = true
				}
			}
		}
		if node == nil {
			return
		}
		if addr[v] == nil {	// node不为nil,表示有一个指针
			// The address of an auto reaches this op.
			addr[v] = node
			changed = true
			return
		}
		if addr[v] != node {	// 多个指针reaches this op
			// This doesn't happen in practice, but catch it just in case.
			used[node] = true
			changed = true
		}
		return
	}

	iterations := 0
	for {
		if iterations == 4 {	// 最多4次就放弃优化
			// give up
			return
		}
		iterations++
		changed := false
		for _, b := range f.Blocks {
			for _, v := range b.Values {
				changed = visit(v) || changed
			}
			// keep the auto if its address reaches a control value
			for _, c := range b.ControlValues() {
				if n, ok := addr[c]; ok && !used[n] {
					used[n] = true
					changed = true
				}
			}
		}
		if !changed {
			break
		}
	}

	// Eliminate stores to unread autos.
	for v, n := range elim {
		if used[n] {	// n被使用就不消除
			continue
		}
		// replace with OpCopy
		v.SetArgs1(v.MemoryArg())
		v.Aux = nil
		v.AuxInt = 0
		v.Op = OpCopy
	}
}

// elimUnreadAutos deletes stores (and associated bookkeeping ops VarDef and VarKill)
// to autos that are never read from.
func elimUnreadAutos(f *Func) {
	// Loop over all ops that affect autos taking note of which
	// autos we need and also stores that we might be able to
	// eliminate.
	seen := make(map[GCNode]bool)
	var stores []*Value
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			n, ok := v.Aux.(GCNode)
			if !ok {
				continue
			}
			if n.StorageClass() != ClassAuto {	// 必须是个局部栈变量
				continue
			}

			effect := v.Op.SymEffect()
			switch effect {
			case SymNone, SymWrite:	// 此操作对变量没有影响或者写了数据,只有读了才是有用的
				// If we haven't seen the auto yet
				// then this might be a store we can
				// eliminate.
				if !seen[n] {
					stores = append(stores, v)
				}
			default:
				// Assume the auto is needed (loaded,
				// has its address taken, etc.).
				// Note we have to check the uses
				// because dead loads haven't been
				// eliminated yet.
				if v.Uses > 0 {
					seen[n] = true
				}
			}
		}
	}

	// Eliminate stores to unread autos.
	for _, store := range stores {
		n, _ := store.Aux.(GCNode)
		if seen[n] {	// 某个变量在后面有取地址或者读的操作,这种情况下的store不能删
			continue
		}

		// replace store with OpCopy
		store.SetArgs1(store.MemoryArg())
		store.Aux = nil
		store.AuxInt = 0
		store.Op = OpCopy
	}
}

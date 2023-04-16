// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// TODO: live at start of block instead?

package ssa

import (
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"fmt"
)

type stackAllocState struct {
	f *Func

	// live is the output of stackalloc.
	// live[b.id] = live values at the end of block b.
	live [][]ID		// 块ID -> 块末尾通过栈槽保存的live values或者spill values

	// The following slices are reused across multiple users
	// of stackAllocState.
	values    []stackValState
	interfere [][]ID // interfere[v.id] = values that interfere with v.		类型相同或者至少一个是参数(OpArg)
	names     []LocalSlot	// vID对应存储这个value的栈槽
	slots     []int		// vID对应used的index
	used      []bool

	nArgSlot, // Number of Values sourced to arg slot		需要栈槽的OpArg values的数量
	nNotNeed, // Number of Values not needing a stack slot	不需要栈槽的values数量
	nNamedSlot, // Number of Values using a named stack slot
	nReuse, // Number of values reusing a stack slot
	nAuto, // Number of autos allocated for stack slots.	// 自动分配的栈槽数量
	nSelfInterfere int32 // Number of self-interferences
}

func newStackAllocState(f *Func) *stackAllocState {
	s := f.Cache.stackAllocState
	if s == nil {
		return new(stackAllocState)
	}
	if s.f != nil {
		f.fe.Fatalf(src.NoXPos, "newStackAllocState called without previous free")
	}
	return s
}

func putStackAllocState(s *stackAllocState) {
	for i := range s.values {
		s.values[i] = stackValState{}
	}
	for i := range s.interfere {
		s.interfere[i] = nil
	}
	for i := range s.names {
		s.names[i] = LocalSlot{}
	}
	for i := range s.slots {
		s.slots[i] = 0
	}
	for i := range s.used {
		s.used[i] = false
	}
	s.f.Cache.stackAllocState = s
	s.f = nil
	s.live = nil
	s.nArgSlot, s.nNotNeed, s.nNamedSlot, s.nReuse, s.nAuto, s.nSelfInterfere = 0, 0, 0, 0, 0, 0
}

type stackValState struct {
	typ      *types.Type	// value的type
	/*
		if v.Op == OpStoreReg{
			s.values[v.Args[0].ID].spill = v
		}
	*/
	spill    *Value	// 当前value对应的spill value(Op为OpStoreReg的value)
	needSlot bool	// 是否需要栈槽(活跃value且没有为其分配寄存器)
	isArg    bool	// v.Op == OpArg
}

// stackalloc allocates storage in the stack frame for
// all Values that did not get a register.
// Returns a map from block ID to the stack values live at the end of that block.
// spillLive: 在后继块中会使用且不能重新实现的value会为其创建一个spill并添加到对应块ID的切片中
func stackalloc(f *Func, spillLive [][]ID) [][]ID {
	if f.pass.debug > stackDebug {
		fmt.Println("before stackalloc")
		fmt.Println(f.String())
	}
	s := newStackAllocState(f)
	// 计算出需要栈槽的live values以及构造干涉图
	s.init(f, spillLive)
	defer putStackAllocState(s)

	s.stackalloc()
	if f.pass.stats > 0 {
		f.LogStat("stack_alloc_stats",
			s.nArgSlot, "arg_slots", s.nNotNeed, "slot_not_needed",
			s.nNamedSlot, "named_slots", s.nAuto, "auto_slots",
			s.nReuse, "reused_slots", s.nSelfInterfere, "self_interfering")
	}

	return s.live
}

// spillLive: 在后继块中会使用且不能重新实现的value会为其创建一个spill并添加到对应块ID的切片中
func (s *stackAllocState) init(f *Func, spillLive [][]ID) {
	s.f = f

	// Initialize value information.
	if n := f.NumValues(); cap(s.values) >= n {
		s.values = s.values[:n]
	} else {
		s.values = make([]stackValState, n)
	}
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			s.values[v.ID].typ = v.Type		// 存储的value的类型
			// 没有为其分配寄存器,所以需要通过栈槽进行存储
			s.values[v.ID].needSlot = !v.Type.IsMemory() && !v.Type.IsVoid() && !v.Type.IsFlags() && f.getHome(v.ID) == nil && !v.rematerializeable() && !v.OnWasmStack
			s.values[v.ID].isArg = v.Op == OpArg
			if f.pass.debug > stackDebug && s.values[v.ID].needSlot {
				fmt.Printf("%s needs a stack slot\n", v)
			}
			if v.Op == OpStoreReg {		// 第一个参数代表的寄存器中的值保存到位于栈上的某处内存
				s.values[v.Args[0].ID].spill = v	// 记录第一个参数是因为v要spill的
			}
		}
	}

	// Compute liveness info for values needing a slot.
	s.computeLive(spillLive)

	// Build interference graph among values needing a slot.
	s.buildInterferenceGraph()
}

func (s *stackAllocState) stackalloc() {
	f := s.f

	// Build map from values to their names, if any.
	// A value may be associated with more than one name (e.g. after
	// the assignment i=j). This step picks one name per value arbitrarily.
	if n := f.NumValues(); cap(s.names) >= n {
		s.names = s.names[:n]
	} else {
		s.names = make([]LocalSlot, n)
	}
	names := s.names	// vID -> 栈槽
	for _, name := range f.Names {	// 遍历所有的栈槽
		// Note: not "range f.NamedValues" above, because
		// that would be nondeterministic.
		for _, v := range f.NamedValues[name] {	// 遍历存储在这个栈槽的所有values
			names[v.ID] = name	// 记录vID与栈槽的关系
		}
	}

	// Allocate args to their assigned locations.
	for _, v := range f.Entry.Values {	// 遍历entry块的values
		if v.Op != OpArg {	// 找到参数
			continue
		}
		loc := LocalSlot{N: v.Aux.(GCNode), Type: v.Type, Off: v.AuxInt}	// 为参数创建一个栈槽
		if f.pass.debug > stackDebug {
			fmt.Printf("stackalloc %s to %s\n", v, loc)
		}
		f.setHome(v, loc)	// 设置v保存在loc中
	}

	// For each type, we keep track of all the stack slots we
	// have allocated for that type.
	// TODO: share slots among equivalent types. We would need to
	// only share among types with the same GC signature. See the
	// type.Equal calls below for where this matters.
	locations := map[*types.Type][]LocalSlot{}

	// Each time we assign a stack slot to a value v, we remember
	// the slot we used via an index into locations[v.Type].
	slots := s.slots	// vID对应locs的index,表示为value分配的栈槽
	if n := f.NumValues(); cap(slots) >= n {
		slots = slots[:n]
	} else {
		slots = make([]int, n)
		s.slots = slots
	}
	for i := range slots {	// 初始话slots中的所有元素为-1
		slots[i] = -1
	}

	// Pick a stack slot for each value needing one.
	var used []bool		// used[i]为true表示栈槽locations[v.Type][i]在使用中
	if n := f.NumValues(); cap(s.used) >= n {
		used = s.used[:n]
	} else {
		used = make([]bool, n)
		s.used = used
	}
	for _, b := range f.Blocks {	// 遍历所有块
		for _, v := range b.Values {	// 遍历所有块中的values
			if !s.values[v.ID].needSlot {
				s.nNotNeed++	// 不需要栈槽的value加一
				continue
			}
			if v.Op == OpArg {
				s.nArgSlot++
				continue // already picked
			}

			// If this is a named value, try to use the name as
			// the spill location.
			var name LocalSlot
			if v.Op == OpStoreReg {
				name = names[v.Args[0].ID]	// 根据spill的vID获取spill的栈槽
			} else {
				name = names[v.ID]	// 获取vID对应的栈槽
			}
			if name.N != nil && v.Type.Compare(name.Type) == types.CMPeq {	// v与栈槽的类型相同
				for _, id := range s.interfere[v.ID] {	// 遍历v对应的干涉切片找到可能干扰自身的情况
					h := f.getHome(id)	// 获取干涉value的Location
					if h != nil && h.(LocalSlot).N == name.N && h.(LocalSlot).Off == name.Off {	// 互相干扰的value拥有相同的栈槽
						// A variable can interfere with itself.
						// It is rare, but it can happen.
						s.nSelfInterfere++
						goto noname
					}
				}
				// 类型相符且不是自我干涉的情况
				if f.pass.debug > stackDebug {
					fmt.Printf("stackalloc %s to %s\n", v, name)
				}
				s.nNamedSlot++
				f.setHome(v, name)	// 设置v用name存储
				continue
			}
		noname:
			// Set of stack slots we could reuse.
			locs := locations[v.Type]	// 找到存储相同类型的一组LocalSlot
			// Mark all positions in locs used by interfering values.
			for i := 0; i < len(locs); i++ {	// 标记所有的栈槽都未使用
				used[i] = false
			}
			for _, xid := range s.interfere[v.ID] {	// 遍历干涉v的values
				slot := slots[xid]
				if slot >= 0 {	// xid对应的value存在使用的栈槽
					used[slot] = true	// 标记locs中的第slot个栈槽已经使用了
				}
			}
			// Find an unused stack slot.
			var i int	// 找到相同类型的栈槽中未被使用的
			for i = 0; i < len(locs); i++ {
				if !used[i] {	// 栈槽未使用
					s.nReuse++	// 记录重新使用栈槽的value加一
					break
				}
			}
			// If there is no unused stack slot, allocate a new one.
			if i == len(locs) {		// 没有在相同类型的栈槽切片中找到未使用的栈槽
				s.nAuto++	// 自动分配的栈槽数量加一
				locs = append(locs, LocalSlot{N: f.fe.Auto(v.Pos, v.Type), Type: v.Type, Off: 0})
				locations[v.Type] = locs	// 赋值回去
			}
			// Use the stack variable at that index for v.
			loc := locs[i]	// 获取未使用的栈槽
			if f.pass.debug > stackDebug {
				fmt.Printf("stackalloc %s to %s\n", v, loc)
			}
			f.setHome(v, loc)	// 关联v与LocalSlot
			slots[v.ID] = i		// 记录v使用了第i个栈槽
		}
	}
}

// computeLive computes a map from block ID to a list of
// stack-slot-needing value IDs live at the end of that block.
// TODO: this could be quadratic if lots of variables are live across lots of
// basic blocks. Figure out a way to make this function (or, more precisely, the user
// of this function) require only linear size & time.
// spillLive: 在后继块中会使用且不能重新实现的value会为其创建一个spill并添加到对应块ID的切片中
func (s *stackAllocState) computeLive(spillLive [][]ID) {
	s.live = make([][]ID, s.f.NumBlocks())
	var phis []*Value
	live := s.f.newSparseSet(s.f.NumValues())	// 存储当前块的起始活跃且只能通过栈槽进行存储的value ID
	defer s.f.retSparseSet(live)
	t := s.f.newSparseSet(s.f.NumValues())
	defer s.f.retSparseSet(t)

	// Instead of iterating over f.Blocks, iterate over their postordering.
	// Liveness information flows backward, so starting at the end
	// increases the probability that we will stabilize quickly.
	po := s.f.postorder()
	for {
		changed := false
		for _, b := range po {
			// Start with known live values at the end of the block
			live.clear()
			live.addAll(s.live[b.ID])	// 添加当前块末尾处的live values(没有为其分配的寄存器,只能通过栈槽存储)

			// Propagate backwards to the start of the block
			phis = phis[:0]	// 存储当前块中非memory与void类型的phi
			for i := len(b.Values) - 1; i >= 0; i-- {	// 反向遍历b块中的values
				v := b.Values[i]
				live.remove(v.ID)	// 设置v不再活跃
				if v.Op == OpPhi {
					// Save phi for later.
					// Note: its args might need a stack slot even though
					// the phi itself doesn't. So don't use needSlot.
					if !v.Type.IsMemory() && !v.Type.IsVoid() {
						phis = append(phis, v)
					}
					continue
				}
				for _, a := range v.Args {	// 遍历v的所有参数,如果参数需要栈槽,设置参数活跃
					if s.values[a.ID].needSlot {
						live.add(a.ID)
					}
				}
			}

			// for each predecessor of b, expand its list of live-at-end values
			// invariant: s contains the values live at the start of b (excluding phi inputs)
			for i, e := range b.Preds {		// 遍历b的所有前驱
				p := e.b	// 前驱块
				t.clear()
				t.addAll(s.live[p.ID])	// 在t中添加前驱块需要栈槽存储的live value ID
				t.addAll(live.contents())	// 在t中添加当前块起始处需要栈槽存储的live value ID
				t.addAll(spillLive[p.ID])	// 添加前驱块末尾处的live spill
				for _, v := range phis {
					a := v.Args[i]	// 获取从前驱传进来的参数
					if s.values[a.ID].needSlot {	// phi的参数需要栈槽
						t.add(a.ID)		// 参数从前驱传入,必然活跃
					}
					if spill := s.values[a.ID].spill; spill != nil {	// 当前value被spill,设置spill value活跃
						//TODO: remove?  Subsumed by SpillUse?
						t.add(spill.ID)
					}
				}
				if t.size() == len(s.live[p.ID]) {
					continue
				}
				// grow p's live set
				s.live[p.ID] = append(s.live[p.ID][:0], t.contents()...)
				changed = true
			}
		}

		if !changed {
			break
		}
	}
	if s.f.pass.debug > stackDebug {
		for _, b := range s.f.Blocks {
			fmt.Printf("stacklive %s %v\n", b, s.live[b.ID])
		}
	}
}

func (f *Func) getHome(vid ID) Location {
	if int(vid) >= len(f.RegAlloc) {
		return nil
	}
	return f.RegAlloc[vid]
}

func (f *Func) setHome(v *Value, loc Location) {
	for v.ID >= ID(len(f.RegAlloc)) {
		f.RegAlloc = append(f.RegAlloc, nil)
	}
	f.RegAlloc[v.ID] = loc
}

func (s *stackAllocState) buildInterferenceGraph() {
	f := s.f
	if n := f.NumValues(); cap(s.interfere) >= n {
		s.interfere = s.interfere[:n]
	} else {
		s.interfere = make([][]ID, n)
	}
	live := f.newSparseSet(f.NumValues())	// 记录当前需要栈槽的vID
	defer f.retSparseSet(live)
	for _, b := range f.Blocks {
		// Propagate liveness backwards to the start of the block.
		// Two values interfere if one is defined while the other is live.
		live.clear()
		live.addAll(s.live[b.ID])	// live添加块末尾通过栈槽保存的live values或者spill values
		for i := len(b.Values) - 1; i >= 0; i-- {	// 倒序遍历values
			v := b.Values[i]
			if s.values[v.ID].needSlot {	// v需要栈槽
				live.remove(v.ID)	// 从live中移除vID
				for _, id := range live.contents() {	// 遍历剩余的仍需栈槽的vID
					// Note: args can have different types and still interfere
					// (with each other or with other values). See issue 23522.
					// 找到一个value与v类型相同 || v是一个参数	|| 当前value是一个参数
					if s.values[v.ID].typ.Compare(s.values[id].typ) == types.CMPeq || v.Op == OpArg || s.values[id].isArg {
						s.interfere[v.ID] = append(s.interfere[v.ID], id)	// 记录干涉关系
						s.interfere[id] = append(s.interfere[id], v.ID)
					}
				}
			}
			for _, a := range v.Args {
				if s.values[a.ID].needSlot {
					live.add(a.ID)	// 参数需要栈槽就添加到live中记录
				}
			}
			if v.Op == OpArg && s.values[v.ID].needSlot {	// 需要栈槽的参数
				// OpArg is an input argument which is pre-spilled.
				// We add back v.ID here because we want this value
				// to appear live even before this point. Being live
				// all the way to the start of the entry block prevents other
				// values from being allocated to the same slot and clobbering
				// the input value before we have a chance to load it.
				live.add(v.ID)	// 保持这个参数是活跃的
			}
		}
	}
	if f.pass.debug > stackDebug {
		for vid, i := range s.interfere {
			if len(i) > 0 {
				fmt.Printf("v%d interferes with", vid)
				for _, x := range i {
					fmt.Printf(" v%d", x)
				}
				fmt.Println()
			}
		}
	}
}

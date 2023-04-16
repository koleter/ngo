// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/compile/internal/types"
	"container/heap"
	"sort"
)

const (
	ScorePhi = iota // towards top of block
	ScoreArg
	ScoreNilCheck
	ScoreReadTuple
	ScoreVarDef
	ScoreMemory
	ScoreReadFlags
	ScoreDefault
	ScoreFlags
	ScoreControl // towards bottom of block
)

type ValHeap struct {
	a     []*Value
	score []int8
}

func (h ValHeap) Len() int      { return len(h.a) }
func (h ValHeap) Swap(i, j int) { a := h.a; a[i], a[j] = a[j], a[i] }

func (h *ValHeap) Push(x interface{}) {
	// Push and Pop use pointer receivers because they modify the slice's length,
	// not just its contents.
	v := x.(*Value)
	h.a = append(h.a, v)
}
func (h *ValHeap) Pop() interface{} {
	old := h.a
	n := len(old)
	x := old[n-1]
	h.a = old[0 : n-1]
	return x
}
func (h ValHeap) Less(i, j int) bool {
	x := h.a[i]
	y := h.a[j]
	sx := h.score[x.ID]	// 获取x的score
	sy := h.score[y.ID]	// 获取y的score
	if c := sx - sy; c != 0 {	// score较大的在前面
		return c > 0
	}
	// 源码位置不相等时后出现的优先调度
	if x.Pos != y.Pos { // Favor in-order line stepping
		return x.Pos.After(y.Pos)
	}
	if x.Op != OpPhi {
		// 对于不是phi的value,两个value参数少的优先调度
		if c := len(x.Args) - len(y.Args); c != 0 {
			return c < 0
		}
	}
	// 被使用次数少的优先调度
	if c := x.Uses - y.Uses; c != 0 {
		return c < 0
	}
	// These comparisons are fairly arbitrary.
	// The goal here is stability in the face
	// of unrelated changes elsewhere in the compiler.
	if c := x.AuxInt - y.AuxInt; c != 0 {	// AuxInt大的优先调度
		return c > 0
	}
	if cmp := x.Type.Compare(y.Type); cmp != types.CMPeq {	// 通过类型比较,大的优先调度
		return cmp == types.CMPgt
	}
	return x.ID > y.ID	// Id大的优先调度
}

func (op Op) isLoweredGetClosurePtr() bool {
	switch op {
	case OpAMD64LoweredGetClosurePtr, OpPPC64LoweredGetClosurePtr, OpARMLoweredGetClosurePtr, OpARM64LoweredGetClosurePtr,
		Op386LoweredGetClosurePtr, OpMIPS64LoweredGetClosurePtr, OpS390XLoweredGetClosurePtr, OpMIPSLoweredGetClosurePtr,
		OpRISCV64LoweredGetClosurePtr, OpWasmLoweredGetClosurePtr:
		return true
	}
	return false
}

// Schedule the Values in each Block. After this phase returns, the
// order of b.Values matters and is the order in which those values
// will appear in the assembly output. For now it generates a
// reasonable valid schedule using a priority queue. TODO(khr):
// schedule smarter.
func schedule(f *Func) {
	// For each value, the number of times it is used in the block
	// by values that have not been scheduled yet.
	uses := make([]int32, f.NumValues())	// 当前块中的value的使用次数

	// reusable priority queue
	priq := new(ValHeap)

	// "priority" for a value
	score := make([]int8, f.NumValues())

	// scheduling order. We queue values in this list in reverse order.
	// A constant bound allows this to be stack-allocated. 64 is
	// enough to cover almost every schedule call.
	order := make([]*Value, 0, 64)

	// maps mem values to the next live memory value
	nextMem := make([]*Value, f.NumValues())	// 记录当前mem value的下一个mem value
	// additional pretend arguments for each Value. Used to enforce load/store ordering.
	additionalArgs := make([][]*Value, f.NumValues())

	for _, b := range f.Blocks {
		// Compute score. Larger numbers are scheduled closer to the end of the block.
		for _, v := range b.Values {
			switch {
			case v.Op.isLoweredGetClosurePtr():
				// We also score GetLoweredClosurePtr as early as possible to ensure that the
				// context register is not stomped. GetLoweredClosurePtr should only appear
				// in the entry block where there are no phi functions, so there is no
				// conflict or ambiguity here.
				if b != f.Entry {
					f.Fatalf("LoweredGetClosurePtr appeared outside of entry block, b=%s", b.String())
				}
				score[v.ID] = ScorePhi
			case v.Op == OpAMD64LoweredNilCheck || v.Op == OpPPC64LoweredNilCheck ||
				v.Op == OpARMLoweredNilCheck || v.Op == OpARM64LoweredNilCheck ||
				v.Op == Op386LoweredNilCheck || v.Op == OpMIPS64LoweredNilCheck ||
				v.Op == OpS390XLoweredNilCheck || v.Op == OpMIPSLoweredNilCheck ||
				v.Op == OpRISCV64LoweredNilCheck || v.Op == OpWasmLoweredNilCheck:
				// Nil checks must come before loads from the same address.
				score[v.ID] = ScoreNilCheck
			case v.Op == OpPhi:
				// We want all the phis first.
				score[v.ID] = ScorePhi
			case v.Op == OpVarDef:
				// We want all the vardefs next.
				score[v.ID] = ScoreVarDef
			case v.Op == OpArg:
				// We want all the args as early as possible, for better debugging.
				score[v.ID] = ScoreArg
			case v.Type.IsMemory():
				// Schedule stores as early as possible. This tends to
				// reduce register pressure. It also helps make sure
				// VARDEF ops are scheduled before the corresponding LEA.
				score[v.ID] = ScoreMemory
			case v.Op == OpSelect0 || v.Op == OpSelect1:
				// Schedule the pseudo-op of reading part of a tuple
				// immediately after the tuple-generating op, since
				// this value is already live. This also removes its
				// false dependency on the other part of the tuple.
				// Also ensures tuple is never spilled.
				score[v.ID] = ScoreReadTuple
			case v.Type.IsFlags() || v.Type.IsTuple() && v.Type.FieldType(1).IsFlags():
				// Schedule flag register generation as late as possible.
				// This makes sure that we only have one live flags
				// value at a time.
				score[v.ID] = ScoreFlags
			default:
				score[v.ID] = ScoreDefault
				// If we're reading flags, schedule earlier to keep flag lifetime short.
				for _, a := range v.Args {
					if a.Type.IsFlags() {
						score[v.ID] = ScoreReadFlags
					}
				}
			}
		}
	}

	for _, b := range f.Blocks {
		// Find store chain for block.
		// Store chains for different blocks overwrite each other, so
		// the calculated store chain is good only for this block.
		for _, v := range b.Values {	// 找出每个mem value的下一个mem value
			if v.Op != OpPhi && v.Type.IsMemory() {
				for _, w := range v.Args {
					if w.Type.IsMemory() {
						nextMem[w.ID] = v
					}
				}
			}
		}

		// Compute uses.
		for _, v := range b.Values {
			if v.Op == OpPhi {
				// If a value is used by a phi, it does not induce
				// a scheduling edge because that use is from the
				// previous iteration.
				continue
			}
			// 到这里v必定不是phi
			for _, w := range v.Args {	// 遍历v的参数
				if w.Block == b {	// 在当前块中定义的value
					uses[w.ID]++
				}
				// Any load must come before the following store.
				if !v.Type.IsMemory() && w.Type.IsMemory() {	// v is a load.
					s := nextMem[w.ID]	// 找到w的下一个mem变量
					if s == nil || s.Block != b {
						continue
					}
					// s是一个在b块中定义的mem变量
					additionalArgs[s.ID] = append(additionalArgs[s.ID], v)	// v必定要在s之前,也就是在下一次内存改变之前
					uses[v.ID]++	// load的use加一,v视为s的一个假装的参数,这是为了防止下面在v未被调度时先调度了s
				}
			}
		}

		for _, c := range b.ControlValues() {	// 遍历块的控制语句
			// Force the control values to be scheduled at the end,
			// unless they are phi values (which must be first).
			// OpArg also goes first -- if it is stack it register allocates
			// to a LoadReg, if it is register it is from the beginning anyway.
			if c.Op == OpPhi || c.Op == OpArg {
				continue
			}
			// 控制语句不是phi也不是arg
			score[c.ID] = ScoreControl

			// Schedule values dependent on the control values at the end.
			// This reduces the number of register spills. We don't find
			// all values that depend on the controls, just values with a
			// direct dependency. This is cheaper and in testing there
			// was no difference in the number of spills.
			for _, v := range b.Values {
				if v.Op != OpPhi {
					for _, a := range v.Args {
						if a == c {		// b块中的非phi value v中使用了b块中的ControlValues
							score[v.ID] = ScoreControl	// 标记使用控制语句作为参数的value的score为ScoreControl
						}
					}
				}
			}

		}

		// To put things into a priority queue
		// The values that should come last are least.
		priq.score = score
		priq.a = priq.a[:0]

		// Initialize priority queue with schedulable values.
		for _, v := range b.Values {
			if uses[v.ID] == 0 {	// v在当前块中已经不再被使用了,所以可以处理,将其放到代码的前面
				heap.Push(priq, v)	// 将v添加到priq.a中
			}
		}

		// Schedule highest priority value, update use counts, repeat.
		order = order[:0]
		tuples := make(map[ID][]*Value)		// 第一维的索引为某个tuple的value ID,第二维记录获取这个tuple的两个元素的value
		for priq.Len() > 0 {	// 这个循环中使用的类似于拓扑排序
			// Find highest priority schedulable value.
			// Note that schedule is assembled backwards.

			v := heap.Pop(priq).(*Value)	// 从优先队列中弹出一项,这是优先级最高的一项

			// Add it to the schedule.
			// Do not emit tuple-reading ops until we're ready to emit the tuple-generating op.
			//TODO: maybe remove ReadTuple score above, if it does not help on performance
			switch {
			case v.Op == OpSelect0:
				if tuples[v.Args[0].ID] == nil {
					tuples[v.Args[0].ID] = make([]*Value, 2)
				}
				tuples[v.Args[0].ID][0] = v	// v获取v.Args[0]对应tuple的第一项
			case v.Op == OpSelect1:
				if tuples[v.Args[0].ID] == nil {
					tuples[v.Args[0].ID] = make([]*Value, 2)
				}
				tuples[v.Args[0].ID][1] = v	// v获取v.Args[0]对应tuple的第二项
			case v.Type.IsTuple() && tuples[v.ID] != nil:	// 之前遍历的value中有用到了当前tuple的OpSelect0或者OpSelect1
				if tuples[v.ID][1] != nil {
					order = append(order, tuples[v.ID][1])
				}
				if tuples[v.ID][0] != nil {
					order = append(order, tuples[v.ID][0])
				}
				delete(tuples, v.ID)
				fallthrough
			default:
				order = append(order, v)	// 直接添加到order列表中
			}

			// Update use counts of arguments.
			for _, w := range v.Args {
				if w.Block != b {
					continue
				}
				uses[w.ID]--	// 参数的uses减一
				if uses[w.ID] == 0 {	// 参数不被使用了就放到队列中
					// All uses scheduled, w is now schedulable.
					heap.Push(priq, w)
				}
			}
			for _, w := range additionalArgs[v.ID] {
				uses[w.ID]--
				if uses[w.ID] == 0 {
					// All uses scheduled, w is now schedulable.
					heap.Push(priq, w)
				}
			}
		}
		if len(order) != len(b.Values) {
			f.Fatalf("schedule does not include all values in block %s", b)
		}
		for i := 0; i < len(b.Values); i++ {	// order的倒序就是我们想要的顺序
			b.Values[i] = order[len(b.Values)-1-i]
		}
	}

	f.scheduled = true
}

// storeOrder orders values with respect to stores. That is,
// if v transitively depends on store s, v is ordered after s,
// otherwise v is ordered before s.
// Specifically, values are ordered like
//   store1
//   NilCheck that depends on store1
//   other values that depends on store1
//   store2
//   NilCheck that depends on store2
//   other values that depends on store2
//   ...
// The order of non-store and non-NilCheck values are undefined
// (not necessarily dependency order). This should be cheaper
// than a full scheduling as done above.
// Note that simple dependency order won't work: there is no
// dependency between NilChecks and values like IsNonNil.
// Auxiliary data structures are passed in as arguments, so
// that they can be allocated in the caller and be reused.
// This function takes care of reset them.
func storeOrder(values []*Value, sset *sparseSet, storeNumber []int32) []*Value {
	if len(values) == 0 {	// 没有value可以进行排序
		return values
	}

	f := values[0].Block.Func

	// find all stores

	// Members of values that are store values.
	// A constant bound allows this to be stack-allocated. 64 is
	// enough to cover almost every storeOrder call.
	stores := make([]*Value, 0, 64)	// 存储除了最后一个外所有Memory类型的value
	hasNilCheck := false	// 记录values中是否有nilcheck的value
	sset.clear() // sset is the set of stores that are used in other values		存储除了最后一个以及OpInitMem与OpPhi以外的所有Memory类型的value的id
	for _, v := range values {
		if v.Type.IsMemory() {
			stores = append(stores, v)
			if v.Op == OpInitMem || v.Op == OpPhi {
				continue
			}
			sset.add(v.MemoryArg().ID) // record that v's memory arg is used
		}
		if v.Op == OpNilCheck {
			hasNilCheck = true
		}
	}
	if len(stores) == 0 || !hasNilCheck && f.pass.name == "nilcheckelim" {	// 没有影响内存的操作或者nilcheckelim的pass中没有nilcheck
		// there is no store, the order does not matter
		return values
	}

	// find last store, which is the one that is not used by other stores
	var last *Value
	for _, v := range stores {	// store中存储的memory参数都是上一个memory参数,所以store不会保存最后一个memory参数,这个循环应该是想找到最后的那一个memory变量
		if !sset.contains(v.ID) {
			if last != nil {
				f.Fatalf("two stores live simultaneously: %v and %v", v, last)
			}
			last = v
		}
	}

	// We assign a store number to each value. Store number is the
	// index of the latest store that this value transitively depends.
	// The i-th store in the current block gets store number 3*i. A nil
	// check that depends on the i-th store gets store number 3*i+1.
	// Other values that depends on the i-th store gets store number 3*i+2.
	// Special case: 0 -- unassigned, 1 or 2 -- the latest store it depends
	// is in the previous block (or no store at all, e.g. value is Const).
	// First we assign the number to all stores by walking back the store chain,
	// then assign the number to other values in DFS order.
	count := make([]int32, 3*(len(stores)+1))	// 记录storeNumber的出现次数
	sset.clear() // reuse sparse set to ensure that a value is pushed to stack only once
	for n, w := len(stores), last; n > 0; n-- {	// 这个循环将所有的memory变量与其storeNumber保存在storeNumber数组中
		storeNumber[w.ID] = int32(3 * n)
		count[3*n]++	// 标记一个storeNumber
		sset.add(w.ID)	// 标记w已处理
		if w.Op == OpInitMem || w.Op == OpPhi {
			if n != 1 {
				f.Fatalf("store order is wrong: there are stores before %v", w)
			}
			break
		}
		w = w.MemoryArg()	// 继续处理上一个memory变量
	}
	var stack []*Value
	for _, v := range values {	// 遍历一个块中的所有values
		if sset.contains(v.ID) {
			// in sset means v is a store, or already pushed to stack, or already assigned a store number
			continue
		}
		stack = append(stack, v)	// 将value添加进stack
		sset.add(v.ID)	// 标记v已经处理了

		for len(stack) > 0 {
			w := stack[len(stack)-1]	// 获取最后一项
			if storeNumber[w.ID] != 0 {	// 处理过w
				stack = stack[:len(stack)-1]	// 弹栈
				continue
			}
			if w.Op == OpPhi {
				// Phi value doesn't depend on store in the current block.
				// Do this early to avoid dependency cycle.
				storeNumber[w.ID] = 2
				count[2]++
				stack = stack[:len(stack)-1]
				continue
			}

			max := int32(0) // latest store dependency
			argsdone := true	// 该值为false表示value存在某个在相同块中的value Arg仍未被处理
			for _, a := range w.Args {	// 遍历非Memory value的所有Args
				if a.Block != w.Block {	// 这行意在找到在当前块中使用的value参数
					continue
				}
				if !sset.contains(a.ID) {	// 将Arg添加进stack中继续遍历
					stack = append(stack, a)
					sset.add(a.ID)
					argsdone = false
					break
				}
				// 到这一步表示a已经有了storeNumber
				if storeNumber[a.ID]/3 > max {
					max = storeNumber[a.ID] / 3
				}
			}
			if !argsdone {	// 仍有Arg未处理就先处理Arg,这属于深度优先遍历
				continue
			}

			n := 3*max + 2	// 最近的store的storeNumber+2
			if w.Op == OpNilCheck {
				n = 3*max + 1
			}
			storeNumber[w.ID] = n	// 为w赋予storeNumber
			count[n]++
			stack = stack[:len(stack)-1]	// 弹栈
		}
	}

	// convert count to prefix sum of counts: count'[i] = sum_{j<=i} count[i]
	for i := range count {	// 计算count数组的前缀和
		if i == 0 {
			continue
		}
		count[i] += count[i-1]
	}
	if count[len(count)-1] != int32(len(values)) {
		f.Fatalf("storeOrder: value is missing, total count = %d, values = %v", count[len(count)-1], values)
	}

	// place values in count-indexed bins, which are in the desired store order
	order := make([]*Value, len(values))
	for _, v := range values {	// 遍历values
		s := storeNumber[v.ID]	// 获取value的storeNumber
		order[count[s-1]] = v	// 在order的count[s-1]处存储v
		count[s-1]++	// count[s-1]自增一,上一行代码就会放到下一个位置
	}

	// Order nil checks in source order. We want the first in source order to trigger.
	// If two are on the same line, we don't really care which happens first.
	// See issue 18169.
	if hasNilCheck {	// 对多个OpNilCheck之间的values通过pos进行排序
		start := -1	// 标记第一个OpNilCheck在order中的索引
		for i, v := range order {	// 这个for循环将连续的OpNilCheck根据在源码中出现的先后顺序进行排序
			if v.Op == OpNilCheck {
				if start == -1 {
					start = i
				}
			} else {
				if start != -1 {
					sort.Sort(bySourcePos(order[start:i]))	// 对两个OpNilCheck之间的values通过pos进行排序
					start = -1
				}
			}
		}
		if start != -1 {
			sort.Sort(bySourcePos(order[start:]))
		}
	}

	return order
}

type bySourcePos []*Value

func (s bySourcePos) Len() int           { return len(s) }
func (s bySourcePos) Swap(i, j int)      { s[i], s[j] = s[j], s[i] }
func (s bySourcePos) Less(i, j int) bool { return s[i].Pos.Before(s[j].Pos) }

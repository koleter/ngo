// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import (
	"cmd/compile/internal/ssa"
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"container/heap"
	"fmt"
)

// This file contains the algorithm to place phi nodes in a function.
// For small functions, we use Braun, Buchwald, Hack, Leißa, Mallon, and Zwinkau.
// https://pp.info.uni-karlsruhe.de/uploads/publikationen/braun13cc.pdf
// For large functions, we use Sreedhar & Gao: A Linear Time Algorithm for Placing Φ-Nodes.
// http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.8.1979&rep=rep1&type=pdf

const smallBlocks = 500

const debugPhi = false

// insertPhis finds all the places in the function where a phi is
// necessary and inserts them.
// Uses FwdRef ops to find all uses of variables, and s.defvars to find
// all definitions.
// Phi values are inserted, and all FwdRefs are changed to a Copy
// of the appropriate phi or definition.
// TODO: make this part of cmd/compile/internal/ssa somehow?
func (s *state) insertPhis() {
	if len(s.f.Blocks) <= smallBlocks {
		sps := simplePhiState{s: s, f: s.f, defvars: s.defvars}
		sps.insertPhis()
		return
	}
	ps := phiState{s: s, f: s.f, defvars: s.defvars}
	ps.insertPhis()
}

type phiState struct {
	s       *state                 // SSA state
	f       *ssa.Func              // function to work on
	defvars []map[*Node]*ssa.Value // defined variables at end of each block	每个块中节点定义的变量与value的映射

	varnum map[*Node]int32 // variable numbering

	// properties of the dominator tree
	idom  []*ssa.Block // dominator parents
	tree  []domBlock   // dominator child+sibling
	level []int32      // level in dominator tree (0 = root or unreachable, 1 = children of root, ...)	被支配的节点等级值大

	// scratch locations
	priq   blockHeap    // priority queue of blocks, higher level (toward leaves) = higher priority
	q      []*ssa.Block // inner loop queue
	queued *sparseSet   // has been put in q
	hasPhi *sparseSet   // has a phi
	hasDef *sparseSet   // has a write of the variable we're processing

	// miscellaneous
	placeholder *ssa.Value // dummy value to use as a "not set yet" placeholder.
}

/*
当前块使用了唯一的前驱块中定义的变量,可以认为是直接复制
*/
func (s *phiState) insertPhis() {
	if debugPhi {
		fmt.Println(s.f.String())
	}

	// Find all the variables for which we need to match up reads & writes.
	// This step prunes any basic-block-only variables from consideration.
	// Generate a numbering for these variables.
	s.varnum = map[*Node]int32{} // Node节点与vars和vartypes的相关index
	var vars []*Node             // 存储要生成phi函数的节点
	var vartypes []*types.Type   // 对应vars变量,存储变量的类型
	for _, b := range s.f.Blocks {
		for _, v := range b.Values {
			if v.Op != ssa.OpFwdRef { // 遍历所有的values并找到OpFwdRef
				continue
			}
			var_ := v.Aux.(*Node) // OpFwdRef所对应的Node节点

			// Optimization: look back 1 block for the definition.
			if len(b.Preds) == 1 { // 只有一个前驱块
				c := b.Preds[0].Block()                   // 获取唯一的前驱块
				if w := s.defvars[c.ID][var_]; w != nil { // 变量是在这个唯一的前驱块中定义的
					v.Op = ssa.OpCopy // 所以其实就是类似于对上一个块中变量直接的拷贝,其他的情况在下面通过支配节点设置
					v.Aux = nil
					v.AddArg(w)
					continue
				}
			}

			if _, ok := s.varnum[var_]; ok { // 已遍历过节点
				continue
			}
			s.varnum[var_] = int32(len(vartypes)) // Node节点的索引
			if debugPhi {
				fmt.Printf("var%d = %v\n", len(vartypes), var_)
			}
			vars = append(vars, var_) // 存储以待查找Node节点的定义处
			vartypes = append(vartypes, v.Type)
		}
	}

	if len(vartypes) == 0 { // 不需要phi函数
		return
	}

	// Find all definitions of the variables we need to process.
	// defs[n] contains all the blocks in which variable number n is assigned.
	defs := make([][]*ssa.Block, len(vartypes)) // 变量下标对应着一个block数组,记录一个变量在哪些块中被定义了
	for _, b := range s.f.Blocks {
		for var_ := range s.defvars[b.ID] { // TODO: encode defvars some other way (explicit ops)? make defvars[n] a slice instead of a map.
			if n, ok := s.varnum[var_]; ok {
				defs[n] = append(defs[n], b)
			}
		}
	}

	// Make dominator tree.
	s.idom = s.f.Idom()
	s.tree = make([]domBlock, s.f.NumBlocks())
	for _, b := range s.f.Blocks {
		p := s.idom[b.ID] // 获取b的支配节点
		if p != nil {
			s.tree[b.ID].sibling = s.tree[p.ID].firstChild
			s.tree[p.ID].firstChild = b
		}
	}
	// Compute levels in dominator tree.
	// With parent pointers we can do a depth-first walk without
	// any auxiliary storage.
	s.level = make([]int32, s.f.NumBlocks()) // 块ID与支配级别的映射
	b := s.f.Entry
levels:
	for {
		if p := s.idom[b.ID]; p != nil { // 获取块b的支配节点p
			s.level[b.ID] = s.level[p.ID] + 1 // 记录支配等级,被支配的节点等级高
			if debugPhi {
				fmt.Printf("level %s = %d\n", b, s.level[b.ID])
			}
		}
		if c := s.tree[b.ID].firstChild; c != nil { // 获取b的第一个子节点并将c赋给b继续循环
			b = c // 深度搜索
			continue
		}
		// 到这一行必定是b没有子节点了
		for {
			if c := s.tree[b.ID].sibling; c != nil { // 取出b的兄弟节点
				b = c
				continue levels
			}
			b = s.idom[b.ID] // 返回上一个支配节点
			if b == nil {    // b是entry节点就退出大循环
				break levels
			}
		}
	}

	// Allocate scratch locations.
	s.priq.level = s.level
	s.q = make([]*ssa.Block, 0, s.f.NumBlocks())
	s.queued = newSparseSet(s.f.NumBlocks())
	s.hasPhi = newSparseSet(s.f.NumBlocks())
	s.hasDef = newSparseSet(s.f.NumBlocks())
	s.placeholder = s.s.entryNewValue0(ssa.OpUnknown, types.TypeInvalid)

	// Generate phi ops for each variable.
	for n := range vartypes {
		s.insertVarPhis(n, vars[n], defs[n], vartypes[n]) // 添加phi函数
	}

	// Resolve FwdRefs to the correct write or phi.
	s.resolveFwdRefs()

	// Erase variable numbers stored in AuxInt fields of phi ops. They are no longer needed.
	for _, b := range s.f.Blocks {
		for _, v := range b.Values {
			if v.Op == ssa.OpPhi {
				v.AuxInt = 0
			}
		}
	}
}

// n代表index, var_代表一个块中使用了的别的块的节点变量,defs代表var_节点在哪些块中定义过,typ代表phi函数的类型
func (s *phiState) insertVarPhis(n int, var_ *Node, defs []*ssa.Block, typ *types.Type) {
	priq := &s.priq
	q := s.q
	queued := s.queued // 用于确认某个块是否在q中,这里存储的是块的ID
	queued.clear()
	hasPhi := s.hasPhi // 存储有phi函数的块ID
	hasPhi.clear()
	hasDef := s.hasDef // 定义了变量的块ID
	hasDef.clear()

	// Add defining blocks to priority queue.
	for _, b := range defs {
		priq.a = append(priq.a, b) // 将定义过变量的块添加到优先队列中
		hasDef.add(b.ID)
		if debugPhi {
			fmt.Printf("def of var%d in %s\n", n, b)
		}
	}
	heap.Init(priq) // 对priq.a进行排序,块ID的级别大的排在前面

	// Visit blocks defining variable n, from deepest to shallowest.
	for len(priq.a) > 0 { // 还存在未遍历的定义过的变量
		currentRoot := heap.Pop(priq).(*ssa.Block) // 从priq.a中弹出最后一项,这个是定义了变量的块

		if debugPhi {
			fmt.Printf("currentRoot %s\n", currentRoot)
		}
		// Walk subtree below definition.
		// Skip subtrees we've done in previous iterations.
		// Find edges exiting tree dominated by definition (the dominance frontier).
		// Insert phis at target blocks.
		if queued.contains(currentRoot.ID) {
			s.s.Fatalf("root already in queue")
		}
		q = append(q, currentRoot)
		for len(q) > 0 { // 遍历从currentRoot开始的支配树
			b := q[len(q)-1] // 从q中弹出一项
			q = q[:len(q)-1]
			if debugPhi {
				fmt.Printf("  processing %s\n", b)
			}

			currentRootLevel := s.level[currentRoot.ID] // 获取支配等级
			// 遍历currentRoot所支配的所有块(不仅仅遍历直接支配的节点)
			for _, e := range b.Succs { // 遍历后继边
				c := e.Block() // currentRoot是定义了变量的块,获取后继块,这里的c是currentRoot的后继,也可能是后继的后继,也可能是后继的后继的后继.....
				// TODO: if the variable is dead at c, skip it.
				if s.level[c.ID] > currentRootLevel {
					// a D-edge, or an edge whose target is in currentRoot's subtree.
					continue
				}
				// b的后继块的支配等级小于currentRoot的支配等级,说明currentRoot应该是在一个以c块开始的循环中,要在c块中添加phi函数
				/*
					b的后继块的支配等级等于currentRoot的支配等级
					           if(a块)
					          /     \
					true分支(b块)     false分支(c块)
					           \    /
					             d块
					这种情况下b,c,d块的最近支配节点都是a且这三个块的支配等级相同,也会进到这里,这时可能是b找到后继块d,也可能是c找到后继块d
					d块有多个分支时这些分支都不是d的最近支配节点,所以如果这些分支中如果定义了d中使用的变量的话,它们的支配等级是相同的,应该在d中添加phi
				*/
				if hasPhi.contains(c.ID) {
					continue
				}
				// Add a phi to block c for variable n.
				hasPhi.add(c.ID)
				v := c.NewValue0I(currentRoot.Pos, ssa.OpPhi, typ, int64(n)) // TODO: line number right?
				// Note: we store the variable number in the phi's AuxInt field. Used temporarily by phi building.
				s.s.addNamedValue(var_, v)
				for range c.Preds { // 添加c的前驱数量的phi参数
					v.AddArg(s.placeholder) // Actual args will be filled in by resolveFwdRefs.
				}
				if debugPhi {
					fmt.Printf("new phi for var%d in %s: %s\n", n, c, v)
				}
				if !hasDef.contains(c.ID) { // c块中没有定义变量,那么将c添加到优先队列中继续循环
					// There's now a new definition of this variable in block c.
					// Add it to the priority queue to explore.
					heap.Push(priq, c) // 将带有phi函数的块c添加到priq中
					hasDef.add(c.ID)
				}
			}

			// Visit children if they have not been visited yet.
			for c := s.tree[b.ID].firstChild; c != nil; c = s.tree[c.ID].sibling { // 把b所支配的所有未访问过的节点添加到q中,这一步就可以通过currentRoot遍历所有的被支配节点而不是仅仅处理直接支配节点
				if !queued.contains(c.ID) {
					q = append(q, c) // 添加到q中继续找循环中可以插入的phi
					queued.add(c.ID)
				}
			}
		}
	}
}

// resolveFwdRefs links all FwdRef uses up to their nearest dominating definition.
func (s *phiState) resolveFwdRefs() {
	// Do a depth-firs、minator tree, keeping track
	// of the most-recently-seen value for each variable.

	// Map from variable ID to SSA value at the current point of the walk.
	values := make([]*ssa.Value, len(s.varnum))
	for i := range values {
		values[i] = s.placeholder
	}

	// Stack of work to do.
	type stackEntry struct {
		b *ssa.Block // block to explore

		// variable/value pair to reinstate on exit
		n int32 // variable ID
		v *ssa.Value

		// Note: only one of b or n,v will be set.
	}
	var stk []stackEntry

	stk = append(stk, stackEntry{b: s.f.Entry}) // 从entry块开始遍历
	for len(stk) > 0 {                          // 深度优先遍历
		work := stk[len(stk)-1]
		stk = stk[:len(stk)-1]

		b := work.b   // 获取当前处理的块
		if b == nil { // 处理过,回退
			// On exit from a block, this case will undo any assignments done below.
			values[work.n] = work.v
			continue
		}

		// Process phis as new defs. They come before FwdRefs in this block.
		for _, v := range b.Values { // 对于b块的所有phi函数,暂时记录变量对应的Value为这个phi函数
			if v.Op != ssa.OpPhi {
				continue
			}
			n := int32(v.AuxInt) // 获取phi函数的索引
			// Remember the old assignment so we can undo it when we exit b.
			stk = append(stk, stackEntry{n: n, v: values[n]}) // b为nil,重复遍历时会执行上面的undo操作,这里的v保存之前的values[n]
			// Record the new assignment.
			values[n] = v // 记录values中索引为n的项为v
		}

		// Replace a FwdRef op with the current incoming value for its variable.
		/*
								if块
			                   /  \
			             true分支   false分支
			如果if的两个分支中使用了if块中定义的变量的话,在insertPhi函数中是不会将OpFwdRef替换为phi的
		*/
		for _, v := range b.Values { // 遍历其中的OpFwdRef并替换为OpCopy
			if v.Op != ssa.OpFwdRef {
				continue
			}
			n := s.varnum[v.Aux.(*Node)] // 通过节点获取变量的varnum
			v.Op = ssa.OpCopy
			v.Aux = nil
			v.AddArg(values[n]) // 当前变量的值
		}

		// Establish values for variables defined in b.
		for var_, v := range s.defvars[b.ID] { // 对于b块中定义的变量以及对应的Value,暂时记录变量对应该Value
			n, ok := s.varnum[var_] // 获取变量ID
			if !ok {
				// some variable not live across a basic block boundary.
				continue
			}
			// Remember the old assignment so we can undo it when we exit b.
			stk = append(stk, stackEntry{n: n, v: values[n]})
			// Record the new assignment.
			values[n] = v // 记录第n个变量为phi函数v
		}

		// Replace phi args in successors with the current incoming value.
		for _, e := range b.Succs { // 这个循环替换后继块中phi函数的参数
			c, i := e.Block(), e.Index()              // 后继块, 后继块的第i个前驱是b块
			for j := len(c.Values) - 1; j >= 0; j-- { // 倒序遍历后继块中的所有Values
				v := c.Values[j] // 获取块中的Value
				if v.Op != ssa.OpPhi {
					break // All phis will be at the end of the block during phi building.
				}
				// Only set arguments that have been resolved.
				// For very wide CFGs, this significantly speeds up phi resolution.
				// See golang.org/issue/8225.
				if w := values[v.AuxInt]; w.Op != ssa.OpUnknown { // 获取最近支配节点中变量的值并设置为phi函数的参数
					v.SetArg(i, w) // 设置phi的第i个变量为w(与前驱的索引一致)
				}
			}
		}

		// Walk children in dominator tree.
		for c := s.tree[b.ID].firstChild; c != nil; c = s.tree[c.ID].sibling { // b的所有直接支配节点添加到队列继续进行遍历
			stk = append(stk, stackEntry{b: c})
		}
	}
}

// domBlock contains Extra per-block information to record the dominator tree.
type domBlock struct {
	firstChild *ssa.Block // first child of block in dominator tree		当前节点是哪个节点的最近支配节点
	sibling    *ssa.Block // next child of parent in dominator tree		有相同的最近支配节点的该节点的兄弟节点
}

// A block heap is used as a priority queue to implement the PiggyBank
// from Sreedhar and Gao.  That paper uses an array which is better
// asymptotically but worse in the common case when the PiggyBank
// holds a sparse set of blocks.
type blockHeap struct {
	a     []*ssa.Block // block IDs in heap
	level []int32      // depth in dominator tree (static, used for determining priority)
}

func (h *blockHeap) Len() int      { return len(h.a) }
func (h *blockHeap) Swap(i, j int) { a := h.a; a[i], a[j] = a[j], a[i] }

func (h *blockHeap) Push(x interface{}) {
	v := x.(*ssa.Block)
	h.a = append(h.a, v)
}

// 弹出数组最后一项
func (h *blockHeap) Pop() interface{} {
	old := h.a
	n := len(old)
	x := old[n-1] // 取了最后一项
	h.a = old[:n-1]
	return x // 返回最后一项
}
func (h *blockHeap) Less(i, j int) bool {
	return h.level[h.a[i].ID] > h.level[h.a[j].ID] // 块ID的级别大的排在前面
}

// TODO: stop walking the iterated domininance frontier when
// the variable is dead. Maybe detect that by checking if the
// node we're on is reverse dominated by all the reads?
// Reverse dominated by the highest common successor of all the reads?

// copy of ../ssa/sparseset.go
// TODO: move this file to ../ssa, then use sparseSet there.
type sparseSet struct {
	dense  []ssa.ID
	sparse []int32
}

// newSparseSet returns a sparseSet that can represent
// integers between 0 and n-1
func newSparseSet(n int) *sparseSet {
	return &sparseSet{dense: nil, sparse: make([]int32, n)}
}

func (s *sparseSet) contains(x ssa.ID) bool {
	i := s.sparse[x]
	return i < int32(len(s.dense)) && s.dense[i] == x
}

func (s *sparseSet) add(x ssa.ID) {
	i := s.sparse[x]
	if i < int32(len(s.dense)) && s.dense[i] == x {
		return
	}
	s.dense = append(s.dense, x)
	s.sparse[x] = int32(len(s.dense)) - 1
}

func (s *sparseSet) clear() {
	s.dense = s.dense[:0]
}

// Variant to use for small functions.
type simplePhiState struct {
	s         *state                 // SSA state
	f         *ssa.Func              // function to work on
	fwdrefs   []*ssa.Value           // list of FwdRefs to be processed
	defvars   []map[*Node]*ssa.Value // defined variables at end of each block		索引为块ID
	reachable []bool                 // which blocks are reachable
}

func (s *simplePhiState) insertPhis() {
	s.reachable = ssa.ReachableBlocks(s.f) // 找到所有可以到达的块

	// Find FwdRef ops.
	for _, b := range s.f.Blocks {
		for _, v := range b.Values {
			if v.Op != ssa.OpFwdRef {
				continue
			}
			s.fwdrefs = append(s.fwdrefs, v) // 将被使用的变量添加到s.fwdrefs中
			var_ := v.Aux.(*Node)            // 获取该变量对应的Node节点
			if _, ok := s.defvars[b.ID][var_]; !ok {
				s.defvars[b.ID][var_] = v // treat FwdDefs as definitions.
			}
		}
	}

	var args []*ssa.Value

loop:
	for len(s.fwdrefs) > 0 {
		v := s.fwdrefs[len(s.fwdrefs)-1] // 弹出一项, v是在当前块中使用的变量
		s.fwdrefs = s.fwdrefs[:len(s.fwdrefs)-1]
		b := v.Block          // 获取对应的Block
		var_ := v.Aux.(*Node) // 使用的变量对应的Node节点
		if b == s.f.Entry {
			// No variable should be live at entry.
			s.s.Fatalf("Value live at entry. It shouldn't be. func %s, node %v, value %v", s.f.Name, var_, v)
		}
		if !s.reachable[b.ID] {
			// This block is dead.
			// It doesn't matter what we use here as long as it is well-formed.
			v.Op = ssa.OpUnknown
			v.Aux = nil
			continue
		}
		// Find variable value on each predecessor.
		args = args[:0]             // 存储OpFwdRef变量
		for _, e := range b.Preds { // 遍历所有前驱块,找到所有的前驱块中对于v的定义保存到args中
			args = append(args, s.lookupVarOutgoing(e.Block(), v.Type, var_, v.Pos))
		}

		// Decide if we need a phi or not. We need a phi if there
		// are two different args (which are both not v).
		var w *ssa.Value
		for _, a := range args {
			if a == v {
				continue // self-reference
			}
			if a == w {
				continue // already have this witness
			}
			if w != nil {
				// two witnesses, need a phi value
				v.Op = ssa.OpPhi
				v.AddArgs(args...)
				v.Aux = nil
				continue loop
			}
			w = a // save witness
		}
		if w == nil {
			s.s.Fatalf("no witness for reachable phi %s", v)
		}
		// One witness. Make v a copy of w.
		v.Op = ssa.OpCopy
		v.Aux = nil
		v.AddArg(w)
	}
}

// lookupVarOutgoing finds the variable's value at the end of block b.
func (s *simplePhiState) lookupVarOutgoing(b *ssa.Block, t *types.Type, var_ *Node, line src.XPos) *ssa.Value {
	for {
		if v := s.defvars[b.ID][var_]; v != nil { // // The variable is defined by b
			return v
		}
		// The variable is not defined by b and we haven't looked it up yet.
		// If b has exactly one predecessor, loop to look it up there.
		// Otherwise, give up and insert a new FwdRef and resolve it later.
		if len(b.Preds) != 1 { // 存在多个前驱就跳出循环
			break
		}
		b = b.Preds[0].Block()  // 获取唯一的前驱块继续循环
		if !s.reachable[b.ID] { // 前驱块不能抵达就跳出循环
			// This is rare; it happens with oddly interleaved infinite loops in dead code.
			// See issue 19783.
			break
		}
	}
	// Generate a FwdRef for the variable and return that.
	v := b.NewValue0A(line, ssa.OpFwdRef, t, var_) // 表示在该块使用了该变量
	s.defvars[b.ID][var_] = v
	s.s.addNamedValue(var_, v)
	s.fwdrefs = append(s.fwdrefs, v)
	return v
}

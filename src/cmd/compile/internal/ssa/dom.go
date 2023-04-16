// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// This file contains code to compute the dominator tree
// of a control-flow graph.

// postorder computes a postorder traversal ordering for the
// basic blocks in f. Unreachable blocks will not appear.
func postorder(f *Func) []*Block {
	return postorderWithNumbering(f, nil)
}

type blockAndIndex struct {
	b     *Block
	index int // index is the number of successor edges of b that have already been explored.
}

// postorderWithNumbering provides a DFS postordering.
// This seems to make loop-finding more robust.
func postorderWithNumbering(f *Func, ponums []int32) []*Block {
	seen := make([]bool, f.NumBlocks())

	// result ordering
	order := make([]*Block, 0, len(f.Blocks))

	// stack of blocks and next child to visit
	// A constant bound allows this to be stack-allocated. 32 is
	// enough to cover almost every postorderWithNumbering call.
	s := make([]blockAndIndex, 0, 32)
	s = append(s, blockAndIndex{b: f.Entry}) // 第一个放入entry块
	seen[f.Entry.ID] = true
	for len(s) > 0 {
		tos := len(s) - 1
		x := s[tos] // 取出s中的最后一项
		b := x.b    // 获取块
		if i := x.index; i < len(b.Succs) {
			s[tos].index++           // 将s的最后一项的index加1,以便下次遍历b的下一个后继
			bb := b.Succs[i].Block() // 获取第i个后继块
			if !seen[bb.ID] {
				seen[bb.ID] = true
				s = append(s, blockAndIndex{b: bb})
			}
			continue
		}
		s = s[:tos] // 弹出最后一项
		if ponums != nil {
			ponums[b.ID] = int32(len(order)) // 块ID对应返回数组中的index
		}
		order = append(order, b) // 处理完当前块的所有后继块后再将当前块放到返回数组中
	}
	return order
}

type linkedBlocks func(*Block) []Edge

const nscratchslices = 7

// experimentally, functions with 512 or fewer blocks account
// for 75% of memory (size) allocation for dominator computation
// in make.bash.
const minscratchblocks = 512

func (cache *Cache) scratchBlocksForDom(maxBlockID int) (a, b, c, d, e, f, g []ID) {
	tot := maxBlockID * nscratchslices
	scratch := cache.domblockstore
	if len(scratch) < tot {
		// req = min(1.5*tot, nscratchslices*minscratchblocks)
		// 50% padding allows for graph growth in later phases.
		req := (tot * 3) >> 1
		if req < nscratchslices*minscratchblocks {
			req = nscratchslices * minscratchblocks
		}
		scratch = make([]ID, req)
		cache.domblockstore = scratch
	} else {
		// Clear as much of scratch as we will (re)use
		scratch = scratch[0:tot]
		for i := range scratch {
			scratch[i] = 0
		}
	}

	a = scratch[0*maxBlockID : 1*maxBlockID]
	b = scratch[1*maxBlockID : 2*maxBlockID]
	c = scratch[2*maxBlockID : 3*maxBlockID]
	d = scratch[3*maxBlockID : 4*maxBlockID]
	e = scratch[4*maxBlockID : 5*maxBlockID]
	f = scratch[5*maxBlockID : 6*maxBlockID]
	g = scratch[6*maxBlockID : 7*maxBlockID]

	return
}

func dominators(f *Func) []*Block {
	preds := func(b *Block) []Edge { return b.Preds }
	succs := func(b *Block) []Edge { return b.Succs }

	//TODO: benchmark and try to find criteria for swapping between
	// dominatorsSimple and dominatorsLT
	return f.dominatorsLTOrig(f.Entry, preds, succs)
}

// dominatorsLTOrig runs Lengauer-Tarjan to compute a dominator tree starting at
// entry and using predFn/succFn to find predecessors/successors to allow
// computing both dominator and post-dominator trees.
func (f *Func) dominatorsLTOrig(entry *Block, predFn linkedBlocks, succFn linkedBlocks) []*Block {
	// Adapted directly from the original TOPLAS article's "simple" algorithm

	maxBlockID := entry.Func.NumBlocks()
	/*
		semi记录块的ID与半必经节点的深度优先顺序号的映射		所有祖先节点中拥有最小深度序号的祖先id
		vertex记录深度优先顺序号与块ID的映射
		label记录块ID与这个块的所有非根祖先块中拥有最低深度优先顺序号的块的ID
		parent表示一个块的父节点是哪个块,父节点的深度序号必定小于子节点,parent中记录的是这两个块的ID
	*/
	semi, vertex, label, parent, ancestor, bucketHead, bucketLink := f.Cache.scratchBlocksForDom(maxBlockID)

	// This version uses integers for most of the computation,
	// to make the work arrays smaller and pointer-free.
	// fromID translates from ID to *Block where that is needed.
	fromID := make([]*Block, maxBlockID) // 记录块的Id与块的映射
	for _, v := range f.Blocks {
		fromID[v.ID] = v
	}
	idom := make([]*Block, maxBlockID) // 记录value的最近支配块

	// Step 1. Carry out a depth first search of the problem graph. Number
	// the vertices from 1 to n as they are reached during the search.
	n := f.dfsOrig(entry, succFn, semi, vertex, label, parent) // n代表深度遍历序号的最大值,从1开始,该函数运行完毕后semi代表一个块的ID到深度遍历序号的映射

	for i := n; i >= 2; i-- { // 倒序,从树的底部开始向上遍历,根节点不必遍历,因为根节点支配全场,此为回溯阶段
		blockID := vertex[i] // 通过深度优先顺序号获取块ID

		// step2 in TOPLAS paper	这个循环遍历当前块的所有前驱块并找到顺序号最小的那个记录到semi[blockID]中
		for _, edge := range predFn(fromID[blockID]) { // 遍历ID为blockID的每一条前驱组成的边   predFn(b)返回b.Preds
			predBlock := edge.b          // 获取边对应的前驱块
			if semi[predBlock.ID] == 0 { // v未遍历过,表示这个块无法到达
				// skip unreachable predecessor
				// not in original, but we're using existing pred instead of building one.
				continue
			}
			u := evalOrig(predBlock.ID, ancestor, semi, label) // 依据所有前驱块找到所有前驱块中的具有最小顺序号的祖先块ID
			if semi[u] < semi[blockID] {  // 对比前驱块的祖先与当前块的所有祖先的最小深度序号,当前块的深度序号保存为最小的那个
				semi[blockID] = semi[u]
			}
		}

		// add blockID to bucket[vertex[semi[blockID]]]
		// implement bucket as a linked list implemented
		// in a pair of arrays.		bucketHead可以理解为以某个blockID为根,其下所有的联通环组成的链表
		vsw := vertex[semi[blockID]]          // 获取当前处理的节点所找到的最小顺序号的祖先节点ID
		bucketLink[blockID] = bucketHead[vsw] // 与bucketHead互相作用,相当于头结点之后的结点	这两行代码相当于链表头插一个节点	双数组实现的链表
		bucketHead[vsw] = blockID             // 最小顺序号的祖先节点ID与当前块ID的映射,记录一个链表的头结点,表示节点vsw是当前块的父节点

		linkOrig(parent[blockID], blockID, ancestor) // ancestor[blockID] = parentID[blockID]

		// step3 in TOPLAS paper	下面的循环从父节点的所有子节点,v为0时表示父节点不是最小顺序号的祖先节点
		for v := bucketHead[parent[blockID]]; v != 0; v = bucketLink[v] {
			u := evalOrig(v, ancestor, semi, label) // 找到节点的具有最小顺序号的祖先块ID,
			if semi[u] < semi[v] {                  // 随着树的遍历,找到了对于v来说深度序号更小的祖先
				idom[v] = fromID[u] // v的最近支配节点设置为最小深度序号祖先的节点
			} else { // semi[u] == semi[v],这种情况下表示父节点还没有指定父节点,设置父节点为当前节点的待定支配点
				idom[v] = fromID[parent[blockID]]
			}
		}
	}
	// step 4 in toplas paper	下面的循环解决半必经节点存在旁路的问题
	for i := ID(2); i <= n; i++ { // 忽略根节点,遍历其后的所有节点
		w := vertex[i]                     // 依据顺序号获取blockID
		if idom[w].ID != vertex[semi[w]] { // 当前记录的支配节点不等于w的最小深度序号的节点
			idom[w] = idom[idom[w].ID]
		}
	}

	return idom
}

// dfs performs a depth first search over the blocks starting at entry block
// (in arbitrary order).  This is a de-recursed version of dfs from the
// original Tarjan-Lengauer TOPLAS article.  It's important to return the
// same values for parentID as the original algorithm.
func (f *Func) dfsOrig(entry *Block, succFn linkedBlocks, semi, vertex, label, parent []ID) ID {
	n := ID(0)
	s := make([]*Block, 0, 256)
	s = append(s, entry) // 从entry块开始

	for len(s) > 0 {
		v := s[len(s)-1] // 从s中弹出一个block
		s = s[:len(s)-1]
		// recursing on v

		if semi[v.ID] != 0 {
			continue // already visited
		}
		n++
		semi[v.ID] = n   // 为块的ID进行编号,相当于记录访问顺序
		vertex[n] = v.ID // 通过访问顺序获取块ID
		label[v.ID] = v.ID
		// ancestor[v] already zero
		for _, e := range succFn(v) { // 遍历后继块
			w := e.b // 后继块
			// if it has a dfnum, we've already visited it
			if semi[w.ID] == 0 { // 未遍历到的后继块
				// yes, w can be pushed multiple times.
				s = append(s, w)
				parent[w.ID] = v.ID // keep overwriting this till it is visited.    通过两个块的ID记录某个块的前驱块
			}
		}
	}
	return n
}

// semi记录块的ID与深度优先顺序号的映射, 存放半必经节点, label记录块ID与这个块的所有非根祖先块中拥有最低深度优先顺序号的块的ID的映射
// compressOrig is the "simple" compress function from LT paper
func compressOrig(blockID ID, ancestor, semi, label []ID) {
	if ancestor[ancestor[blockID]] != 0 { // 祖先存在祖先节点,可以进行路径压缩
		compressOrig(ancestor[blockID], ancestor, semi, label)     // 递归祖先节点,尝试对祖先节点进行路径压缩
		if semi[label[ancestor[blockID]]] < semi[label[blockID]] { // 祖先节点的深度序号小于blockID的序号
			label[blockID] = label[ancestor[blockID]] // 设置v的最小序号的祖先块ID为祖先的最小序号的祖先块ID
		}
		ancestor[blockID] = ancestor[ancestor[blockID]] // 设置v的祖先为v的祖先的祖先,这里相当于路径压缩,追根溯源找到祖先节点
	}
}

// evalOrig is the "simple" eval function from LT paper
func evalOrig(blockID ID, ancestor, semi, label []ID) ID {
	if ancestor[blockID] == 0 { // 无记录的祖先节点,不必进行路径压缩,直接返回blockID
		return blockID
	}
	compressOrig(blockID, ancestor, semi, label)
	return label[blockID] // 返回最小序号的祖先块ID
}

func linkOrig(v, w ID, ancestor []ID) {
	ancestor[w] = v
}

// dominators computes the dominator tree for f. It returns a slice
// which maps block ID to the immediate dominator of that block.
// Unreachable blocks map to nil. The entry block maps to nil.
func dominatorsSimple(f *Func) []*Block {
	// A simple algorithm for now
	// Cooper, Harvey, Kennedy
	idom := make([]*Block, f.NumBlocks())

	// Compute postorder walk
	post := f.postorder()

	// Make map from block id to order index (for intersect call)
	postnum := make([]int, f.NumBlocks())
	for i, b := range post {
		postnum[b.ID] = i
	}

	// Make the entry block a self-loop
	idom[f.Entry.ID] = f.Entry
	if postnum[f.Entry.ID] != len(post)-1 {
		f.Fatalf("entry block %v not last in postorder", f.Entry)
	}

	// Compute relaxation of idom entries
	for {
		changed := false

		for i := len(post) - 2; i >= 0; i-- {
			b := post[i]
			var d *Block
			for _, e := range b.Preds {
				p := e.b
				if idom[p.ID] == nil {
					continue
				}
				if d == nil {
					d = p
					continue
				}
				d = intersect(d, p, postnum, idom)
			}
			if d != idom[b.ID] {
				idom[b.ID] = d
				changed = true
			}
		}
		if !changed {
			break
		}
	}
	// Set idom of entry block to nil instead of itself.
	idom[f.Entry.ID] = nil
	return idom
}

// intersect finds the closest dominator of both b and c.
// It requires a postorder numbering of all the blocks.
func intersect(b, c *Block, postnum []int, idom []*Block) *Block {
	// TODO: This loop is O(n^2). It used to be used in nilcheck,
	// see BenchmarkNilCheckDeep*.
	for b != c {
		if postnum[b.ID] < postnum[c.ID] {
			b = idom[b.ID]
		} else {
			c = idom[c.ID]
		}
	}
	return b
}

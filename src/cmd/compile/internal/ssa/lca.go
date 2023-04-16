// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// Code to compute lowest common ancestors in the dominator tree.
// https://en.wikipedia.org/wiki/Lowest_common_ancestor
// https://en.wikipedia.org/wiki/Range_minimum_query#Solution_using_constant_time_and_linearithmic_space

// lcaRange is a data structure that can compute lowest common ancestor queries
// in O(n lg n) precomputed space and O(1) time per query.
type lcaRange struct {
	// Additional information about each block (indexed by block ID).
	blocks []lcaRangeBlock

	// Data structure for range minimum queries.
	// rangeMin[k][i] contains the ID of the minimum depth block
	// in the Euler tour from positions i to i+1<<k-1, inclusive.
	rangeMin [][]ID
}

type lcaRangeBlock struct {
	b            *Block
	parentID     ID    // parentID in dominator tree.  0 = no parentID (entry or unreachable)
	firstChildID ID    // first child in dominator tree
	siblingID    ID    // next child of parentID
	pos          int32 // an index in the Euler tour where this block appears (any one of its occurrences)
	depth        int32 // depth in dominator tree (root=0, its children=1, etc.)
}

func makeLCArange(f *Func) *lcaRange {
	dom := f.Idom()

	// Build tree
	blocks := make([]lcaRangeBlock, f.NumBlocks())	// index为块索引,lcaRangeBlock.b就是对应的块
	for _, b := range f.Blocks {
		blocks[b.ID].b = b
		if dom[b.ID] == nil {
			continue // entry or unreachable
		}
		parent := dom[b.ID].ID	// 获取块b的最近祖先节点的ID
		blocks[b.ID].parentID = parent
		blocks[b.ID].siblingID = blocks[parent].firstChildID
		blocks[parent].firstChildID = b.ID
	}

	// Compute euler tour ordering.
	// Each reachable block will appear #children+1 times in the tour.
	tour := make([]ID, 0, f.NumBlocks()*2-1)	// 存储欧拉游序遍历后的块ID列表,对支配树进行先序遍历的结果
	type queueEntry struct {
		bid ID // block to work on
		cid ID // child we're already working on (0 = haven't started yet)
	}
	q := []queueEntry{{f.Entry.ID, 0}}
	for len(q) > 0 {
		n := len(q) - 1
		bid := q[n].bid	// 获取最后的块的ID
		cid := q[n].cid	// 获取当前正在处理的bid对应块的一个子块ID
		q = q[:n]	// 弹出队列最后一项

		// Add block to tour.
		blocks[bid].pos = int32(len(tour))
		tour = append(tour, bid)

		// Proceed down next child edge (if any).
		if cid == 0 {
			// This is our first visit to b. Set its depth.
			blocks[bid].depth = blocks[blocks[bid].parentID].depth + 1 // 父块的深度加一
			// Then explore its first child.
			cid = blocks[bid].firstChildID
		} else {
			// We've seen b before. Explore the next child.
			cid = blocks[cid].siblingID
		}
		if cid != 0 {	// 没有将bid的所有子节点遍历完
			q = append(q, queueEntry{bid, cid}, queueEntry{cid, 0})	// 添加当前的cid进行下次遍历,添加cid为父节点进行遍历,因为取q的最后一项进行遍历,所以这也是深度遍历
		}
	}

	// Compute fast range-minimum query data structure
	// rangeMin[2][0] = 1 表示步进为2的情况下欧拉游序号为0-2之间的最小深度的块ID为1
	var rangeMin [][]ID	// (2的(第一维的索引号-1)次方)代表步进的长度,第二维的第i项表示(i-1)项通过此步进找到的欧拉游序号
	rangeMin = append(rangeMin, tour) // 1-size windows are just the tour itself.
	// 依次求出长度为1,2,.....。n的所有区间的最小值
	for logS, s := 1, 2; s < len(tour); logS, s = logS+1, s*2 {
		r := make([]ID, len(tour)-s+1)
		for i := 0; i < len(tour)-s+1; i++ {
			// 以s/2为步进找到深度较大的block的ID放到r[i]中
			bid := rangeMin[logS-1][i]
			bid2 := rangeMin[logS-1][i+s/2]
			if blocks[bid2].depth < blocks[bid].depth {
				bid = bid2
			}
			r[i] = bid	// 保存深度较大的block的ID
		}
		rangeMin = append(rangeMin, r)	// r在rangeMin中的索引应该是logS
	}

	return &lcaRange{blocks: blocks, rangeMin: rangeMin}
}

// find returns the lowest common ancestor of a and b.
func (lca *lcaRange) find(a, b *Block) *Block {
	if a == b {
		return a
	}
	// Find the positions of a and b in the Euler tour.
	p1 := lca.blocks[a.ID].pos
	p2 := lca.blocks[b.ID].pos
	if p1 > p2 {	// 保证p1的欧拉游序号小于p2的
		p1, p2 = p2, p1
	}

	// The lowest common ancestor is the minimum depth block
	// on the tour from p1 to p2.  We've precomputed minimum
	// depth blocks for powers-of-two subsequences of the tour.
	// Combine the right two precomputed values to get the answer.
	logS := uint(log2(int64(p2 - p1)))
	bid1 := lca.rangeMin[logS][p1]
	bid2 := lca.rangeMin[logS][p2-1<<logS+1]
	if lca.blocks[bid1].depth < lca.blocks[bid2].depth {
		return lca.blocks[bid1].b
	}
	return lca.blocks[bid2].b
}

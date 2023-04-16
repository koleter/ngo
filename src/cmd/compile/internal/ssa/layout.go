// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// layout orders basic blocks in f with the goal of minimizing control flow instructions.
// After this phase returns, the order of f.Blocks matters and is the order
// in which those blocks will appear in the assembly output.
func layout(f *Func) {
	f.Blocks = layoutOrder(f)
}

// Register allocation may use a different order which has constraints
// imposed by the linear-scan algorithm. Note that f.pass here is
// regalloc, so the switch is conditional on -d=ssa/regalloc/test=N
func layoutRegallocOrder(f *Func) []*Block {

	switch f.pass.test {
	case 0: // layout order
		return layoutOrder(f) // layout pass的块顺序
	case 1: // existing block order
		return f.Blocks
	case 2: // reverse of postorder; legal, but usually not good.
		po := f.postorder()
		visitOrder := make([]*Block, len(po))
		for i, b := range po {
			j := len(po) - i - 1
			visitOrder[j] = b
		}
		return visitOrder
	}

	return nil
}

func layoutOrder(f *Func) []*Block {
	order := make([]*Block, 0, f.NumBlocks())
	scheduled := make([]bool, f.NumBlocks())
	idToBlock := make([]*Block, f.NumBlocks()) // 块ID对应的块指针
	indegree := make([]int, f.NumBlocks())     // 保存每个块的入度
	posdegree := f.newSparseSet(f.NumBlocks()) // blocks with positive remaining degree
	defer f.retSparseSet(posdegree)
	zerodegree := f.newSparseSet(f.NumBlocks()) // blocks with zero remaining degree
	defer f.retSparseSet(zerodegree)
	exit := f.newSparseSet(f.NumBlocks()) // exit blocks ID
	defer f.retSparseSet(exit)

	// Populate idToBlock and find exit blocks.
	for _, b := range f.Blocks {
		idToBlock[b.ID] = b
		if b.Kind == BlockExit {
			exit.add(b.ID)
		}
	}

	// Expand exit to include blocks post-dominated by exit blocks.
	for {
		changed := false
		for _, id := range exit.contents() { // 遍历所有的exit块ID
			b := idToBlock[id] // 获取块
		NextPred:
			for _, pe := range b.Preds { // 遍历所有前驱块
				p := pe.b                // b的前驱块
				if exit.contains(p.ID) { // 前驱块在exit中,表示代码进入了前驱块就一定会exit
					continue
				}
				for _, s := range p.Succs { // 遍历前驱块的后继
					if !exit.contains(s.b.ID) { // 后继块未全部在exit中就跳过去处理下一个前驱,这一步是要找到代码进入后就一定会exit的p块
						continue NextPred
					}
				}
				// All Succs are in exit; add p.
				exit.add(p.ID)
				changed = true
			}
		}
		if !changed {
			break
		}
	}

	// Initialize indegree of each block
	for _, b := range f.Blocks {
		if exit.contains(b.ID) {
			// exit blocks are always scheduled last
			continue
		}
		indegree[b.ID] = len(b.Preds)
		if len(b.Preds) == 0 {
			zerodegree.add(b.ID)
		} else {
			posdegree.add(b.ID)
		}
	}

	bid := f.Entry.ID
blockloop:
	for {
		// add block to schedule
		b := idToBlock[bid]              // 根据块id获取对应的块
		order = append(order, b)         // 添加到order中
		scheduled[bid] = true            // 标记bid已被处理
		if len(order) == len(f.Blocks) { // 已处理完所有的blocks
			break
		}

		for _, e := range b.Succs { // 遍历后继
			c := e.b         // 获取后继块
			indegree[c.ID]-- // 后继块的入度减一
			if indegree[c.ID] == 0 {
				posdegree.remove(c.ID)
				zerodegree.add(c.ID)
			}
		}

		// Pick the next block to schedule
		// Pick among the successor blocks that have not been scheduled yet.

		// Use likely direction if we have it.
		var likely *Block
		switch b.Likely {
		case BranchLikely:
			likely = b.Succs[0].b
		case BranchUnlikely:
			likely = b.Succs[1].b
		}
		if likely != nil && !scheduled[likely.ID] { // 存在明确的静态分支预测且likely块未被调度
			bid = likely.ID // 处理likely块
			continue
		}

		// Use degree for now.
		bid = 0
		mindegree := f.NumBlocks()
		// 找到后继中未被调度且不是exit块的拥有最小入度的块ID赋给bid
		for _, e := range order[len(order)-1].Succs { // 这里的order的最后一项不就是循环开头放到order中的b么
			c := e.b
			if scheduled[c.ID] || c.Kind == BlockExit {
				continue
			}
			if indegree[c.ID] < mindegree {
				mindegree = indegree[c.ID]
				bid = c.ID
			}
		}
		if bid != 0 { // 找到满足的块,继续进行下一次的调度
			continue
		}
		// TODO: improve this part
		// No successor of the previously scheduled block works.
		// Pick a zero-degree block if we can.
		for zerodegree.size() > 0 {
			cid := zerodegree.pop()
			if !scheduled[cid] { // cid未被调度且入度为0
				bid = cid // 下一个调度cid
				continue blockloop
			}
		}
		// Still nothing, pick any non-exit block.
		for posdegree.size() > 0 {
			cid := posdegree.pop()
			if !scheduled[cid] {
				bid = cid
				continue blockloop
			}
		}
		// Pick any exit block.
		// TODO: Order these to minimize jump distances?
		for {
			cid := exit.pop()
			if !scheduled[cid] {
				bid = cid
				continue blockloop
			}
		}
	}
	f.laidout = true
	return order
	//f.Blocks = order
}

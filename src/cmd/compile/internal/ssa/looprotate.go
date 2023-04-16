// Copyright 2017 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// loopRotate converts loops with a check-loop-condition-at-beginning
// to loops with a check-loop-condition-at-end.
// This helps loops avoid extra unnecessary jumps.
//
//   loop:
//     CMPQ ...
//     JGE exit
//     ...
//     JMP loop
//   exit:
//
//    JMP entry
//  loop:
//    ...
//  entry:
//    CMPQ ...
//    JLT loop
func loopRotate(f *Func) {
	loopnest := f.loopnest()
	if loopnest.hasIrreducible {
		return
	}
	if len(loopnest.loops) == 0 {
		return
	}

	idToIdx := make([]int, f.NumBlocks()) // 块ID对应f.Blocks中的索引
	for i, b := range f.Blocks {
		idToIdx[b.ID] = i
	}

	// Set of blocks we're moving, by ID.
	move := map[ID]struct{}{}

	// Map from block ID to the moving blocks that should
	// come right after it.
	after := map[ID][]*Block{}

	// Check each loop header and decide if we want to move it.
	for _, loop := range loopnest.loops { // 遍历所有循环结构体
		b := loop.header // 获取循环头所在块
		var p *Block     // b's in-loop predecessor
		for _, e := range b.Preds {
			if e.b.Kind != BlockPlain { // 保证前驱块是基本块
				continue
			}
			if loopnest.b2l[e.b.ID] != loop { // 找到循环尾部所在块
				continue
			}
			p = e.b
		}
		// p == nil时的情况想象不到,p == b表示这个循环是个空循环,没有循环体
		if p == nil || p == b {
			continue
		}
		after[p.ID] = []*Block{b} // 标记将b(循环头块)移动到p之后
		// 将循环头到循环尾之间的块都放到循环尾部的后面
		for {
			nextIdx := idToIdx[b.ID] + 1  // 找到b位于f.Blocks中的下一个块的索引
			if nextIdx >= len(f.Blocks) { // reached end of function (maybe impossible?)
				break
			}
			nextb := f.Blocks[nextIdx] // 获取被移动的块的下一个块
			if nextb == p {            // original loop predecessor is next
				break
			}
			if loopnest.b2l[nextb.ID] != loop { // about to leave loop
				break
			}
			// nextb也放到p块的后面
			after[p.ID] = append(after[p.ID], nextb)
			b = nextb // 继续判断下一个块
		}

		// Place b after p.
		for _, b := range after[p.ID] {
			move[b.ID] = struct{}{} // 记录要被移动的块
		}
	}

	// Move blocks to their destinations in a single pass.
	// We rely here on the fact that loop headers must come
	// before the rest of the loop.  And that relies on the
	// fact that we only identify reducible loops.
	j := 0
	for i, b := range f.Blocks {
		if _, ok := move[b.ID]; ok { // 要被移动的块就跳过等待被覆盖
			continue
		}
		f.Blocks[j] = b
		j++
		for _, a := range after[b.ID] { // 将after[b.ID]的块放到b块的后面
			if j > i {
				f.Fatalf("head before tail in loop %s", b)
			}
			f.Blocks[j] = a
			j++
		}
	}
	if j != len(f.Blocks) {
		f.Fatalf("bad reordering in looprotate")
	}
}

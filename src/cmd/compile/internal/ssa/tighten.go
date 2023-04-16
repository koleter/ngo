// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// tighten moves Values closer to the Blocks in which they are used.
// This can reduce the amount of register spilling required,
// if it doesn't also create more live values.
// A Value can be moved to any block that
// dominates all blocks in which it is used.
func tighten(f *Func) {
	canMove := make([]bool, f.NumValues())
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if v.Op.isLoweredGetClosurePtr() {
				// Must stay in the entry block.
				continue
			}
			switch v.Op {
			case OpPhi, OpArg, OpSelect0, OpSelect1:
				// Phis need to stay in their block.
				// Arg must stay in the entry block.
				// Tuple selectors must stay with the tuple generator.
				continue
			}
			if v.MemoryArg() != nil {
				// We can't move values which have a memory arg - it might
				// make two memory values live across a block boundary.
				continue
			}
			// Count arguments which will need a register.
			narg := 0
			for _, a := range v.Args {
				if !a.rematerializeable() {
					narg++
				}
			}
			if narg >= 2 && !v.Type.IsFlags() {
				// Don't move values with more than one input, as that may
				// increase register pressure.
				// We make an exception for flags, as we want flag generators
				// moved next to uses (because we only have 1 flag register).
				continue
			}
			canMove[v.ID] = true
		}
	}

	// Build data structure for fast least-common-ancestor queries.
	lca := makeLCArange(f)

	// For each moveable value, record the block that dominates all uses found so far.
	target := make([]*Block, f.NumValues())		// value ID对应将其移动到的块

	// Grab loop information.
	// We use this to make sure we don't tighten a value into a (deeper) loop.
	idom := f.Idom()
	loops := f.loopnest()
	loops.calculateDepths()

	changed := true
	for changed {
		changed = false

		// Reset target
		for i := range target {
			target[i] = nil
		}

		// Compute target locations (for moveable values only).
		// target location = the least common ancestor of all uses in the dominator tree.
		for _, b := range f.Blocks {
			for _, v := range b.Values {
				for i, a := range v.Args {
					if !canMove[a.ID] {	// 找到可以move的参数
						continue
					}
					use := b	// 该参数在哪个块中被使用
					if v.Op == OpPhi {	// phi函数好像在canMove中不会标记为true,所以这个if语句应该永远不会执行
						use = b.Preds[i].b
					}
					if target[a.ID] == nil {
						target[a.ID] = use
					} else {	// 有多个块使用到了这个arg
						target[a.ID] = lca.find(target[a.ID], use)  // 找到两个块中的最低公共祖先
					}
				}
			}
			for _, c := range b.ControlValues() {
				if !canMove[c.ID] {		// 找到可以move的控制value
					continue
				}
				if target[c.ID] == nil {	// c不需要移动就保持现状
					target[c.ID] = b
				} else {
					target[c.ID] = lca.find(target[c.ID], b)	  // 找到两个块中的最低公共祖先
				}
			}
		}

		// If the target location is inside a loop,
		// move the target location up to just before the loop head.
		for _, b := range f.Blocks {
			origloop := loops.b2l[b.ID]	// 找到块对应的循环头结构体loop
			for _, v := range b.Values {
				t := target[v.ID]	// v将被移动到哪个块中
				if t == nil {
					continue
				}
				targetloop := loops.b2l[t.ID]	// 目标块对应的循环头结构体loop
				// 将原本不在循环中的value移动到了一个循环块中或者移动到了更深的循环中了
				for targetloop != nil && (origloop == nil || targetloop.depth > origloop.depth) {
					t = idom[targetloop.header.ID]	// 找到目标块的最近支配节点
					target[v.ID] = t				// 移动到这个最近支配节点中
					targetloop = loops.b2l[t.ID]
				}
			}
		}

		// Move values to target locations.
		for _, b := range f.Blocks {
			for i := 0; i < len(b.Values); i++ {
				v := b.Values[i]
				t := target[v.ID]
				if t == nil || t == b {
					// v is not moveable, or is already in correct place.
					continue
				}
				// Move v to the block which dominates its uses.
				t.Values = append(t.Values, v)
				v.Block = t
				last := len(b.Values) - 1
				b.Values[i] = b.Values[last]
				b.Values[last] = nil
				b.Values = b.Values[:last]
				changed = true
				i--
			}
		}
	}
}

// phiTighten moves constants closer to phi users.
// This pass avoids having lots of constants live for lots of the program.
// See issue 16407.
func phiTighten(f *Func) {
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if v.Op != OpPhi {
				continue
			}
			for i, a := range v.Args {
				if !a.rematerializeable() {
					continue // not a constant we can move around
				}
				if a.Block == b.Preds[i].b {
					continue // already in the right place
				}
				// Make a copy of a, put in predecessor block.
				v.SetArg(i, a.copyInto(b.Preds[i].b))
			}
		}
	}
}

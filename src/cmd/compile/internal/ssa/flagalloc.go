// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// flagalloc allocates the flag register among all the flag-generating
// instructions. Flag values are recomputed if they need to be
// spilled/restored.
func flagalloc(f *Func) {
	// Compute the in-register flag value we want at the end of
	// each block. This is basically a best-effort live variable
	// analysis, so it can be much simpler than a full analysis.
	end := make([]*Value, f.NumBlocks()) // 表示某个块最后传给后继块的flag value
	po := f.postorder()                  // 获取倒序块序列
	for n := 0; n < 2; n++ {             // 遍历2次的循环
		for _, b := range po { // 倒序遍历块
			// Walk values backwards to figure out what flag
			// value we want in the flag register at the start
			// of the block.
			var flag *Value // 存储当前块的flag类型的value
			for _, c := range b.ControlValues() {
				if c.Type.IsFlags() { // lowerBlock时会将控制语句转为TypeFlags类型的语句
					if flag != nil {
						panic("cannot have multiple controls using flags")
					}
					flag = c
				}
			}
			if flag == nil { // 当前块没有flag value,使用
				flag = end[b.ID]
			}
			// flag表示之前的flag寄存器的状态
			for j := len(b.Values) - 1; j >= 0; j-- { // 倒序遍历块的values
				v := b.Values[j]
				if v == flag { // 找到了控制语句就将flag置为nil,因为这是倒序遍历,这个value之前的flag寄存器未必与当前一致
					flag = nil
				}
				if v.clobbersFlags() { // 会更改flag寄存器的value
					flag = nil
				}
				for _, a := range v.Args { // 遍历v的参数
					if a.Type.IsFlags() { // 用到了之前的flag,说明之前的flag寄存器状态是a
						flag = a
					}
				}
			}
			if flag != nil { // 表示当前的flag是从前驱块中传下来的flag
				for _, e := range b.Preds { // 标记所有前驱块输出的flag
					p := e.b
					end[p.ID] = flag
				}
			}
		}
	}

	// For blocks which have a flags control value, that's the only value
	// we can leave in the flags register at the end of the block. (There
	// is no place to put a flag regeneration instruction.)
	for _, b := range f.Blocks {
		if b.Kind == BlockDefer {
			// Defer blocks internally use/clobber the flags value.
			end[b.ID] = nil // defer块执行后就退出函数了,所以defer块中的flag无意义
			continue
		}
		for _, v := range b.ControlValues() {
			if v.Type.IsFlags() && end[b.ID] != v { // b块的控制value传出的flag与记录的不符,说明b块的后继中的flag可能是个phi
				end[b.ID] = nil
			}
		}
	}

	// Compute which flags values will need to be spilled.
	spill := map[ID]bool{} // 标记某个flag需要被恢复
	for _, b := range f.Blocks {
		var flag *Value
		if len(b.Preds) > 0 { // 有多个前驱就获取第一个前驱传出的flag value
			flag = end[b.Preds[0].b.ID]
		}
		for _, v := range b.Values { // 正向遍历b块中的values
			for _, a := range v.Args { // 遍历b块中所有的values用到的args
				if !a.Type.IsFlags() { // 找到flag value
					continue
				}
				if a == flag { // 找到不是通过前驱传进来的flag value
					continue
				}
				// a will need to be restored here.
				// 某个value依赖a的flag寄存器状态,那么a应该被压入栈上并在此时恢复
				spill[a.ID] = true // 表示在这里恢复a
				flag = a           // 之后的flag状态就是a
			}
			if v.clobbersFlags() { // 当前v会破坏flag寄存器
				flag = nil
			}
			if v.Type.IsFlags() { // 遇到flag value,表示之后的flag状态为v了
				flag = v
			}
		}
		for _, v := range b.ControlValues() {
			if v != flag && v.Type.IsFlags() {
				spill[v.ID] = true
			}
		}
		if v := end[b.ID]; v != nil && v != flag {
			spill[v.ID] = true
		}
	}

	// Add flag spill and recomputation where they are needed.
	var remove []*Value // values that should be checked for possible removal
	var oldSched []*Value
	for _, b := range f.Blocks {
		oldSched = append(oldSched[:0], b.Values...)
		b.Values = b.Values[:0]
		// The current live flag value (the pre-flagalloc copy).
		var flag *Value // 可以简单理解为当前的eflags寄存器中的状态
		if len(b.Preds) > 0 {
			flag = end[b.Preds[0].b.ID]
			// Note: the following condition depends on the lack of critical edges.
			for _, e := range b.Preds[1:] {
				p := e.b
				if end[p.ID] != flag {
					f.Fatalf("live flag in %s's predecessors not consistent", b)
				}
			}
		}
		for _, v := range oldSched {
			if v.Op == OpPhi && v.Type.IsFlags() {
				f.Fatalf("phi of flags not supported: %s", v.LongString())
			}

			// If v will be spilled, and v uses memory, then we must split it
			// into a load + a flag generator.
			if spill[v.ID] && v.MemoryArg() != nil {
				remove = append(remove, v) // v将被切分为load与flag values,这个v将被移除
				if !f.Config.splitLoad(v) {
					f.Fatalf("can't split flag generator: %s", v.LongString())
				}
			}

			// Make sure any flag arg of v is in the flags register.
			// If not, recompute it.
			for i, a := range v.Args {
				if !a.Type.IsFlags() { // 找到v中的flag value
					continue
				}
				if a == flag { // 找到与flag不同的参数
					continue
				}
				// Recalculate a
				c := copyFlags(a, b) // 在b中创建一个与a相同的value
				// Update v.
				v.SetArg(i, c)
				// Remember the most-recently computed flag value.
				flag = a
			}
			// Issue v.
			b.Values = append(b.Values, v)
			if v.clobbersFlags() {
				flag = nil
			}
			if v.Type.IsFlags() {
				flag = v
			}
		}
		for i, v := range b.ControlValues() {
			if v != flag && v.Type.IsFlags() { // b的控制语句与传递过来的flag不相同
				// Recalculate control value.
				remove = append(remove, v)
				c := copyFlags(v, b) // ???????
				b.ReplaceControl(i, c)
				flag = v
			}
		}
		if v := end[b.ID]; v != nil && v != flag {
			// Need to reissue flag generator for use by
			// subsequent blocks.
			remove = append(remove, v)
			copyFlags(v, b)
			// Note: this flag generator is not properly linked up
			// with the flag users. This breaks the SSA representation.
			// We could fix up the users with another pass, but for now
			// we'll just leave it. (Regalloc has the same issue for
			// standard regs, and it runs next.)
			// For this reason, take care not to add this flag
			// generator to the remove list.
		}
	}

	// Save live flag state for later.
	for _, b := range f.Blocks {
		b.FlagsLiveAtEnd = end[b.ID] != nil
	}

	const go115flagallocdeadcode = true
	if !go115flagallocdeadcode {
		return
	}

	// Remove any now-dead values.
	// The number of values to remove is likely small,
	// and removing them requires processing all values in a block,
	// so minimize the number of blocks that we touch.

	// Shrink remove to contain only dead values, and clobber those dead values.
	for i := 0; i < len(remove); i++ {
		v := remove[i]
		if v.Uses == 0 {
			v.reset(OpInvalid)
			continue
		}
		// Remove v.
		last := len(remove) - 1
		remove[i] = remove[last]
		remove[last] = nil
		remove = remove[:last]
		i-- // reprocess value at i
	}

	if len(remove) == 0 {
		return
	}

	removeBlocks := f.newSparseSet(f.NumBlocks())
	defer f.retSparseSet(removeBlocks)
	for _, v := range remove {
		removeBlocks.add(v.Block.ID)
	}

	// Process affected blocks, preserving value order.
	for _, b := range f.Blocks {
		if !removeBlocks.contains(b.ID) {
			continue
		}
		i := 0
		for j := 0; j < len(b.Values); j++ {
			v := b.Values[j]
			if v.Op == OpInvalid {
				continue
			}
			b.Values[i] = v
			i++
		}
		b.truncateValues(i)
	}
}

func (v *Value) clobbersFlags() bool {
	if opcodeTable[v.Op].clobberFlags {
		return true
	}
	if v.Type.IsTuple() && (v.Type.FieldType(0).IsFlags() || v.Type.FieldType(1).IsFlags()) {
		// This case handles the possibility where a flag value is generated but never used.
		// In that case, there's no corresponding Select to overwrite the flags value,
		// so we must consider flags clobbered by the tuple-generating instruction.
		return true
	}
	return false
}

// copyFlags copies v (flag generator) into b, returns the copy.
// If v's arg is also flags, copy recursively.
func copyFlags(v *Value, b *Block) *Value {
	flagsArgs := make(map[int]*Value)
	for i, a := range v.Args {
		if a.Type.IsFlags() || a.Type.IsTuple() {
			flagsArgs[i] = copyFlags(a, b)
		}
	}
	c := v.copyInto(b) // 在b块中创建一个与v相同的value
	for i, a := range flagsArgs {
		c.SetArg(i, a)
	}
	return c
}

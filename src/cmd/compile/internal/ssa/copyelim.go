// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// copyelim removes all uses of OpCopy values from f.
// A subsequent deadcode pass is needed to actually remove the copies.
func copyelim(f *Func) {
	// Modify all values so no arg (including args
	// of OpCopy) is a copy.
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			copyelimValue(v)	// 将b中的所有OpCopy的拷贝参数换成最根本的源数据
		}
	}

	// Update block control values.
	for _, b := range f.Blocks {
		for i, v := range b.ControlValues() {
			if v.Op == OpCopy {	// 相当于if判断的表达式是一个copy操作
				b.ReplaceControl(i, v.Args[0])	// 将控制流语句替换为拷贝的参数
			}
		}
	}

	// Update named values.
	for _, name := range f.Names {
		values := f.NamedValues[name]
		for i, v := range values {
			if v.Op == OpCopy {
				values[i] = v.Args[0]
			}
		}
	}
}

// copySource returns the (non-copy) op which is the
// ultimate source of v.  v must be a copy op.
func copySource(v *Value) *Value {
	w := v.Args[0]	// 获取拷贝的值

	// This loop is just:
	// for w.Op == OpCopy {
	//     w = w.Args[0]
	// }
	// but we take some extra care to make sure we
	// don't get stuck in an infinite loop.
	// Infinite copy loops may happen in unreachable code.
	// (TODO: or can they? Needs a test.)
	slow := w
	var advance bool
	for w.Op == OpCopy {
		w = w.Args[0]	// 获取拷贝的源数据
		if w == slow {	// 存在一个拷贝环
			w.reset(OpUnknown)
			break
		}
		if advance {	// 用于控制慢指针的进度
			slow = slow.Args[0]
		}
		advance = !advance
	}

	// The answer is w.  Update all the copies we saw
	// to point directly to w.  Doing this update makes
	// sure that we don't end up doing O(n^2) work
	// for a chain of n copies.
	for v != w {
		x := v.Args[0]	// 临时存储待拷贝的参数,便于下次继续向下循环
		v.SetArg(0, w)	// 拷贝的参数为w
		v = x	// 继续循环遍历x
	}
	return w
}

// copyelimValue ensures that no args of v are copies.
func copyelimValue(v *Value) {
	for i, a := range v.Args {
		if a.Op == OpCopy {
			v.SetArg(i, copySource(a))	// 将拷贝操作的目标换成最根本的源数据
		}
	}
}

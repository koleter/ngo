// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// phielim eliminates redundant phi values from f.
// A phi is redundant if its arguments are all equal. For
// purposes of counting, ignore the phi itself. Both of
// these phis are redundant:
//   v = phi(x,x,x)
//   v = phi(x,v,x,v)
// We repeat this process to also catch situations like:
//   v = phi(x, phi(x, x), phi(x, v))
// TODO: Can we also simplify cases like:
//   v = phi(v, w, x)
//   w = phi(v, w, x)
// and would that be useful?
func phielim(f *Func) {
	for {	// 死循环,直到将所有可以消除的phi都消除掉
		change := false
		for _, b := range f.Blocks {
			for _, v := range b.Values {
				copyelimValue(v)	// 将拷贝操作的参数替换为最根本的源参数
				change = phielimValue(v) || change
			}
		}
		if !change {	// 所有可以消除的phi都消除掉了
			break
		}
	}
}

// phielimValue tries to convert the phi v to a copy.
func phielimValue(v *Value) bool {
	if v.Op != OpPhi {
		return false
	}

	// If there are two distinct args of v which
	// are not v itself, then the phi must remain.
	// Otherwise, we can replace it with a copy.
	var w *Value	// 记录上一个不为v的Arg
	for _, x := range v.Args {
		if x == v {
			continue
		}
		if x == w {	// phi函数中的某个Arg等于上一个不为v的Arg
			continue
		}
		if w != nil {	// 至少有两个不为v的不同Arg,所以这个phi函数不能被消除
			return false
		}
		w = x
	}

	if w == nil {	// 表示phi函数中的Args都等于v,话说这种情况应该不可能吧???
		// v references only itself. It must be in
		// a dead code loop. Don't bother modifying it.
		return false
	}
	v.Op = OpCopy	// 到了这一步,表示v中的参数实际上是一个变量,将phi替换为OpCopy
	v.SetArgs1(w)
	f := v.Block.Func
	if f.pass.debug > 0 {
		f.Warnl(v.Pos, "eliminated phi")
	}
	return true
}

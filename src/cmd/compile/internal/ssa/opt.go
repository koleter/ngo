// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// machine-independent optimization
func opt(f *Func) {
	// rewriteBlockgeneric处理if块中的控制Value,将其进行优化
	// rewriteValuegeneric用于重写特定Value进行运算优化
	applyRewrite(f, rewriteBlockgeneric, rewriteValuegeneric)
}

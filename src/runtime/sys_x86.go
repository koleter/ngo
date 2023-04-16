// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build amd64 386

package runtime

import (
	"runtime/internal/sys"
	"unsafe"
)

// adjust Gobuf as if it executed a call to fn with context ctxt
// and then did an immediate gosave.
func gostartcall(buf *gobuf, fn, ctxt unsafe.Pointer) {
	sp := buf.sp	//newg的栈顶，目前newg栈上只有fn的参数，sp指向的是fn的第一参数
	if sys.RegSize > sys.PtrSize {	// 32位程序
		sp -= sys.PtrSize	// 栈上开辟出一个指针的空间并通过下面一行代码保存一个0
		*(*uintptr)(unsafe.Pointer(sp)) = 0
	}
	sp -= sys.PtrSize	//为返回地址预留空间
	*(*uintptr)(unsafe.Pointer(sp)) = buf.pc	//伪装fn是被goexit函数调用的，使得fn执行完后返回goexit继续执行，从而完成清理工作
	buf.sp = sp	//重新设置buf.sp
	buf.pc = uintptr(fn)	//当goroutine被调度起来时，会从这里的pc值开始执行，初始化时就是runtime.main
	buf.ctxt = ctxt
}

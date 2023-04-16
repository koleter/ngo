// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package atomic

import "unsafe"

// Export some functions via linkname to assembly in sync/atomic.
//go:linkname Load
//go:linkname Loadp
//go:linkname Load64

//go:nosplit
//go:noinline
func Load(ptr *uint32) uint32 {
	return *ptr
}

//go:nosplit
//go:noinline
func Loadp(ptr unsafe.Pointer) unsafe.Pointer {
	return *(*unsafe.Pointer)(ptr)
}

//go:nosplit
//go:noinline
func Load64(ptr *uint64) uint64 {
	return *ptr
}

//go:nosplit
//go:noinline
func LoadAcq(ptr *uint32) uint32 {
	return *ptr
}

//go:noescape
func Xadd(ptr *uint32, delta int32) uint32	//lock xadd指令，交换*ptr与delta中的值并相加后保存到*ptr中

//go:noescape
func Xadd64(ptr *uint64, delta int64) uint64 //交换后再相加，返回相加后的结果，有lock指令，但是实际上delta的值并未改变

//go:noescape
func Xadduintptr(ptr *uintptr, delta uintptr) uintptr //相当于返回*ptr与delta之和

//go:noescape
func Xchg(ptr *uint32, new uint32) uint32 //交换ptr指向的值与new的值，并返回旧的ptr的值（该操作只会改变*ptr的内容）

//go:noescape
func Xchg64(ptr *uint64, new uint64) uint64

//go:noescape
func Xchguintptr(ptr *uintptr, new uintptr) uintptr

//go:nosplit
//go:noinline
func Load8(ptr *uint8) uint8 {
	return *ptr
}

//go:noescape
func And8(ptr *uint8, val uint8)

//go:noescape
func Or8(ptr *uint8, val uint8)

// NOTE: Do not add atomicxor8 (XOR is not idempotent).

//go:noescape
func Cas64(ptr *uint64, old, new uint64) bool

//go:noescape
func CasRel(ptr *uint32, old, new uint32) bool

//go:noescape
func Store(ptr *uint32, val uint32)

//go:noescape
func Store8(ptr *uint8, val uint8)

//go:noescape
func Store64(ptr *uint64, val uint64)	//通过xchg指令以交换的方式将val存储到ptr指向的内容，但val的值没有改变

//go:noescape
func StoreRel(ptr *uint32, val uint32)

// StorepNoWB performs *ptr = val atomically and without a write
// barrier.
//
// NO go:noescape annotation; see atomic_pointer.go.
func StorepNoWB(ptr unsafe.Pointer, val unsafe.Pointer)	//*ptr = val

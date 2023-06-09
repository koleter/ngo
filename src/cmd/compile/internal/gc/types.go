// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import (
	"cmd/compile/internal/types"
)

// convenience constants
const (
	Txxx = types.Txxx

	TINT8    = types.TINT8
	TUINT8   = types.TUINT8	//uint8
	TINT16   = types.TINT16	//int16
	TUINT16  = types.TUINT16	
	TINT32   = types.TINT32
	TUINT32  = types.TUINT32
	TINT64   = types.TINT64	//int64
	TUINT64  = types.TUINT64
	TINT     = types.TINT
	TUINT    = types.TUINT
	TUINTPTR = types.TUINTPTR	// unsafe uintptr

	TCOMPLEX64  = types.TCOMPLEX64	// 复数类型，用float32表示
	TCOMPLEX128 = types.TCOMPLEX128	// 复数类型，用float64表示

	TFLOAT32 = types.TFLOAT32
	TFLOAT64 = types.TFLOAT64

	TBOOL = types.TBOOL

	TPTR       = types.TPTR
	TFUNC      = types.TFUNC
	TSLICE     = types.TSLICE
	TARRAY     = types.TARRAY
	TSTRUCT    = types.TSTRUCT
	TCHAN      = types.TCHAN
	TMAP       = types.TMAP
	TINTER     = types.TINTER	//interface{}
	TFORW      = types.TFORW
	TANY       = types.TANY
	TSTRING    = types.TSTRING	//string
	TUNSAFEPTR = types.TUNSAFEPTR

	// pseudo-types for literals
	TIDEAL = types.TIDEAL	// untyped number
	TNIL   = types.TNIL
	TBLANK = types.TBLANK

	// pseudo-types for frame layout
	TFUNCARGS = types.TFUNCARGS
	TCHANARGS = types.TCHANARGS

	NTYPE = types.NTYPE
)

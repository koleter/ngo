// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import (
	"cmd/compile/internal/ssa"
	"cmd/compile/internal/types"
	"cmd/internal/obj"
	"cmd/internal/src"
	"sync"
)

const (
	BADWIDTH = types.BADWIDTH
)

var (
	// maximum size variable which we will allocate on the stack.
	// This limit is for explicit variable declarations like "var x T" or "x := ...".
	// Note: the flag smallframes can update this value.
	maxStackVarSize = int64(10 * 1024 * 1024)

	// maximum size of implicit variables that we will allocate on the stack.
	//   p := new(T)          allocating T on the stack
	//   p := &T{}            allocating T on the stack
	//   s := make([]T, n)    allocating [n]T on the stack
	//   s := []byte("...")   allocating [n]byte on the stack
	// Note: the flag smallframes can update this value.
	maxImplicitStackVarSize = int64(64 * 1024)

	// smallArrayBytes is the maximum size of an array which is considered small.
	// Small arrays will be initialized directly with a sequence of constant stores.
	// Large arrays will be initialized by copying from a static temp.
	// 256 bytes was chosen to minimize generated code + statictmp size.
	smallArrayBytes = int64(256)
)

// isRuntimePkg reports whether p is package runtime.
func isRuntimePkg(p *types.Pkg) bool {
	if compiling_runtime && p == localpkg {
		return true
	}
	return p.Path == "runtime"
}

// isReflectPkg reports whether p is package reflect.
func isReflectPkg(p *types.Pkg) bool {
	if p == localpkg {
		return myimportpath == "reflect"
	}
	return p.Path == "reflect"
}

// The Class of a variable/function describes the "storage class"
// of a variable or function. During parsing, storage classes are
// called declaration contexts.
type Class uint8

//go:generate stringer -type=Class
const (
	Pxxx      Class = iota // no class; used during ssa conversion to indicate pseudo-variables
	PEXTERN                // global variable
	PAUTO                  // local variables
	PAUTOHEAP              // local variable or parameter moved to heap
	PPARAM                 // input arguments
	PPARAMOUT              // output results
	PFUNC                  // global function

	// Careful: Class is stored in three bits in Node.flags.
	_ = uint((1 << 3) - iota) // static assert for iota <= (1 << 3)
)

// Slices in the runtime are represented by three components:
//
// type slice struct {
// 	ptr unsafe.Pointer
// 	len int
// 	cap int
// }
//
// Strings in the runtime are represented by two components:
//
// type string struct {
// 	ptr unsafe.Pointer
// 	len int
// }
//
// These variables are the offsets of fields and sizes of these structs.
var (
	slicePtrOffset int64
	sliceLenOffset int64
	sliceCapOffset int64

	sizeofSlice  int64
	sizeofString int64
)

var pragcgobuf [][]string

var outfile string // 生成的文件
var linkobj string

// nerrors is the number of compiler errors reported
// since the last call to saveerrors.
var nerrors int

// nsavederrors is the total number of compiler errors
// reported before the last call to saveerrors.
var nsavederrors int

var nsyntaxerrors int

var decldepth int32 // 声明时的作用域深度

var nolocalimports bool

var Debug [256]int //比如  Debug['l'] != 0，表示命令行参数中有-l

var debugstr string

var Debug_checknil int
var Debug_typeassert int

var localpkg *types.Pkg // package being compiled	当前正在被编译的包

var inimport bool // set during import

var itabpkg *types.Pkg // fake pkg for itab entries

var itablinkpkg *types.Pkg // fake package for runtime itab entries

var Runtimepkg *types.Pkg // fake package runtime

var racepkg *types.Pkg // package runtime/race

var msanpkg *types.Pkg // package runtime/msan

var unsafepkg *types.Pkg // package unsafe

var trackpkg *types.Pkg // fake package for field tracking

var mappkg *types.Pkg // fake package for map zero value

var gopkg *types.Pkg // pseudo-package for method symbols on anonymous receiver types

var zerosize int64

var myimportpath string // 当前正在编译的包路径名	full import path of the package being compiled

var localimport string

var asmhdr string

var simtype [NTYPE]types.EType

var (
	isInt     [NTYPE]bool
	isFloat   [NTYPE]bool
	isComplex [NTYPE]bool
	issimple  [NTYPE]bool // 第1到16的索引都是true,其他的都是false
)

var (
	okforeq    [NTYPE]bool
	okforadd   [NTYPE]bool
	okforand   [NTYPE]bool
	okfornone  [NTYPE]bool
	okforcmp   [NTYPE]bool
	okforbool  [NTYPE]bool
	okforcap   [NTYPE]bool
	okforlen   [NTYPE]bool
	okforarith [NTYPE]bool
	okforconst [NTYPE]bool
)

var (
	okfor [OEND][]bool
	iscmp [OEND]bool // 记录某种操作是否为比较操作
)

var minintval [NTYPE]*Mpint

var maxintval [NTYPE]*Mpint

var minfltval [NTYPE]*Mpflt

var maxfltval [NTYPE]*Mpflt

var xtop []*Node // 保存所有最顶层的AST

var exportlist []*Node // 导出列表

var importlist []*Node // imported functions and methods with inlinable bodies

var (
	funcsymsmu sync.Mutex // protects funcsyms and associated package lookups (see func funcsym)
	funcsyms   []*types.Sym
)

var dclcontext Class // PEXTERN/PAUTO	标志当前解析的上下文的类型

var Curfn *Node // 表示当前所在的函数的节点

var Widthptr int // 表示一个指针的宽度

var Widthreg int // 通用寄存器的字节数

var nblank *Node

var typecheckok bool

var compiling_runtime bool

// Compiling the standard library
var compiling_std bool

var use_writebarrier bool

var pure_go bool

var flag_installsuffix string

var flag_race bool

var flag_msan bool

var flagDWARF bool

// Whether we are adding any sort of code instrumentation, such as
// when the race detector is enabled.
var instrumenting bool

// Whether we are tracking lexical scopes for DWARF.
var trackScopes bool

// Controls generation of DWARF inlined instance records. Zero
// disables, 1 emits inlined routines but suppresses var info,
// and 2 emits inlined routines with tracking of formals/locals.
var genDwarfInline int

var debuglive int

var Ctxt *obj.Link

var writearchive bool

// nodfp貌似是一个Sym为fp的int32类型的入参,用于recover,是一个栈帧指针,推测为rbp
var nodfp *Node

var disable_checknil int

var autogeneratedPos src.XPos

// interface to back end

type Arch struct {
	LinkArch *obj.LinkArch

	REGSP     int
	MAXWIDTH  int64
	Use387    bool // should 386 backend use 387 FP instructions instead of sse2.
	SoftFloat bool

	PadFrame func(int64) int64

	// ZeroRange zeroes a range of memory on stack. It is only inserted
	// at function entry, and it is ok to clobber registers.
	ZeroRange func(*Progs, *obj.Prog, int64, int64, *uint32) *obj.Prog

	Ginsnop      func(*Progs) *obj.Prog
	Ginsnopdefer func(*Progs) *obj.Prog // special ginsnop for deferreturn

	// SSAMarkMoves marks any MOVXconst ops that need to avoid clobbering flags.
	SSAMarkMoves func(*SSAGenState, *ssa.Block)

	// SSAGenValue emits Prog(s) for the Value.
	SSAGenValue func(*SSAGenState, *ssa.Value)

	// SSAGenBlock emits end-of-block Progs. SSAGenValue should be called
	// for all values in the block before SSAGenBlock.
	SSAGenBlock func(s *SSAGenState, b, next *ssa.Block)
}

var thearch Arch

var (
	staticuint64s, // The actual type is [256]uint64, but we use [256*8]uint8 so we can address individual bytes.
	zerobase *Node // zerobase.Type = types.Types[TUINTPTR]

	assertE2I,
	assertE2I2,
	assertI2I,
	assertI2I2,
	deferproc,
	deferprocStack,
	Deferreturn,
	Duffcopy,
	Duffzero,
	gcWriteBarrier,
	goschedguarded,
	growslice,
	cutslice,
	msanread,
	msanwrite,
	newobject,
	newproc,
	panicdivide,
	panicshift,
	panicdottypeE,
	panicdottypeI,
	panicnildottype,
	panicoverflow,
	raceread,
	racereadrange,
	racewrite,
	racewriterange,
	x86HasPOPCNT,
	x86HasSSE41,
	x86HasFMA,
	armHasVFPv4,
	arm64HasATOMICS,
	typedmemclr,
	typedmemmove,
	Udiv,
	writeBarrier,
	zerobaseSym *obj.LSym

	BoundsCheckFunc [ssa.BoundsKindCount]*obj.LSym
	ExtendCheckFunc [ssa.BoundsKindCount]*obj.LSym

	// GO386=387
	ControlWord64trunc,
	ControlWord32 *obj.LSym

	// Wasm
	WasmMove,
	WasmZero,
	WasmDiv,
	WasmTruncS,
	WasmTruncU,
	SigPanic *obj.LSym
)

// GCWriteBarrierReg maps from registers to gcWriteBarrier implementation LSyms.
var GCWriteBarrierReg map[int16]*obj.LSym

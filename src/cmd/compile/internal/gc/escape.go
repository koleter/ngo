// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import (
	"cmd/compile/internal/logopt"
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"fmt"
	"math"
	"strings"
)

// Escape analysis.
//
// Here we analyze functions to determine which Go variables
// (including implicit allocations such as calls to "new" or "make",
// composite literals, etc.) can be allocated on the stack. The two
// key invariants we have to ensure are: (1) pointers to stack objects
// cannot be stored in the heap, and (2) pointers to a stack object
// cannot outlive that object (e.g., because the declaring function
// returned and destroyed the object's stack frame, or its space is
// reused across loop iterations for logically distinct variables).
//
// We implement this with a static data-flow analysis of the AST.
// First, we construct a directed weighted graph where vertices
// (termed "locations") represent variables allocated by statements
// and expressions, and edges represent assignments between variables
// (with weights representing addressing/dereference counts).
//
// Next we walk the graph looking for assignment paths that might
// violate the invariants stated above. If a variable v's address is
// stored in the heap or elsewhere that may outlive it, then v is
// marked as requiring heap allocation.
//
// To support interprocedural analysis, we also record data-flow from
// each function's parameters to the heap and to its result
// parameters. This information is summarized as "parameter tags",
// which are used at static call sites to improve escape analysis of
// function arguments.

// Constructing the location graph.
//
// Every allocating statement (e.g., variable declaration) or
// expression (e.g., "new" or "make") is first mapped to a unique
// "location."
//
// We also model every Go assignment as a directed edges between
// locations. The number of dereference operations minus the number of
// addressing operations is recorded as the edge's weight (termed
// "derefs"). For example:
//
//     p = &q    // -1
//     p = q     //  0
//     p = *q    //  1
//     p = **q   //  2
//
//     p = **&**&q  // 2
//
// Note that the & operator can only be applied to addressable
// expressions, and the expression &x itself is not addressable, so
// derefs cannot go below -1.
//
// Every Go language construct is lowered into this representation,
// generally without sensitivity to flow, path, or context; and
// without distinguishing elements within a compound variable. For
// example:
//
//     var x struct { f, g *int }
//     var u []*int
//
//     x.f = u[0]
//
// is modeled simply as
//
//     x = *u
//
// That is, we don't distinguish x.f from x.g, or u[0] from u[1],
// u[2], etc. However, we do record the implicit dereference involved
// in indexing a slice.

type Escape struct {
	allLocs []*EscLocation // 存储函数中所有的包含局部变量的EscLocation结构体

	curfn *Node // 当前进行逃逸分析的函数节点

	// loopDepth counts the current loop nesting depth within
	// curfn. It increments within each "for" loop and at each
	// label with a corresponding backwards "goto" (i.e.,
	// unstructured loop).
	loopDepth int // 循环嵌套深度从1开始

	heapLoc  EscLocation // 表示堆分配
	blankLoc EscLocation // 不会逃逸到堆
}

// An EscLocation represents an abstract location that stores a Go
// variable.
type EscLocation struct {
	n         *Node     // represented variable or expression, if any
	curfn     *Node     // enclosing function
	edges     []EscEdge // incoming edges
	loopDepth int       // loopDepth at declaration

	// derefs and walkgen are used during walkOne to track the
	// minimal dereferences from the walk root.
	derefs  int    // >= -1		记录src到dst的最小的解引用次数
	walkgen uint32 // 记录是第几个walk的EscLocation

	// dst and dstEdgeindex track the next immediate assignment
	// destination location during walkone, along with the index
	// of the edge pointing back to this location.
	dst        *EscLocation
	dstEdgeIdx int // dst的流入边的索引

	// queued is used by walkAll to track whether this location is
	// in the walk queue.
	queued bool

	// escapes reports whether the represented variable's address
	// escapes; that is, whether the variable must be heap
	// allocated.
	escapes bool

	// transient reports whether the represented expression's
	// address does not outlive the statement; that is, whether
	// its storage can be immediately reused.
	transient bool

	// paramEsc records the represented parameter's leak set.
	paramEsc EscLeaks
}

// An EscEdge represents an assignment edge between two Go variables.
type EscEdge struct {
	src    *EscLocation // 流向dst的节点
	derefs int          // >= -1		src流向dst时解引用的次数,-1表示取地址
	notes  *EscNote
}

// escapeFuncs performs escape analysis on a minimal batch of
// functions.
func escapeFuncs(fns []*Node, recursive bool) {
	for _, fn := range fns {
		if fn.Op != ODCLFUNC {
			Fatalf("unexpected node: %v", fn)
		}
	}

	var e Escape
	e.heapLoc.escapes = true // 标记数据流向这个heapLoc的节点都是逃逸的

	// Construct data-flow graph from syntax trees.
	for _, fn := range fns { // 遍历所有的递归函数节点,构建以e.heapLoc为根节点的数据流图
		// 遍历函数中所有声明的局部变量,创建相关的EscLocation结构体并保存到e.allLocs中,将确定会逃逸的EscLocation标记为逃逸并记录数据的流入到e.heapLoc的edges中
		e.initFunc(fn)
	}
	for _, fn := range fns {
		e.walkFunc(fn)
	}
	e.curfn = nil

	e.walkAll()
	e.finish(fns)
}

func (e *Escape) initFunc(fn *Node) {
	if fn.Op != ODCLFUNC || fn.Esc != EscFuncUnknown {
		Fatalf("unexpected node: %v", fn)
	}
	fn.Esc = EscFuncPlanned
	if Debug['m'] > 3 {
		Dump("escAnalyze", fn)
	}

	e.curfn = fn
	e.loopDepth = 1 // 循环嵌套深度从1开始

	// Allocate locations for local variables.
	for _, dcl := range fn.Func.Dcl { // 遍历函数中所有声明的局部变量
		if dcl.Op == ONAME { // 找到命名节点
			e.newLoc(dcl, false)
		}
	}
}

func (e *Escape) walkFunc(fn *Node) {
	fn.Esc = EscFuncStarted

	// Identify labels that mark the head of an unstructured loop.
	inspectList(fn.Nbody, func(n *Node) bool { // 遍历函数体的所有节点
		switch n.Op {
		case OLABEL: // Sym:
			n.Sym.Label = asTypesNode(&nonlooping)

		case OGOTO: // goto Sym
			// If we visited the label before the goto,
			// then this is a looping label.
			if n.Sym.Label == asTypesNode(&nonlooping) {
				n.Sym.Label = asTypesNode(&looping)
			}
		}

		return true
	})

	e.curfn = fn
	e.loopDepth = 1
	e.block(fn.Nbody)
}

// Below we implement the methods for walking the AST and recording
// data flow edges. Note that because a sub-expression might have
// side-effects, it's important to always visit the entire AST.
//
// For example, write either:
//
//     if x {
//         e.discard(n.Left)
//     } else {
//         e.value(k, n.Left)
//     }
//
// or
//
//     if x {
//         k = e.discardHole()
//     }
//     e.value(k, n.Left)
//
// Do NOT write:
//
//    // BAD: possibly loses side-effects within n.Left
//    if !x {
//        e.value(k, n.Left)
//    }

// stmt evaluates a single Go statement.
func (e *Escape) stmt(n *Node) {
	if n == nil {
		return
	}

	lno := setlineno(n)
	defer func() {
		lineno = lno
	}()

	if Debug['m'] > 2 {
		fmt.Printf("%v:[%d] %v stmt: %v\n", linestr(lineno), e.loopDepth, funcSym(e.curfn), n)
	}

	e.stmts(n.Ninit)

	switch n.Op {
	default:
		Fatalf("unexpected stmt: %v", n)
	// const pi = 3.14   48, type Int int or type Int = int  49, no-op (empty statement)  117, fallthrough  118,
	case ODCLCONST, ODCLTYPE, OEMPTY, OFALL, OINLMARK:
		// nop
	// 113, 115, 121
	case OBREAK, OCONTINUE, OGOTO:
		// TODO(mdempsky): Handle dead code?
		// { List } (block of code)    112
	case OBLOCK:
		e.stmts(n.List)

	case ODCL: // 45	var Left (declares Left of type Left.Type)
		// Record loop depth at declaration.
		if !n.Left.isBlank() { // 声明的变量不是_
			e.dcl(n.Left) // 记录n.Left声明的循环深度
		}

	case OLABEL: //123
		switch asNode(n.Sym.Label) {
		case &nonlooping: // 不是非结构循环
			if Debug['m'] > 2 {
				fmt.Printf("%v:%v non-looping label\n", linestr(lineno), n)
			}
		case &looping: // 是非结构循环
			if Debug['m'] > 2 {
				fmt.Printf("%v: %v looping label\n", linestr(lineno), n)
			}
			e.loopDepth++ // 循环深度加一
		default:
			Fatalf("label missing tag")
		}
		n.Sym.Label = nil
	// if Ninit; Left { Nbody } else { Rlist }   122
	case OIF:
		e.discard(n.Left) // 这里Left表达式中不会有逃逸的情况
		e.block(n.Nbody)
		e.block(n.Rlist)
		// for Ninit; Left; Right { Nbody }  119, 120
	case OFOR, OFORUNTIL: // for Ninit; Left; Right { Nbody }
		e.loopDepth++     // 循环深度加一
		e.discard(n.Left) // 判断不会出现逃逸的情况
		e.stmt(n.Right)
		e.block(n.Nbody)
		e.loopDepth-- // 循环深度还原

	case ORANGE:
		// for List = range Right { Nbody }
		e.loopDepth++
		ks := e.addrs(n.List)
		e.block(n.Nbody)
		e.loopDepth--

		// Right is evaluated outside the loop.
		k := e.discardHole()
		if len(ks) >= 2 {
			if n.Right.Type.IsArray() {
				k = ks[1].note(n, "range")
			} else {
				k = ks[1].deref(n, "range-deref")
			}
		}
		e.expr(e.later(k), n.Right)

	case OSWITCH:
		typesw := n.Left != nil && n.Left.Op == OTYPESW

		var ks []EscHole
		for _, cas := range n.List.Slice() { // cases
			if typesw && n.Left.Left != nil {
				cv := cas.Rlist.First()
				k := e.dcl(cv) // type switch variables have no ODCL.
				if cv.Type.HasPointers() {
					ks = append(ks, k.dotType(cv.Type, cas, "switch case"))
				}
			}

			e.discards(cas.List)
			e.block(cas.Nbody)
		}

		if typesw {
			e.expr(e.teeHole(ks...), n.Left.Right)
		} else {
			e.discard(n.Left)
		}

	case OSELECT:
		for _, cas := range n.List.Slice() {
			e.stmt(cas.Left)
			e.block(cas.Nbody)
		}
	case OSELRECV:
		e.assign(n.Left, n.Right, "selrecv", n)
	case OSELRECV2:
		e.assign(n.Left, n.Right, "selrecv", n)
		e.assign(n.List.First(), nil, "selrecv", n)
	case ORECV:
		// TODO(mdempsky): Consider e.discard(n.Left).
		e.exprSkipInit(e.discardHole(), n) // already visited n.Ninit
	case OSEND:
		e.discard(n.Left)
		e.assignHeap(n.Right, "send", n)

	case OAS, OASOP:
		e.assign(n.Left, n.Right, "assign", n)

	case OAS2:
		for i, nl := range n.List.Slice() {
			e.assign(nl, n.Rlist.Index(i), "assign-pair", n)
		}

	case OAS2DOTTYPE: // v, ok = x.(type)
		e.assign(n.List.First(), n.Right, "assign-pair-dot-type", n)
		e.assign(n.List.Second(), nil, "assign-pair-dot-type", n)
	case OAS2MAPR: // v, ok = m[k]
		e.assign(n.List.First(), n.Right, "assign-pair-mapr", n)
		e.assign(n.List.Second(), nil, "assign-pair-mapr", n)
	case OAS2RECV: // v, ok = <-ch
		e.assign(n.List.First(), n.Right, "assign-pair-receive", n)
		e.assign(n.List.Second(), nil, "assign-pair-receive", n)

	case OAS2FUNC:
		e.stmts(n.Right.Ninit)
		e.call(e.addrs(n.List), n.Right, nil)
	case ORETURN:
		results := e.curfn.Type.Results().FieldSlice() // 获取函数声明时的返回列表
		for i, v := range n.List.Slice() {             // 遍历返回列表
			e.assign(asNode(results[i].Nname), v, "return", n)
		}
	case OCALLFUNC, OCALLMETH, OCALLINTER, OCLOSE, OCOPY, ODELETE, OPANIC, OPRINT, OPRINTN, ORECOVER:
		e.call(nil, n, nil)
	case OGO, ODEFER:
		e.stmts(n.Left.Ninit)
		e.call(nil, n.Left, n)

	case ORETJMP:
		// TODO(mdempsky): What do? esc.go just ignores it.
	}
}

func (e *Escape) stmts(l Nodes) {
	for _, n := range l.Slice() {
		e.stmt(n)
	}
}

// block is like stmts, but preserves loopDepth.
func (e *Escape) block(l Nodes) {
	old := e.loopDepth
	e.stmts(l)
	e.loopDepth = old
}

// expr models evaluating an expression n and flowing the result into
// hole k.
func (e *Escape) expr(k EscHole, n *Node) {
	if n == nil {
		return
	}
	e.stmts(n.Ninit)
	e.exprSkipInit(k, n)
}

func (e *Escape) exprSkipInit(k EscHole, n *Node) {
	if n == nil {
		return
	}

	lno := setlineno(n)
	defer func() {
		lineno = lno
	}()

	uintptrEscapesHack := k.uintptrEscapesHack
	k.uintptrEscapesHack = false

	if uintptrEscapesHack && n.Op == OCONVNOP && n.Left.Type.IsUnsafePtr() { // Type(Left) (type conversion, no effect),将unsafePointer强转为某个类型
		// nop
	} else if k.derefs >= 0 && !n.Type.HasPointers() { //	dst = n,如果dst对应的EscHole的derefs >= 0且n中没有指针,这种情况不需要记录数据流,因为这行代码不会导致逃逸
		k = e.discardHole() // blankLoc
	}

	switch n.Op {
	default:
		Fatalf("unexpected expr: %v", n)

	case OLITERAL, OGETG, OCLOSUREVAR, OTYPE: // literal, getg(), 闭包捕获的变量, 表示一个类型的节点
		// nop

	case ONAME:
		if n.Class() == PFUNC || n.Class() == PEXTERN { // n为全局函数或全局变量不记录
			return
		}
		e.flow(k, e.oldLoc(n)) // n为局部变量,记录数据流向k

	case OPLUS, ONEG, OBITNOT, ONOT: // 对一元表达式的处理,对于数据的一元操作不会改变数据的逃逸情况
		e.discard(n.Left) // 处理副作用并不记录数据的流向
	case OADD, OSUB, OOR, OXOR, OMUL, ODIV, OMOD, OLSH, ORSH, OAND, OANDNOT, OEQ, ONE, OLT, OLE, OGT, OGE, OANDAND, OOROR: // 二元操作类似一元操作
		e.discard(n.Left)  // 处理副作用并不记录数据的流向
		e.discard(n.Right) // 处理副作用并不记录数据的流向

	case OADDR: // &Left		dst = &Left, 这里用k.addr用来记录Left取一次引用给了dst
		e.expr(k.addr(n, "address-of"), n.Left) // "address-of"
	case ODEREF: // *Left
		e.expr(k.deref(n, "indirection"), n.Left) // "indirection"
	case ODOT, ODOTMETH, ODOTINTER: // Left.Sym (Left is of struct type), Left.Sym (Left is non-interface, Right is method name), Left.Sym (Left is interface, Right is method name)
		e.expr(k.note(n, "dot"), n.Left) // 处理left的数据流向
	case ODOTPTR: // Left.Sym (Left is of pointer to struct type)
		e.expr(k.deref(n, "dot of pointer"), n.Left) // "dot of pointer"
	case ODOTTYPE, ODOTTYPE2:
		e.expr(k.dotType(n.Type, n, "dot"), n.Left)
	case OINDEX: // Left[Right] (index of array or slice)
		if n.Left.Type.IsArray() { // 数组中存储的是值而切片中存储的是引用?????
			e.expr(k.note(n, "fixed-array-index-of"), n.Left)
		} else {
			// TODO(mdempsky): Fix why reason text.
			e.expr(k.deref(n, "dot of pointer"), n.Left) // 切片中有一个指针,需要对指针解引用
		}
		e.discard(n.Right) // 处理副作用并不记录数据的流向
	case OINDEXMAP: // Left[Right] (index of map)
		e.discard(n.Left)
		e.discard(n.Right)
	case OSLICE, OSLICEARR, OSLICE3, OSLICE3ARR, OSLICESTR: // Left[List[0] : List[1]] (Left is untypechecked or slice)
		e.expr(k.note(n, "slice"), n.Left)
		low, high, max := n.SliceBounds()
		e.discard(low)
		e.discard(high)
		e.discard(max)

	case OCONV, OCONVNOP: // Type(Left) (type conversion), Type(Left) (type conversion, no effect)
		if checkPtr(e.curfn, 2) && n.Type.Etype == TUNSAFEPTR && n.Left.Type.IsPtr() { // 将指针强转为unsafePointer的操作
			// When -d=checkptr=2 is enabled, treat
			// conversions to unsafe.Pointer as an
			// escaping operation. This allows better
			// runtime instrumentation, since we can more
			// easily detect object boundaries on the heap
			// than the stack.
			e.assignHeap(n.Left, "conversion to unsafe.Pointer", n) // 尝试让被强转的节点逃逸到堆
		} else if n.Type.Etype == TUNSAFEPTR && n.Left.Type.Etype == TUINTPTR { // 将uintptr类型强转为unsafePointer的操作
			e.unsafeValue(k, n.Left)
		} else {
			e.expr(k, n.Left)
		}
	case OCONVIFACE: // Type(Left) (type conversion, to interface)
		if !n.Left.Type.IsInterface() && !isdirectiface(n.Left.Type) { // 某个非interface类型强转为interface并且不是直接存储在interface的Data域中的,需要取地址
			k = e.spill(k, n)
		}
		e.expr(k.note(n, "interface-converted"), n.Left)

	case ORECV: // <-Left, 从管道中取数据与管道无任何关系,所以不必记录管道的数据流向
		e.discard(n.Left)

	case OCALLMETH, OCALLFUNC, OCALLINTER, OLEN, OCAP, OCOMPLEX, OREAL, OIMAG, OAPPEND, OCOPY:
		e.call([]EscHole{k}, n, nil)

	case ONEW: // variable = new(Type)
		e.spill(k, n)

	case OMAKESLICE:
		e.spill(k, n)
		e.discard(n.Left)
		e.discard(n.Right)
	case OMAKECHAN:
		e.discard(n.Left)
	case OMAKEMAP:
		e.spill(k, n)
		e.discard(n.Left)

	case ORECOVER:
		// nop

	case OCALLPART:
		// Flow the receiver argument to both the closure and
		// to the receiver parameter.

		closureK := e.spill(k, n)

		m := callpartMethod(n)

		// We don't know how the method value will be called
		// later, so conservatively assume the result
		// parameters all flow to the heap.
		//
		// TODO(mdempsky): Change ks into a callback, so that
		// we don't have to create this dummy slice?
		var ks []EscHole
		for i := m.Type.NumResults(); i > 0; i-- {
			ks = append(ks, e.heapHole())
		}
		paramK := e.tagHole(ks, asNode(m.Type.Nname()), m.Type.Recv())

		e.expr(e.teeHole(paramK, closureK), n.Left)

	case OPTRLIT:
		e.expr(e.spill(k, n), n.Left)

	case OARRAYLIT:
		for _, elt := range n.List.Slice() {
			if elt.Op == OKEY {
				elt = elt.Right
			}
			e.expr(k.note(n, "array literal element"), elt)
		}

	case OSLICELIT:
		k = e.spill(k, n)
		k.uintptrEscapesHack = uintptrEscapesHack // for ...uintptr parameters

		for _, elt := range n.List.Slice() {
			if elt.Op == OKEY {
				elt = elt.Right
			}
			e.expr(k.note(n, "slice-literal-element"), elt)
		}

	case OSTRUCTLIT:
		for _, elt := range n.List.Slice() {
			e.expr(k.note(n, "struct literal element"), elt.Left)
		}

	case OMAPLIT:
		e.spill(k, n)

		// Map keys and values are always stored in the heap.
		for _, elt := range n.List.Slice() {
			e.assignHeap(elt.Left, "map literal key", n)
			e.assignHeap(elt.Right, "map literal value", n)
		}

	case OCLOSURE:
		k = e.spill(k, n)

		// Link addresses of captured variables to closure.
		for _, v := range n.Func.Closure.Func.Cvars.Slice() {
			if v.Op == OXXX { // unnamed out argument; see dcl.go:/^funcargs
				continue
			}

			k := k
			if !v.Name.Byval() {
				k = k.addr(v, "reference")
			}

			e.expr(k.note(n, "captured by a closure"), v.Name.Defn)
		}

	case ORUNES2STR, OBYTES2STR, OSTR2RUNES, OSTR2BYTES, ORUNESTR:
		e.spill(k, n)
		e.discard(n.Left)

	case OADDSTR:
		e.spill(k, n)

		// Arguments of OADDSTR never escape;
		// runtime.concatstrings makes sure of that.
		e.discards(n.List)
	}
}

// unsafeValue evaluates a uintptr-typed arithmetic expression looking
// for conversions from an unsafe.Pointer.
func (e *Escape) unsafeValue(k EscHole, n *Node) {
	if n.Type.Etype != TUINTPTR {
		Fatalf("unexpected type %v for %v", n.Type, n)
	}

	e.stmts(n.Ninit)

	switch n.Op {
	case OCONV, OCONVNOP:
		if n.Left.Type.Etype == TUNSAFEPTR { // TUNSAFEPTR强转为TUINTPTR可能会逃逸
			e.expr(k, n.Left)
		} else {
			e.discard(n.Left)
		}
	case ODOTPTR: // Left.Sym (Left is of pointer to struct type)
		if isReflectHeaderDataField(n) {
			e.expr(k.deref(n, "reflect.Header.Data"), n.Left)
		} else {
			e.discard(n.Left)
		}
	case OPLUS, ONEG, OBITNOT: // 对TUINTPTR进行的一元运算
		e.unsafeValue(k, n.Left)
	case OADD, OSUB, OOR, OXOR, OMUL, ODIV, OMOD, OAND, OANDNOT:
		e.unsafeValue(k, n.Left)
		e.unsafeValue(k, n.Right)
	case OLSH, ORSH:
		e.unsafeValue(k, n.Left)
		// RHS need not be uintptr-typed (#32959) and can't meaningfully
		// flow pointers anyway.
		e.discard(n.Right)
	default:
		e.exprSkipInit(e.discardHole(), n)
	}
}

// discard evaluates an expression n for side-effects, but discards
// its value.
func (e *Escape) discard(n *Node) {
	e.expr(e.discardHole(), n)
}

func (e *Escape) discards(l Nodes) {
	for _, n := range l.Slice() {
		e.discard(n)
	}
}

// addr evaluates an addressable expression n and returns an EscHole
// that represents storing into the represented location.
func (e *Escape) addr(n *Node) EscHole {
	if n == nil || n.isBlank() {
		// Can happen at least in OSELRECV.
		// TODO(mdempsky): Anywhere else?
		return e.discardHole()
	}

	k := e.heapHole() // 默认为n分配在堆中

	switch n.Op {
	default:
		Fatalf("unexpected addr: %v", n)
	case ONAME:
		if n.Class() == PEXTERN { // global variable,对一个全局变量的赋值,那么认为逃逸到堆了
			break
		}
		k = e.oldLoc(n).asHole() // 直接返回已经记录的变量location并包装成EscHole结构体
	case ODOT: // Left.Sym (Left is of struct type)
		k = e.addr(n.Left) // 取结构体示例的location
	case OINDEX: // Left[Right] (index of array or slice)
		e.discard(n.Right) // Right必定为int类型,不会逃逸
		if n.Left.Type.IsArray() {
			k = e.addr(n.Left) // 是数组就取数组的location
		} else {
			e.discard(n.Left)
		}
	case ODEREF, ODOTPTR: // 操作解了一次引用,所以这个节点对逃逸分析无效
		e.discard(n)
	case OINDEXMAP: // Left[Right] (index of map)
		e.discard(n.Left)
		e.assignHeap(n.Right, "key of map put", n)
	}

	if !n.Type.HasPointers() { // n的类型中不包含堆指针
		k = e.discardHole() // 忽略这个数据流
	}

	return k
}

func (e *Escape) addrs(l Nodes) []EscHole {
	var ks []EscHole
	for _, n := range l.Slice() {
		ks = append(ks, e.addr(n))
	}
	return ks
}

// assign evaluates the assignment dst = src. where是dst与src的父级节点
func (e *Escape) assign(dst, src *Node, why string, where *Node) {
	// Filter out some no-op assignments for escape analysis.
	ignore := dst != nil && src != nil && isSelfAssign(dst, src) // 自己为自己赋值就为true
	if ignore && Debug['m'] != 0 {
		Warnl(where.Pos, "%v ignoring self-assignment in %S", funcSym(e.curfn), where)
	}

	k := e.addr(dst) // 计算并获取dst对应的EscHole
	if dst != nil && dst.Op == ODOTPTR && isReflectHeaderDataField(dst) {
		e.unsafeValue(e.heapHole().note(where, why), src)
	} else {
		if ignore { // 自己对自己赋值就忽略这个数据流
			k = e.discardHole()
		}
		e.expr(k.note(where, why), src) // 传入k与src,记录src流向了k
	}
}

func (e *Escape) assignHeap(src *Node, why string, where *Node) {
	e.expr(e.heapHole().note(where, why), src)
}

// call evaluates a call expressions, including builtin calls. ks
// should contain the holes representing where the function callee's
// results flows; where is the OGO/ODEFER context of the call, if any.
func (e *Escape) call(ks []EscHole, call, where *Node) {
	topLevelDefer := where != nil && where.Op == ODEFER && e.loopDepth == 1 // 是否为在函数最外层的defer调用
	if topLevelDefer {
		// force stack allocation of defer record, unless
		// open-coded defers are used (see ssa.go)
		where.Esc = EscNever
	}

	argument := func(k EscHole, arg *Node) {
		if topLevelDefer {
			// Top level defers arguments don't escape to
			// heap, but they do need to last until end of
			// function.
			k = e.later(k)
		} else if where != nil {
			k = e.heapHole()
		}

		e.expr(k.note(call, "call parameter"), arg)
	}

	switch call.Op {
	default:
		Fatalf("unexpected call op: %v", call.Op)

	case OCALLFUNC, OCALLMETH, OCALLINTER: // Left(List/Rlist) (function call f(args)), Left(List/Rlist) (direct method call x.Method(args)), Left(List/Rlist) (interface method call x.Method(args))
		fixVariadicCall(call) // 处理函数声明时存在可变参数但是调用时没有可变参数的情况,将实参构成一个切片

		// Pick out the function callee, if statically known.
		var fn *Node // 存储函数名代表的节点
		switch call.Op {
		case OCALLFUNC: // Left(List/Rlist) (function call f(args))
			if call.Left.Op == ONAME && call.Left.Class() == PFUNC {
				fn = call.Left
			} else if call.Left.Op == OCLOSURE {
				fn = call.Left.Func.Closure.Func.Nname
			}
		case OCALLMETH: // Left(List/Rlist) (direct method call x.Method(args))
			fn = asNode(call.Left.Type.FuncType().Nname)
		}

		fntype := call.Left.Type // 函数类型
		if fn != nil {           // 有名字的函数
			fntype = fn.Type
		}

		if ks != nil && fn != nil && e.inMutualBatch(fn) { // fn在递归调用分析中
			for i, result := range fn.Type.Results().FieldSlice() {
				e.expr(ks[i], asNode(result.Nname))
			}
		}

		if r := fntype.Recv(); r != nil { // 调用的函数存在receiver
			argument(e.tagHole(ks, fn, r), call.Left.Left)
		} else {
			// Evaluate callee function expression.
			argument(e.discardHole(), call.Left)
		}

		args := call.List.Slice()
		for i, param := range fntype.Params().FieldSlice() {
			argument(e.tagHole(ks, fn, param), args[i])
		}

	case OAPPEND:
		args := call.List.Slice()

		// Appendee slice may flow directly to the result, if
		// it has enough capacity. Alternatively, a new heap
		// slice might be allocated, and all slice elements
		// might flow to heap.
		appendeeK := ks[0]
		if args[0].Type.Elem().HasPointers() {
			appendeeK = e.teeHole(appendeeK, e.heapHole().deref(call, "appendee slice"))
		}
		argument(appendeeK, args[0])

		if call.IsDDD() {
			appendedK := e.discardHole()
			if args[1].Type.IsSlice() && args[1].Type.Elem().HasPointers() {
				appendedK = e.heapHole().deref(call, "appended slice...")
			}
			argument(appendedK, args[1])
		} else {
			for _, arg := range args[1:] {
				argument(e.heapHole(), arg)
			}
		}

	case OCOPY:
		argument(e.discardHole(), call.Left)

		copiedK := e.discardHole()
		if call.Right.Type.IsSlice() && call.Right.Type.Elem().HasPointers() {
			copiedK = e.heapHole().deref(call, "copied slice")
		}
		argument(copiedK, call.Right)

	case OPANIC:
		argument(e.heapHole(), call.Left)

	case OCOMPLEX:
		argument(e.discardHole(), call.Left)
		argument(e.discardHole(), call.Right)
	case ODELETE, OPRINT, OPRINTN, ORECOVER:
		for _, arg := range call.List.Slice() {
			argument(e.discardHole(), arg)
		}
	case OLEN, OCAP, OREAL, OIMAG, OCLOSE:
		argument(e.discardHole(), call.Left)
	}
}

// tagHole returns a hole for evaluating an argument passed to param.
// ks should contain the holes representing where the function
// callee's results flows. fn is the statically-known callee function,
// if any.
func (e *Escape) tagHole(ks []EscHole, fn *Node, param *types.Field) EscHole {
	// If this is a dynamic call, we can't rely on param.Note.
	if fn == nil {
		return e.heapHole()
	}

	if e.inMutualBatch(fn) { // fn在递归分析中
		return e.addr(asNode(param.Nname)) // 直接返回参数的地址表示的EscHole

	}

	// Call to previously tagged function.

	if param.Note == uintptrEscapesTag {
		k := e.heapHole()
		k.uintptrEscapesHack = true
		return k
	}

	var tagKs []EscHole

	esc := ParseLeaks(param.Note)
	if x := esc.Heap(); x >= 0 { // x >= 0表示参数的tag流向堆了
		tagKs = append(tagKs, e.heapHole().shift(x))
	}

	if ks != nil {
		for i := 0; i < numEscResults; i++ {
			if x := esc.Result(i); x >= 0 { // 第i个参数也记录了非esc:开头的tag
				tagKs = append(tagKs, ks[i].shift(x))
			}
		}
	}

	return e.teeHole(tagKs...) // 创建一个临时Location并记录数据流向所有的tagKs中的元素并返回这个新建的临时Location
}

// inMutualBatch reports whether function fn is in the batch of
// mutually recursive functions being analyzed. When this is true,
// fn has not yet been analyzed, so its parameters and results
// should be incorporated directly into the flow graph instead of
// relying on its escape analysis tagging.
func (e *Escape) inMutualBatch(fn *Node) bool {
	if fn.Name.Defn != nil && fn.Name.Defn.Esc < EscFuncTagged {
		if fn.Name.Defn.Esc == EscFuncUnknown {
			Fatalf("graph inconsistency")
		}
		return true
	}
	return false
}

// An EscHole represents a context for evaluation a Go
// expression. E.g., when evaluating p in "x = **p", we'd have a hole
// with dst==x and derefs==2.
type EscHole struct {
	dst    *EscLocation
	derefs int      // >= -1	表示需要解引用的次数   如果小于0表示取了地址   每次取变量地址中的值会将该成员加一
	notes  *EscNote // 是一个链表

	// uintptrEscapesHack indicates this context is evaluating an
	// argument for a //go:uintptrescapes function.
	uintptrEscapesHack bool
}

type EscNote struct {
	next  *EscNote // 链表中下一个EscNote指针
	where *Node    // 什么方式导致
	why   string
}

func (k EscHole) note(where *Node, why string) EscHole {
	if where == nil || why == "" {
		Fatalf("note: missing where/why")
	}
	if Debug['m'] >= 2 || logopt.Enabled() { // 开关开启之后才会记录
		k.notes = &EscNote{
			next:  k.notes,
			where: where,
			why:   why,
		}
	}
	return k
}

func (k EscHole) shift(delta int) EscHole {
	k.derefs += delta
	if k.derefs < -1 {
		Fatalf("derefs underflow: %v", k.derefs)
	}
	return k
}

func (k EscHole) deref(where *Node, why string) EscHole { return k.shift(1).note(where, why) }
func (k EscHole) addr(where *Node, why string) EscHole  { return k.shift(-1).note(where, why) }

func (k EscHole) dotType(t *types.Type, where *Node, why string) EscHole {
	// 对于类型断言来说,只有interface类型才可以断言为其他的类型
	if !t.IsInterface() && !isdirectiface(t) { // 不是强转为interface类型且不能直接存储在interface中(不是代表一个单独的指针)
		k = k.shift(1) // 这里也说明了interface中的data域存储的是实际类型元素的指针或者本身就代表一个指针而直接保存到interface中的
	}
	return k.note(where, why)
}

// teeHole returns a new hole that flows into each hole of ks,
// similar to the Unix tee(1) command.
func (e *Escape) teeHole(ks ...EscHole) EscHole {
	if len(ks) == 0 {
		return e.discardHole()
	}
	if len(ks) == 1 {
		return ks[0]
	}
	// TODO(mdempsky): Optimize if there's only one non-discard hole?

	// Given holes "l1 = _", "l2 = **_", "l3 = *_", ..., create a
	// new temporary location ltmp, wire it into place, and return
	// a hole for "ltmp = _".
	loc := e.newLoc(nil, true)
	for _, k := range ks {
		// N.B., "p = &q" and "p = &tmp; tmp = q" are not
		// semantically equivalent. To combine holes like "l1
		// = _" and "l2 = &_", we'd need to wire them as "l1 =
		// *ltmp" and "l2 = ltmp" and return "ltmp = &_"
		// instead.
		if k.derefs < 0 {
			Fatalf("teeHole: negative derefs")
		}

		e.flow(k, loc)
	}
	return loc.asHole()
}

// 记录n声明的循环深度
func (e *Escape) dcl(n *Node) EscHole {
	loc := e.oldLoc(n)
	loc.loopDepth = e.loopDepth // 记录变量所在的深度
	return loc.asHole()
}

// spill allocates a new location associated with expression n, flows
// its address to k, and returns a hole that flows values to it. It's
// intended for use with most expressions that allocate storage.
func (e *Escape) spill(k EscHole, n *Node) EscHole {
	loc := e.newLoc(n, true)
	e.flow(k.addr(n, "spill"), loc)
	return loc.asHole()
}

// later returns a new hole that flows into k, but some time later.
// Its main effect is to prevent immediate reuse of temporary
// variables introduced during Order.
func (e *Escape) later(k EscHole) EscHole {
	loc := e.newLoc(nil, false)
	e.flow(k, loc)
	return loc.asHole()
}

// canonicalNode returns the canonical *Node that n logically
// represents.
func canonicalNode(n *Node) *Node {
	if n != nil && n.Op == ONAME && n.Name.IsClosureVar() { // n是否为闭包变量
		n = n.Name.Defn
		if n.Name.IsClosureVar() {
			Fatalf("still closure var")
		}
	}

	return n
}

func (e *Escape) newLoc(n *Node, transient bool) *EscLocation {
	if e.curfn == nil {
		Fatalf("e.curfn isn't set")
	}
	if n != nil && n.Type != nil && n.Type.NotInHeap() {
		yyerrorl(n.Pos, "%v is incomplete (or unallocatable); stack allocation disallowed", n.Type)
	}

	n = canonicalNode(n) // 如果是闭包变量,获取这个变量最初声明的节点,否则返回n
	loc := &EscLocation{
		n:         n,
		curfn:     e.curfn,
		loopDepth: e.loopDepth,
		transient: transient,
	}
	e.allLocs = append(e.allLocs, loc)
	if n != nil {
		if n.Op == ONAME && n.Name.Curfn != e.curfn {
			Fatalf("curfn mismatch: %v != %v", n.Name.Curfn, e.curfn)
		}

		if n.HasOpt() {
			Fatalf("%v already has a location", n)
		}
		n.SetOpt(loc) // n.E = loc

		if mustHeapAlloc(n) { // 只能通过堆申请内存
			why := "too large for stack"
			if n.Op == OMAKESLICE && (!Isconst(n.Left, CTINT) || !Isconst(n.Right, CTINT)) {
				why = "non-constant size"
			}
			e.flow(e.heapHole().addr(n, why), loc) // 这里使用addr只是为了确保将loc逃逸而使用的方式,loc数据流向堆,逃逸
		}
	}
	return loc
}

func (e *Escape) oldLoc(n *Node) *EscLocation {
	n = canonicalNode(n) // 获取原始节点
	return n.Opt().(*EscLocation)
}

func (l *EscLocation) asHole() EscHole {
	return EscHole{dst: l}
}

// 处理从src流向k.dst的操作
func (e *Escape) flow(k EscHole, src *EscLocation) {
	dst := k.dst            // 数据流向的EscLocation结构体
	if dst == &e.blankLoc { // 表示没有逃逸,直接返回
		return
	}
	if dst == src && k.derefs >= 0 { // dst = dst, dst = *dst, ...		这种情况不会导致dst逃逸,没有记录数据流的必要
		return
	}
	if dst.escapes && k.derefs < 0 { // 这行判断表示在dst已经确认是逃逸的情况下执行了dst = &src,堆中的某个指针不应该指向栈上的内存,所以src也要逃逸
		if Debug['m'] >= 2 || logopt.Enabled() {
			pos := linestr(src.n.Pos)
			if Debug['m'] >= 2 {
				fmt.Printf("%s: %v escapes to heap:\n", pos, src.n)
			}
			explanation := e.explainFlow(pos, dst, src, k.derefs, k.notes, []*logopt.LoggedOpt{})
			if logopt.Enabled() {
				logopt.LogOpt(src.n.Pos, "escapes", "escape", e.curfn.funcname(), fmt.Sprintf("%v escapes to heap", src.n), explanation)
			}

		}
		src.escapes = true // 标记src也逃逸了
		return
	}

	// TODO(mdempsky): Deduplicate edges?
	dst.edges = append(dst.edges, EscEdge{src: src, derefs: k.derefs, notes: k.notes}) // 记录src流向dst
}

func (e *Escape) heapHole() EscHole    { return e.heapLoc.asHole() }
func (e *Escape) discardHole() EscHole { return e.blankLoc.asHole() }

// walkAll computes the minimal dereferences between all pairs of
// locations.
func (e *Escape) walkAll() {
	// We use a work queue to keep track of locations that we need
	// to visit, and repeatedly walk until we reach a fixed point.
	//
	// We walk once from each location (including the heap), and
	// then re-enqueue each location on its transition from
	// transient->!transient and !escapes->escapes, which can each
	// happen at most once. So we take Θ(len(e.allLocs)) walks.

	// LIFO queue, has enough room for e.allLocs and e.heapLoc.
	todo := make([]*EscLocation, 0, len(e.allLocs)+1)
	enqueue := func(loc *EscLocation) {
		if !loc.queued {
			todo = append(todo, loc)
			loc.queued = true
		}
	}

	for _, loc := range e.allLocs { // 所有的EscLocation加入队列
		enqueue(loc)
	}
	enqueue(&e.heapLoc) // e.heapLoc加入队列

	var walkgen uint32  // 记录walk的次数
	for len(todo) > 0 { // 遍历所有的EscLocation
		root := todo[len(todo)-1] // 获取队列中最后一项,如果是第一次进入循环,那么这个root应该是heapLoc
		todo = todo[:len(todo)-1]
		root.queued = false // 标记root已经不在队列中了

		walkgen++
		e.walkOne(root, walkgen, enqueue)
	}
}

// walkOne computes the minimal number of dereferences from root to
// all other locations.
func (e *Escape) walkOne(root *EscLocation, walkgen uint32, enqueue func(*EscLocation)) {
	// The data flow graph has negative edges (from addressing
	// operations), so we use the Bellman-Ford algorithm. However,
	// we don't have to worry about infinite negative cycles since
	// we bound intermediate dereference counts to 0.

	root.walkgen = walkgen
	root.derefs = 0 // 将引用设置为0
	root.dst = nil

	todo := []*EscLocation{root} // LIFO queue	这个队列中保存的都是未逃逸的待分析的EscLocation,除了root
	for len(todo) > 0 {          // 以root为根不停遍历,找到所有最终流向root的节点
		l := todo[len(todo)-1] // 弹出最后一项
		todo = todo[:len(todo)-1]

		base := l.derefs // 获取引用次数

		// If l.derefs < 0, then l's address flows to root.
		addressOf := base < 0
		if addressOf { // If l.derefs < 0
			// For a flow path like "root = &l; l = x",
			// l's address flows to root, but x's does
			// not. We recognize this by lower bounding
			// base at 0.
			base = 0

			// If l's address flows to a non-transient
			// location, then l can't be transiently
			// allocated.
			if !root.transient && l.transient {
				l.transient = false
				enqueue(l) // 将l加入到外层队列进行循环
			}
		}

		if e.outlives(root, l) { // 判断root的生命周期是否比l长,这种情况下l可能会逃逸
			// l's value flows to root. If l is a function
			// parameter and root is the heap or a
			// corresponding result parameter, then record
			// that value flow for tagging the function
			// later.
			if l.isName(PPARAM) { // l是入参变量,表示一个函数的参数的数据流向了一个返回参数且返回参数包含指针
				if (logopt.Enabled() || Debug['m'] >= 2) && !l.escapes {
					if Debug['m'] >= 2 {
						fmt.Printf("%s: parameter %v leaks to %s with derefs=%d:\n", linestr(l.n.Pos), l.n, e.explainLoc(root), base)
					}
					explanation := e.explainPath(root, l)
					if logopt.Enabled() {
						logopt.LogOpt(l.n.Pos, "leak", "escape", e.curfn.funcname(),
							fmt.Sprintf("parameter %v leaks to %s with derefs=%d", l.n, e.explainLoc(root), base), explanation)
					}
				}
				l.leakTo(root, base)
			}

			// If l's address flows somewhere that
			// outlives it, then l needs to be heap
			// allocated.
			if addressOf && !l.escapes { // l未逃逸且l的地址流向了一个比l自身存活时间久的变量中,那么l必须在堆中分配内存
				if logopt.Enabled() || Debug['m'] >= 2 {
					if Debug['m'] >= 2 {
						fmt.Printf("%s: %v escapes to heap:\n", linestr(l.n.Pos), l.n)
					}
					explanation := e.explainPath(root, l)
					if logopt.Enabled() {
						logopt.LogOpt(l.n.Pos, "escape", "escape", e.curfn.funcname(), fmt.Sprintf("%v escapes to heap", l.n), explanation)
					}
				}
				l.escapes = true
				enqueue(l) // l逃逸了就添加到外部队列
				continue
			}
		}

		for i, edge := range l.edges { // 遍历所有流向l的边
			if edge.src.escapes { // 已经逃逸的不再分析
				continue
			}
			derefs := base + edge.derefs                                 // 求出src的实际解引用次数,解引用多少次后赋值给root
			if edge.src.walkgen != walkgen || edge.src.derefs > derefs { // 保存src解引用次数最少到达droot的情况
				edge.src.walkgen = walkgen    // 设置为相同的walkgen,再次遍历到时会跳过
				edge.src.derefs = derefs      // 保存src赋值到root的最小的解引用次数
				edge.src.dst = l              // 设置src的最小解引用次数数据流向的目标为l
				edge.src.dstEdgeIdx = i       // 设置src属于其dst在数据流边中的index
				todo = append(todo, edge.src) // 添加到内部队列进行循环
			}
		}
	}
}

// explainPath prints an explanation of how src flows to the walk root.
func (e *Escape) explainPath(root, src *EscLocation) []*logopt.LoggedOpt {
	visited := make(map[*EscLocation]bool)
	pos := linestr(src.n.Pos)
	var explanation []*logopt.LoggedOpt
	for {
		// Prevent infinite loop.
		if visited[src] { // src遍历过了就跳出循环
			if Debug['m'] >= 2 {
				fmt.Printf("%s:   warning: truncated explanation due to assignment cycle; see golang.org/issue/35518\n", pos)
			}
			break
		}
		visited[src] = true // 标记src遍历过了就跳出
		dst := src.dst
		edge := &dst.edges[src.dstEdgeIdx]
		if edge.src != src {
			Fatalf("path inconsistency: %v != %v", edge.src, src)
		}

		explanation = e.explainFlow(pos, dst, src, edge.derefs, edge.notes, explanation)

		if dst == root {
			break
		}
		src = dst
	}

	return explanation
}

func (e *Escape) explainFlow(pos string, dst, srcloc *EscLocation, derefs int, notes *EscNote, explanation []*logopt.LoggedOpt) []*logopt.LoggedOpt {
	ops := "&"
	if derefs >= 0 {
		ops = strings.Repeat("*", derefs)
	}
	print := Debug['m'] >= 2

	flow := fmt.Sprintf("   flow: %s = %s%v:", e.explainLoc(dst), ops, e.explainLoc(srcloc))
	if print {
		fmt.Printf("%s:%s\n", pos, flow)
	}
	if logopt.Enabled() {
		var epos src.XPos
		if notes != nil {
			epos = notes.where.Pos
		} else if srcloc != nil && srcloc.n != nil {
			epos = srcloc.n.Pos
		}
		explanation = append(explanation, logopt.NewLoggedOpt(epos, "escflow", "escape", e.curfn.funcname(), flow))
	}

	for note := notes; note != nil; note = note.next {
		if print {
			fmt.Printf("%s:     from %v (%v) at %s\n", pos, note.where, note.why, linestr(note.where.Pos))
		}
		if logopt.Enabled() {
			explanation = append(explanation, logopt.NewLoggedOpt(note.where.Pos, "escflow", "escape", e.curfn.funcname(),
				fmt.Sprintf("     from %v (%v)", note.where, note.why)))
		}
	}
	return explanation
}

func (e *Escape) explainLoc(l *EscLocation) string {
	if l == &e.heapLoc {
		return "{heap}"
	}
	if l.n == nil {
		// TODO(mdempsky): Omit entirely.
		return "{temp}"
	}
	if l.n.Op == ONAME {
		return fmt.Sprintf("%v", l.n)
	}
	return fmt.Sprintf("{storage for %v}", l.n)
}

// outlives reports whether values stored in l may survive beyond
// other's lifetime if stack allocated.
func (e *Escape) outlives(l, other *EscLocation) bool {
	// The heap outlives everything.
	if l.escapes { // l逃逸了
		return true
	}

	// We don't know what callers do with returned values, so
	// pessimistically we need to assume they flow to the heap and
	// outlive everything too.
	if l.isName(PPARAMOUT) { // 返回值变量
		// Exception: Directly called closures can return
		// locations allocated outside of them without forcing
		// them to the heap. For example:
		//
		//    var u int  // okay to stack allocate
		//    *(func() *int { return &u }()) = 42
		if containsClosure(other.curfn, l.curfn) && l.curfn.Func.Closure.Func.Top&ctxCallee != 0 {
			return false
		}

		return true
	}

	// If l and other are within the same function, then l
	// outlives other if it was declared outside other's loop
	// scope. For example:
	//
	//    var l *int
	//    for {
	//        l = new(int)
	//    }
	if l.curfn == other.curfn && l.loopDepth < other.loopDepth {
		return true
	}

	// If other is declared within a child closure of where l is
	// declared, then l outlives it. For example:
	//
	//    var l *int
	//    func() {
	//        l = new(int)
	//    }
	if containsClosure(l.curfn, other.curfn) {
		return true
	}

	return false
}

// containsClosure reports whether c is a closure contained within f.
func containsClosure(f, c *Node) bool {
	if f.Op != ODCLFUNC || c.Op != ODCLFUNC {
		Fatalf("bad containsClosure: %v, %v", f, c)
	}

	// Common case.
	if f == c {
		return false
	}

	// Closures within function Foo are named like "Foo.funcN..."
	// TODO(mdempsky): Better way to recognize this.
	fn := f.Func.Nname.Sym.Name
	cn := c.Func.Nname.Sym.Name
	return len(cn) > len(fn) && cn[:len(fn)] == fn && cn[len(fn)] == '.'
}

// leak records that parameter l leaks to sink.
func (l *EscLocation) leakTo(sink *EscLocation, derefs int) {
	// If sink is a result parameter and we can fit return bits
	// into the escape analysis tag, then record a return leak.
	if sink.isName(PPARAMOUT) && sink.curfn == l.curfn { // sink是一个返回参数且sink与l在一个函数中
		// TODO(mdempsky): Eliminate dependency on Vargen here.
		ri := int(sink.n.Name.Vargen) - 1 // sink这个返回值在返回值列表中的index
		if ri < numEscResults {
			// Leak to result parameter.
			l.paramEsc.AddResult(ri, derefs)
			return
		}
	}

	// Otherwise, record as heap leak.
	l.paramEsc.AddHeap(derefs)
}

func (e *Escape) finish(fns []*Node) {
	// Record parameter tags for package export data.
	for _, fn := range fns {
		fn.Esc = EscFuncTagged

		narg := 0                               // 记录所有函数中拥有的recv以及入参总数
		for _, fs := range &types.RecvsParams { // 获取recv与获取参数的两个函数
			for _, f := range fs(fn.Type).Fields().Slice() { // 遍历函数的所有recv和params
				narg++
				f.Note = e.paramTag(fn, narg, f)
			}
		}
	}

	for _, loc := range e.allLocs {
		n := loc.n // 获取节点
		if n == nil {
			continue
		}
		n.SetOpt(nil)

		// Update n.Esc based on escape analysis results.

		if loc.escapes { // 该变量逃逸了
			if n.Op != ONAME {
				if Debug['m'] != 0 {
					Warnl(n.Pos, "%S escapes to heap", n)
				}
				if logopt.Enabled() {
					logopt.LogOpt(n.Pos, "escape", "escape", e.curfn.funcname())
				}
			}
			n.Esc = EscHeap
			addrescapes(n)
		} else {
			if Debug['m'] != 0 && n.Op != ONAME {
				Warnl(n.Pos, "%S does not escape", n)
			}
			n.Esc = EscNone
			if loc.transient { // transient为true时表示函数就是变量的生命周期
				n.SetTransient(true) // 节点设置transient为true
			}
		}
	}
}

func (l *EscLocation) isName(c Class) bool {
	return l.n != nil && l.n.Op == ONAME && l.n.Class() == c
}

const numEscResults = 7

// An EscLeaks represents a set of assignment flows from a parameter
// to the heap or to any of its function's (first numEscResults)
// result parameters.
type EscLeaks [1 + numEscResults]uint8

// Empty reports whether l is an empty set (i.e., no assignment flows).
func (l EscLeaks) Empty() bool { return l == EscLeaks{} }

// Heap returns the minimum deref count of any assignment flow from l
// to the heap. If no such flows exist, Heap returns -1.
func (l EscLeaks) Heap() int { return l.get(0) }

// Result returns the minimum deref count of any assignment flow from
// l to its function's i'th result parameter. If no such flows exist,
// Result returns -1.
func (l EscLeaks) Result(i int) int { return l.get(1 + i) } // 从第一个开始存储函数的第一个返回参数

// AddHeap adds an assignment flow from l to the heap.
func (l *EscLeaks) AddHeap(derefs int) { l.add(0, derefs) }

// AddResult adds an assignment flow from l to its function's i'th
// result parameter.
func (l *EscLeaks) AddResult(i, derefs int) { l.add(1+i, derefs) }

func (l *EscLeaks) setResult(i, derefs int) { l.set(1+i, derefs) }

func (l EscLeaks) get(i int) int { return int(l[i]) - 1 } // 返回derefs-1的值

func (l *EscLeaks) add(i, derefs int) {
	if old := l.get(i); old < 0 || derefs < old {
		l.set(i, derefs)
	}
}

func (l *EscLeaks) set(i, derefs int) {
	v := derefs + 1 // 将derefs+1,在get时会减一
	if v < 0 {
		Fatalf("invalid derefs count: %v", derefs)
	}
	if v > math.MaxUint8 {
		v = math.MaxUint8
	}

	l[i] = uint8(v)
}

// Optimize removes result flow paths that are equal in length or
// longer than the shortest heap flow path.
func (l *EscLeaks) Optimize() {
	// If we have a path to the heap, then there's no use in
	// keeping equal or longer paths elsewhere.
	if x := l.Heap(); x >= 0 {
		for i := 0; i < numEscResults; i++ {
			if l.Result(i) >= x {
				l.setResult(i, -1)
			}
		}
	}
}

var leakTagCache = map[EscLeaks]string{} // 一个保存参数Tag的缓冲空间

// Encode converts l into a binary string for export data.
func (l EscLeaks) Encode() string {
	if l.Heap() == 0 {
		// Space optimization: empty string encodes more
		// efficiently in export data.
		return ""
	}
	if s, ok := leakTagCache[l]; ok {
		return s
	}

	n := len(l)
	for n > 0 && l[n-1] == 0 { // 该循环从后向前找到一个已用位置
		n--
	}
	s := "esc:" + string(l[:n])
	leakTagCache[l] = s
	return s
}

// ParseLeaks parses a binary string representing an EscLeaks.
func ParseLeaks(s string) EscLeaks {
	var l EscLeaks
	if !strings.HasPrefix(s, "esc:") { // 参数的tag不以esc:开头
		l.AddHeap(0)
		return l
	}
	copy(l[:], s[4:])
	return l
}

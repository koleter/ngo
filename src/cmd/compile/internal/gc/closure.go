// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import (
	"cmd/compile/internal/syntax"
	"cmd/compile/internal/types"
	"fmt"
)

func (p *noder) funcLit(expr *syntax.FuncLit) *Node {
	xtype := p.typeExpr(expr.Type)	// 构建函数类型节点
	ntype := p.typeExpr(expr.Type)	// 构建函数类型节点

	xfunc := p.nod(expr, ODCLFUNC, nil, nil)	// 创建一个函数声明节点
	xfunc.Func.SetIsHiddenClosure(Curfn != nil)		// 当这个函数字面量在一个函数中定义,说明这个函数是一个闭包函数
	xfunc.Func.Nname = newfuncnamel(p.pos(expr), nblank.Sym) // filled in by typecheckclosure	创建一个代表函数名的节点
	xfunc.Func.Nname.Name.Param.Ntype = xtype	// 记录其函数声明的函数类型
	xfunc.Func.Nname.Name.Defn = xfunc	// 函数名节点指向其函数声明

	clo := p.nod(expr, OCLOSURE, nil, nil)	// 创建一个闭包节点
	clo.Func.Ntype = ntype	// 赋予闭包函数类型节点

	xfunc.Func.Closure = clo	// 将函数声明与其闭包对应
	clo.Func.Closure = xfunc	// 将函数声明与其闭包对应

	p.funcBody(xfunc, expr.Body)	// 将函数体中的语法分析树转为抽象语法树

	// closure-specific variables are hanging off the
	// ordinary ones in the symbol table; see oldname.
	// unhook them.
	// make the list of pointers for the closure call.
	for _, v := range xfunc.Func.Cvars.Slice() {	// 此时Curfn已经从f4变成了f3
		// Unlink from v1; see comment in syntax.go type Param for these fields.
		v1 := v.Name.Defn	// 找到最外层的局部变量
		v1.Name.Param.Innermost = v.Name.Param.Outer	// Innermost指向被捕获变量外面一层的变量

		// If the closure usage of v is not dense,
		// we need to make it dense; now that we're out
		// of the function in which v appeared,
		// look up v.Sym in the enclosing function
		// and keep it around for use in the compiled code.
		//
		// That is, suppose we just finished parsing the innermost
		// closure f4 in this code:
		//
		//	func f() {
		//		v := 1
		//		func() { // f2
		//			use(v)
		//			func() { // f3
		//				func() { // f4
		//					use(v)
		//				}()
		//			}()
		//		}()
		//	}
		//
		// At this point v.Outer is f2's v; there is no f3's v.
		// To construct the closure f4 from within f3,
		// we need to use f3's v and in this case we need to create f3's v.
		// We are now in the context of f3, so calling oldname(v.Sym)
		// obtains f3's v, creating it if necessary (as it is in the example).
		//
		// capturevars will decide whether to use v directly or &v.
		v.Name.Param.Outer = oldname(v.Sym)	// 如上,当前在f4中,需要在f3中也添加闭包变量
	}

	return clo
}

func typecheckclosure(clo *Node, top int) {
	xfunc := clo.Func.Closure	// 获取包含闭包的函数
	// Set current associated iota value, so iota can be used inside
	// function in ConstSpec, see issue #22344
	if x := getIotaValue(); x >= 0 {
		xfunc.SetIota(x)
	}

	clo.Func.Ntype = typecheck(clo.Func.Ntype, ctxType)	// 检查函数的类型
	clo.Type = clo.Func.Ntype.Type
	clo.Func.Top = top

	// Do not typecheck xfunc twice, otherwise, we will end up pushing
	// xfunc to xtop multiple times, causing initLSym called twice.
	// See #30709
	if xfunc.Typecheck() == 1 {	// 表示xfunc的类型已经检查过了
		return
	}

	for _, ln := range xfunc.Func.Cvars.Slice() {	// 遍历闭包函数引用的局部变量
		n := ln.Name.Defn	
		if !n.Name.Captured() {
			n.Name.SetCaptured(true)
			if n.Name.Decldepth == 0 {
				Fatalf("typecheckclosure: var %S does not have decldepth assigned", n)
			}

			// Ignore assignments to the variable in straightline code
			// preceding the first capturing by a closure.
			if n.Name.Decldepth == decldepth {	// 表示在闭包中又声明了该变量
				n.Name.SetAssigned(false)	// 忽略闭包中的赋值操作
			}
		}
	}

	xfunc.Func.Nname.Sym = closurename(Curfn)	// 为闭包创建一个唯一的函数名
	disableExport(xfunc.Func.Nname.Sym)
	declare(xfunc.Func.Nname, PFUNC)
	xfunc = typecheck(xfunc, ctxStmt)

	// Type check the body now, but only if we're inside a function.
	// At top level (in a variable initialization: curfn==nil) we're not
	// ready to type check code yet; we'll check it later, because the
	// underlying closure function we create is added to xtop.
	if Curfn != nil && clo.Type != nil {
		oldfn := Curfn
		Curfn = xfunc
		olddd := decldepth
		decldepth = 1
		typecheckslice(xfunc.Nbody.Slice(), ctxStmt)
		decldepth = olddd
		Curfn = oldfn
	}

	xtop = append(xtop, xfunc)	// 闭包放到xtop中
}

// globClosgen is like Func.Closgen, but for the global scope.
var globClosgen int

// closurename generates a new unique name for a closure within
// outerfunc.
func closurename(outerfunc *Node) *types.Sym {
	outer := "glob."
	prefix := "func"
	gen := &globClosgen

	if outerfunc != nil {
		if outerfunc.Func.Closure != nil {
			prefix = ""
		}

		outer = outerfunc.funcname()	// 外层函数的函数名

		// There may be multiple functions named "_". In those
		// cases, we can't use their individual Closgens as it
		// would lead to name clashes.
		if !outerfunc.Func.Nname.isBlank() {
			gen = &outerfunc.Func.Closgen
		}
	}

	*gen++
	return lookup(fmt.Sprintf("%s.%s%d", outer, prefix, *gen))
}

// capturevarscomplete is set to true when the capturevars phase is done.
var capturevarscomplete bool

// capturevars is called in a separate phase after all typechecking is done.
// It decides whether each variable captured by a closure should be captured
// by value or by reference.
// We use value capturing for values <= 128 bytes that are never reassigned
// after capturing (effectively constant).
func capturevars(xfunc *Node) {
	lno := lineno
	lineno = xfunc.Pos

	clo := xfunc.Func.Closure	// 获取函数中的闭包
	cvars := xfunc.Func.Cvars.Slice()	// 用于被闭包捕获的变量
	out := cvars[:0]
	for _, v := range cvars {
		if v.Type == nil {
			// If v.Type is nil, it means v looked like it
			// was going to be used in the closure, but
			// isn't. This happens in struct literals like
			// s{f: x} where we can't distinguish whether
			// f is a field identifier or expression until
			// resolving s.
			continue
		}
		out = append(out, v)

		// type check the & of closed variables outside the closure,
		// so that the outer frame also grabs them and knows they escape.
		dowidth(v.Type)

		outer := v.Name.Param.Outer	// 获取被引用的外层变量
		outermost := v.Name.Defn	// 获取被引用的最外层变量

		// out parameters will be assigned to implicitly upon return.
		// 最外层的变量不是出参且本身没有被取地址且没有进行过赋值操作
		if outermost.Class() != PPARAMOUT && !outermost.Name.Addrtaken() && !outermost.Name.Assigned() && v.Type.Width <= 128 {
			v.Name.SetByval(true)	// 当前这个被捕获的变量通过值传递
		} else {
			outermost.Name.SetAddrtaken(true)	// 标记最外层的变量被取地址了
			outer = nod(OADDR, outer, nil)	// 取外层变量的地址
		}

		if Debug['m'] > 1 {
			var name *types.Sym
			if v.Name.Curfn != nil && v.Name.Curfn.Func.Nname != nil {
				name = v.Name.Curfn.Func.Nname.Sym
			}
			how := "ref"
			if v.Name.Byval() {
				how = "value"
			}
			Warnl(v.Pos, "%v capturing by %s: %v (addr=%v assign=%v width=%d)", name, how, v.Sym, outermost.Name.Addrtaken(), outermost.Name.Assigned(), int32(v.Type.Width))
		}

		outer = typecheck(outer, ctxExpr)
		clo.Func.Enter.Append(outer)
	}

	xfunc.Func.Cvars.Set(out)
	lineno = lno
}

// transformclosure is called in a separate phase after escape analysis.
// It transform closure bodies to properly reference captured variables.
func transformclosure(xfunc *Node) {
	lno := lineno
	lineno = xfunc.Pos
	clo := xfunc.Func.Closure	// 获取闭包函数

	if clo.Func.Top&ctxCallee != 0 {	// 闭包函数直接调用
		// If the closure is directly called, we transform it to a plain function call
		// with variables passed as args. This avoids allocation of a closure object.
		// Here we do only a part of the transformation. Walk of OCALLFUNC(OCLOSURE)
		// will complete the transformation later.
		// For illustration, the following closure:
		//	func(a int) {
		//		println(byval)
		//		byref++
		//	}(42)
		// becomes:
		//	func(byval int, &byref *int, a int) {
		//		println(byval)
		//		(*&byref)++
		//	}(byval, &byref, 42)

		// f is ONAME of the actual function.
		f := xfunc.Func.Nname	// 获取函数名节点

		// We are going to insert captured variables before input args.
		var params []*types.Field
		var decls []*Node
		for _, v := range xfunc.Func.Cvars.Slice() {	// 遍历闭包变量
			if !v.Name.Byval() {	// 不是值传递
				// If v of type T is captured by reference,
				// we introduce function param &v *T
				// and v remains PAUTOHEAP with &v heapaddr
				// (accesses will implicitly deref &v).
				addr := newname(lookup("&" + v.Sym.Name))
				addr.Type = types.NewPtr(v.Type)
				v.Name.Param.Heapaddr = addr
				v = addr
			}

			v.SetClass(PPARAM)
			decls = append(decls, v)

			fld := types.NewField()
			fld.Nname = asTypesNode(v)
			fld.Type = v.Type
			fld.Sym = v.Sym
			params = append(params, fld)
		}

		if len(params) > 0 {
			// Prepend params and decls.
			f.Type.Params().SetFields(append(params, f.Type.Params().FieldSlice()...))
			xfunc.Func.Dcl = append(decls, xfunc.Func.Dcl...)
		}

		dowidth(f.Type)
		xfunc.Type = f.Type // update type of ODCLFUNC
	} else {
		// The closure is not called, so it is going to stay as closure.
		var body []*Node
		offset := int64(Widthptr)
		for _, v := range xfunc.Func.Cvars.Slice() {	// 遍历闭包变量
			// cv refers to the field inside of closure OSTRUCTLIT.
			cv := nod(OCLOSUREVAR, nil, nil)

			cv.Type = v.Type
			if !v.Name.Byval() {	// 引用传参
				cv.Type = types.NewPtr(v.Type)
			}
			offset = Rnd(offset, int64(cv.Type.Align))
			cv.Xoffset = offset
			offset += cv.Type.Width

			if v.Name.Byval() && v.Type.Width <= int64(2*Widthptr) {
				// If it is a small variable captured by value, downgrade it to PAUTO.
				v.SetClass(PAUTO)
				xfunc.Func.Dcl = append(xfunc.Func.Dcl, v)
				body = append(body, nod(OAS, v, cv))
			} else {
				// Declare variable holding addresses taken from closure
				// and initialize in entry prologue.
				addr := newname(lookup("&" + v.Sym.Name))
				addr.Type = types.NewPtr(v.Type)
				addr.SetClass(PAUTO)
				addr.Name.SetUsed(true)
				addr.Name.Curfn = xfunc
				xfunc.Func.Dcl = append(xfunc.Func.Dcl, addr)
				v.Name.Param.Heapaddr = addr
				if v.Name.Byval() {		// 如果为true，表示当前的v是因为类型宽度过大才使用指针进行传递的
					cv = nod(OADDR, cv, nil)
				}
				body = append(body, nod(OAS, addr, cv))
			}
		}

		if len(body) > 0 {
			typecheckslice(body, ctxStmt)
			xfunc.Func.Enter.Set(body)
			xfunc.Func.SetNeedctxt(true)
		}
	}

	lineno = lno
}

// hasemptycvars reports whether closure clo has an
// empty list of captured vars.
func hasemptycvars(clo *Node) bool {
	xfunc := clo.Func.Closure
	return xfunc.Func.Cvars.Len() == 0
}

// closuredebugruntimecheck applies boilerplate checks for debug flags
// and compiling runtime
func closuredebugruntimecheck(clo *Node) {
	if Debug_closure > 0 {
		xfunc := clo.Func.Closure
		if clo.Esc == EscHeap {
			Warnl(clo.Pos, "heap closure, captured vars = %v", xfunc.Func.Cvars)
		} else {
			Warnl(clo.Pos, "stack closure, captured vars = %v", xfunc.Func.Cvars)
		}
	}
	if compiling_runtime && clo.Esc == EscHeap {
		yyerrorl(clo.Pos, "heap-allocated closure, not allowed in runtime")
	}
}

// closureType returns the struct type used to hold all the information
// needed in the closure for clo (clo must be a OCLOSURE node).
// The address of a variable of the returned type can be cast to a func.
func closureType(clo *Node) *types.Type {
	// Create closure in the form of a composite literal.
	// supposing the closure captures an int i and a string s
	// and has one float64 argument and no results,
	// the generated code looks like:
	//
	//	clos = &struct{.F uintptr; i *int; s *string}{func.1, &i, &s}
	//
	// The use of the struct provides type information to the garbage
	// collector so that it can walk the closure. We could use (in this case)
	// [3]unsafe.Pointer instead, but that would leave the gc in the dark.
	// The information appears in the binary in the form of type descriptors;
	// the struct is unnamed so that closures in multiple packages with the
	// same struct type can share the descriptor.
	fields := []*Node{
		namedfield(".F", types.Types[TUINTPTR]),
	}
	for _, v := range clo.Func.Closure.Func.Cvars.Slice() {	// 遍历所有的闭包变量
		typ := v.Type	// 闭包变量的类型
		if !v.Name.Byval() {	// 闭包变量通过指针引用
			typ = types.NewPtr(typ)	// 创建闭包变量的指针
		}
		fields = append(fields, symfield(v.Sym, typ))	// 将闭包变量添加到fields中
	}
	typ := tostruct(fields)	// 将fields转换为一个结构体
	typ.SetNoalg(true)
	return typ
}

func walkclosure(clo *Node, init *Nodes) *Node {
	xfunc := clo.Func.Closure	// 闭包外的函数声明

	// If no closure vars, don't bother wrapping.
	if hasemptycvars(clo) {
		if Debug_closure > 0 {
			Warnl(clo.Pos, "closure converted to global")
		}
		return xfunc.Func.Nname
	}
	closuredebugruntimecheck(clo)

	typ := closureType(clo)

	clos := nod(OCOMPLIT, nil, typenod(typ))
	clos.Esc = clo.Esc
	clos.List.Set(append([]*Node{nod(OCFUNC, xfunc.Func.Nname, nil)}, clo.Func.Enter.Slice()...))

	clos = nod(OADDR, clos, nil)
	clos.Esc = clo.Esc

	// Force type conversion from *struct to the func type.
	clos = convnop(clos, clo.Type)

	// non-escaping temp to use, if any.
	if x := prealloc[clo]; x != nil {
		if !types.Identical(typ, x.Type) {
			panic("closure type does not match order's assigned type")
		}
		clos.Left.Right = x	// 闭包的类型
		delete(prealloc, clo)
	}

	return walkexpr(clos, init)
}

func typecheckpartialcall(fn *Node, sym *types.Sym) {
	switch fn.Op {
	case ODOTINTER, ODOTMETH:
		break

	default:
		Fatalf("invalid typecheckpartialcall")
	}

	// Create top-level function.
	xfunc := makepartialcall(fn, fn.Type, sym)
	fn.Func = xfunc.Func
	fn.Right = newname(sym)
	fn.Op = OCALLPART
	fn.Type = xfunc.Type
}
// fn代表一个ODOTMETH节点,t0是fn.Type,meth是fn.Sym,表示函数的符号
func makepartialcall(fn *Node, t0 *types.Type, meth *types.Sym) *Node {
	rcvrtype := fn.Left.Type
	sym := methodSymSuffix(rcvrtype, meth, "-fm")	// 找到或者创建类似于(*user).hello这样的带有recv的符号

	if sym.Uniq() {
		return asNode(sym.Def)
	}
	sym.SetUniq(true)

	savecurfn := Curfn
	saveLineNo := lineno
	Curfn = nil

	// Set line number equal to the line number where the method is declared.
	var m *types.Field
	if lookdot0(meth, rcvrtype, &m, false) == 1 && m.Pos.IsKnown() {
		lineno = m.Pos
	}
	// Note: !m.Pos.IsKnown() happens for method expressions where
	// the method is implicitly declared. The Error method of the
	// built-in error type is one such method.  We leave the line
	// number at the use of the method expression in this
	// case. See issue 29389.

	tfn := nod(OTFUNC, nil, nil)
	tfn.List.Set(structargs(t0.Params(), true))
	tfn.Rlist.Set(structargs(t0.Results(), false))

	disableExport(sym)
	xfunc := dclfunc(sym, tfn)
	xfunc.Func.SetDupok(true)
	xfunc.Func.SetNeedctxt(true)

	tfn.Type.SetPkg(t0.Pkg())

	// Declare and initialize variable holding receiver.

	cv := nod(OCLOSUREVAR, nil, nil)	// 创建一个指向闭包的变量
	cv.Type = rcvrtype
	cv.Xoffset = Rnd(int64(Widthptr), int64(cv.Type.Align))

	ptr := newname(lookup(".this"))	// 创建一个.this符号的ONAME节点
	declare(ptr, PAUTO)
	ptr.Name.SetUsed(true)
	var body []*Node
	if rcvrtype.IsPtr() || rcvrtype.IsInterface() {
		ptr.Type = rcvrtype	// ptr的Type字段应该是指向一个指针的
		body = append(body, nod(OAS, ptr, cv))	// 相当于添加ptr = cv，此时ptr中已经记录了recv的类型信息
	} else {
		ptr.Type = types.NewPtr(rcvrtype)	// ptr的Type字段应该是指向一个指针的
		body = append(body, nod(OAS, ptr, nod(OADDR, cv, nil)))		// 相当于添加ptr = &cv
	}

	call := nod(OCALL, nodSym(OXDOT, ptr, meth), nil)	// call相当于一个函数调用节点，相当于.this.meth函数的调用
	call.List.Set(paramNnames(tfn.Type))	// 设置传递的参数
	call.SetIsDDD(tfn.Type.IsVariadic())
	if t0.NumResults() != 0 {	// 调用的函数存在返回值
		n := nod(ORETURN, nil, nil)
		n.List.Set1(call)	// 这里相当于设置了返回值为函数调用后的返回值，猜测应该是为了后面的类型检查才这么做的
		call = n
	}
	body = append(body, call)

	xfunc.Nbody.Set(body)	// 函数设置函数体
	funcbody()

	xfunc = typecheck(xfunc, ctxStmt)
	sym.Def = asTypesNode(xfunc)
	xtop = append(xtop, xfunc)
	Curfn = savecurfn
	lineno = saveLineNo

	return xfunc
}

// partialCallType returns the struct type used to hold all the information
// needed in the closure for n (n must be a OCALLPART node).
// The address of a variable of the returned type can be cast to a func.
func partialCallType(n *Node) *types.Type {
	t := tostruct([]*Node{
		namedfield("F", types.Types[TUINTPTR]),
		namedfield("R", n.Left.Type),
	})
	t.SetNoalg(true)
	return t
}

func walkpartialcall(n *Node, init *Nodes) *Node {
	// Create closure in the form of a composite literal.
	// For x.M with receiver (x) type T, the generated code looks like:
	//
	//	clos = &struct{F uintptr; R T}{M.T·f, x}
	//
	// Like walkclosure above.

	if n.Left.Type.IsInterface() {	// x的类型是interface
		// Trigger panic for method on nil interface now.
		// Otherwise it happens in the wrapper and is confusing.
		n.Left = cheapexpr(n.Left, init)
		n.Left = walkexpr(n.Left, nil)

		tab := nod(OITAB, n.Left, nil)	// 获取interface的itab
		tab = typecheck(tab, ctxExpr)

		c := nod(OCHECKNIL, tab, nil)
		c.SetTypecheck(1)
		init.Append(c)
	}

	typ := partialCallType(n)

	clos := nod(OCOMPLIT, nil, typenod(typ))
	clos.Esc = n.Esc
	clos.List.Set2(nod(OCFUNC, n.Func.Nname, nil), n.Left)

	clos = nod(OADDR, clos, nil)
	clos.Esc = n.Esc

	// Force type conversion from *struct to the func type.
	clos = convnop(clos, n.Type)

	// non-escaping temp to use, if any.
	if x := prealloc[n]; x != nil {
		if !types.Identical(typ, x.Type) {
			panic("partial call type does not match order's assigned type")
		}
		clos.Left.Right = x
		delete(prealloc, n)
	}

	return walkexpr(clos, init)
}

// callpartMethod returns the *types.Field representing the method
// referenced by method value n.
func callpartMethod(n *Node) *types.Field {
	if n.Op != OCALLPART {
		Fatalf("expected OCALLPART, got %v", n)
	}

	// TODO(mdempsky): Optimize this. If necessary,
	// makepartialcall could save m for us somewhere.
	var m *types.Field
	if lookdot0(n.Right.Sym, n.Left.Type, &m, false) != 1 {
		Fatalf("failed to find field for OCALLPART")
	}

	return m
}

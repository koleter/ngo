// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import (
	"bytes"
	"cmd/compile/internal/types"
	"cmd/internal/obj"
	"cmd/internal/src"
	"fmt"
	"strings"
)

// Declaration stack & operations

var externdcl []*Node // 存储全局变量

func testdclstack() {
	if !types.IsDclstackValid() {
		if nerrors != 0 {
			errorexit()
		}
		Fatalf("mark left on the dclstack")
	}
}

// redeclare emits a diagnostic about symbol s being redeclared at pos.
func redeclare(pos src.XPos, s *types.Sym, where string) {
	if !s.Lastlineno.IsKnown() {
		pkg := s.Origpkg
		if pkg == nil {
			pkg = s.Pkg
		}
		yyerrorl(pos, "%v redeclared %s\n"+
			"\tprevious declaration during import %q", s, where, pkg.Path)
	} else {
		prevPos := s.Lastlineno

		// When an import and a declaration collide in separate files,
		// present the import as the "redeclared", because the declaration
		// is visible where the import is, but not vice versa.
		// See issue 4510.
		if s.Def == nil {
			pos, prevPos = prevPos, pos
		}

		yyerrorl(pos, "%v redeclared %s\n"+
			"\tprevious declaration at %v", s, where, linestr(prevPos))
	}
}

var vargen int // 保存声明的局部变量的数量

// declare individual names - var, typ, const

var declare_typegen int // 记录通过type定义的类型数量

// declare records that Node n declares symbol n.Sym in the specified
// declaration context.
func declare(n *Node, ctxt Class) {
	if n.isBlank() { // _
		return
	}

	if n.Name == nil {
		// named OLITERAL needs Name; most OLITERALs don't.
		n.Name = new(Name)
	}

	s := n.Sym

	// kludgy: typecheckok means we're past parsing. Eg genwrapper may declare out of package names later.
	if !inimport && !typecheckok && s.Pkg != localpkg {
		yyerrorl(n.Pos, "cannot declare name %v", s)
	}

	gen := 0
	if ctxt == PEXTERN { // 全局
		if s.Name == "init" {
			yyerrorl(n.Pos, "cannot declare init - must be func")
		}
		if s.Name == "main" && s.Pkg.Name == "main" {
			yyerrorl(n.Pos, "cannot declare main - must be func")
		}
		externdcl = append(externdcl, n)
	} else {
		if Curfn == nil && ctxt == PAUTO { // 处理局部变量但是却不在函数中
			lineno = n.Pos
			Fatalf("automatic outside function")
		}
		if Curfn != nil { // 在某个函数内部声明的变量
			Curfn.Func.Dcl = append(Curfn.Func.Dcl, n) // 添加到函数声明列表中
		}
		if n.Op == OTYPE {
			declare_typegen++
			gen = declare_typegen // 类型编号是持续生成的
		} else if n.Op == ONAME && ctxt == PAUTO && !strings.Contains(s.Name, "·") {
			vargen++
			gen = vargen // 局部变量编号是持续生成的
		}
		types.Pushdcl(s)
		n.Name.Curfn = Curfn
	}

	if ctxt == PAUTO {
		n.Xoffset = 0
	}

	if s.Block == types.Block {
		// functype will print errors about duplicate function arguments.
		// Don't repeat the error here.
		if ctxt != PPARAM && ctxt != PPARAMOUT {
			redeclare(n.Pos, s, "in this block")
		}
	}

	s.Block = types.Block // 这一行标记符号已经在当前的作用域被声明了
	s.Lastlineno = lineno
	s.Def = asTypesNode(n) // 记录符号s被声明的节点
	n.Name.Vargen = int32(gen)
	n.SetClass(ctxt)
	if ctxt == PFUNC {
		n.Sym.SetFunc(true) // 标记n是一个函数的ONAME节点
	}

	autoexport(n, ctxt)
}

func addvar(n *Node, t *types.Type, ctxt Class) {
	if n == nil || n.Sym == nil || (n.Op != ONAME && n.Op != ONONAME) || t == nil {
		Fatalf("addvar: n=%v t=%v nil", n, t)
	}

	n.Op = ONAME
	declare(n, ctxt)
	n.Type = t
}

// declare variables from grammar
// new_name_list (type | [type] = expr_list)
func variter(vl []*Node, t *Node, el []*Node) []*Node { // vl表示左部分,t表示声明的类型,el表示右部分
	var init []*Node
	doexpr := len(el) > 0

	if len(el) == 1 && len(vl) > 1 { // 这种情况类似于 var a,b,c = d
		e := el[0] // 获取右边的唯一的值
		as2 := nod(OAS2, nil, nil)
		as2.List.Set(vl)
		as2.Rlist.Set1(e)
		for _, v := range vl {
			v.Op = ONAME
			declare(v, dclcontext)
			v.Name.Param.Ntype = t
			v.Name.Defn = as2
			if Curfn != nil {
				init = append(init, nod(ODCL, v, nil))
			}
		}

		return append(init, as2)
	}

	nel := len(el)         // 保存最初右部分的expr数量
	for _, v := range vl { // 遍历左部分
		var e *Node
		if doexpr {
			if len(el) == 0 {
				yyerror("assignment mismatch: %d variables but %d values", len(vl), nel)
				break
			}
			e = el[0] // 这里相当于从头部将右边的一个表达式的值弹出
			el = el[1:]
		}

		v.Op = ONAME
		declare(v, dclcontext)
		v.Name.Param.Ntype = t // 赋予变量类型

		if e != nil || Curfn != nil || v.isBlank() { // 在函数中声明的局部变量
			if Curfn != nil {
				init = append(init, nod(ODCL, v, nil)) // 变量的声明
			}
			e = nod(OAS, v, e) // 变量的赋值,从这里可以看到类似于var a = 3这样的声明语句分为2步
			init = append(init, e)
			if e.Right != nil {
				v.Name.Defn = e
			}
		}
	}

	if len(el) != 0 {
		yyerror("assignment mismatch: %d variables but %d values", len(vl), nel)
	}
	return init
}

// newnoname returns a new ONONAME Node associated with symbol s.
func newnoname(s *types.Sym) *Node {
	if s == nil {
		Fatalf("newnoname nil")
	}
	n := nod(ONONAME, nil, nil)
	n.Sym = s
	n.Xoffset = 0
	return n
}

// newfuncnamel generates a new name node for a function or method.
// TODO(rsc): Use an ODCLFUNC node instead. See comment in CL 7360.
func newfuncnamel(pos src.XPos, s *types.Sym) *Node {
	n := newnamel(pos, s)
	n.Func = new(Func)
	n.Func.SetIsHiddenClosure(Curfn != nil)
	return n
}

// this generates a new name node for a name
// being declared.
func dclname(s *types.Sym) *Node {
	n := newname(s)
	n.Op = ONONAME // caller will correct it
	return n
}

func typenod(t *types.Type) *Node {
	return typenodl(src.NoXPos, t)
}

func typenodl(pos src.XPos, t *types.Type) *Node {
	// if we copied another type with *t = *u
	// then t->nod might be out of date, so
	// check t->nod->type too
	if asNode(t.Nod) == nil || asNode(t.Nod).Type != t {
		t.Nod = asTypesNode(nodl(pos, OTYPE, nil, nil))
		asNode(t.Nod).Type = t
		asNode(t.Nod).Sym = t.Sym
	}

	return asNode(t.Nod)
}

func anonfield(typ *types.Type) *Node {
	return symfield(nil, typ)
}

func namedfield(s string, typ *types.Type) *Node {
	return symfield(lookup(s), typ)
}

func symfield(s *types.Sym, typ *types.Type) *Node {
	n := nodSym(ODCLFIELD, nil, s)
	n.Type = typ
	return n
}

// oldname returns the Node that declares symbol s in the current scope.
// If no such Node currently exists, an ONONAME Node is returned instead.
func oldname(s *types.Sym) *Node {
	n := asNode(s.Def) // 获取之前定义该符号的抽象语法树中的节点
	if n == nil {
		// Maybe a top-level declaration will come along later to
		// define s. resolve will check s.Def again once all input
		// source has been processed.
		return newnoname(s)
	}
	// n是一个变量且当前使用的这个变量并不是在当前的函数中声明的
	if Curfn != nil && n.Op == ONAME && n.Name.Curfn != nil && n.Name.Curfn != Curfn {
		// Inner func is referring to var in outer func.
		//
		// TODO(rsc): If there is an outer variable x and we
		// are parsing x := 5 inside the closure, until we get to
		// the := it looks like a reference to the outer x so we'll
		// make x a closure variable unnecessarily.
		c := n.Name.Param.Innermost            // 获取已知的最里面的闭包中声明的符号s的ONAME节点
		if c == nil || c.Name.Curfn != Curfn { // Curfn是一个闭包
			// Do not have a closure var for the active closure yet; make one.
			c = newname(s)               // 依据符号创建一个新的ONAME节点
			c.SetClass(PAUTOHEAP)        // 记录该变量移动到了堆中
			c.Name.SetIsClosureVar(true) // 设置c是一个闭包变量
			c.SetIsDDD(n.IsDDD())
			c.Name.Defn = n // 表示闭包变量是通过最初声明符号s时的节点定义的

			// Link into list of active closure variables.
			// Popped from list in func closurebody.
			c.Name.Param.Outer = n.Name.Param.Innermost // 记录c的外层闭包变量是已知的最内层闭包变量
			n.Name.Param.Innermost = c                  // 现在已知的最内层闭包变量就是c了

			Curfn.Func.Cvars.Append(c) // 将捕获的变量添加到当前闭包函数中的捕获列表中
		}

		// return ref to closure var, not original
		return c
	}

	return n
}

// := declarations
func colasname(n *Node) bool {
	switch n.Op {
	case ONAME,
		ONONAME,
		OPACK,
		OTYPE,
		OLITERAL:
		return n.Sym != nil
	}

	return false
}

func colasdefn(left []*Node, defn *Node) {
	for _, n := range left {
		if n.Sym != nil {
			n.Sym.SetUniq(true)
		}
	}

	var nnew, nerr int
	for i, n := range left {
		if n.isBlank() {
			continue
		}
		if !colasname(n) {
			yyerrorl(defn.Pos, "non-name %v on left side of :=", n)
			nerr++
			continue
		}

		if !n.Sym.Uniq() {
			yyerrorl(defn.Pos, "%v repeated on left side of :=", n.Sym)
			n.SetDiag(true)
			nerr++
			continue
		}

		n.Sym.SetUniq(false)
		if n.Sym.Block == types.Block {
			continue
		}

		nnew++
		n = newname(n.Sym)
		declare(n, dclcontext)
		n.Name.Defn = defn
		defn.Ninit.Append(nod(ODCL, n, nil))
		left[i] = n
	}

	if nnew == 0 && nerr == 0 {
		yyerrorl(defn.Pos, "no new variables on left side of :=")
	}
}

// declare the arguments in an
// interface field declaration.
func ifacedcl(n *Node) {
	if n.Op != ODCLFIELD || n.Left == nil {
		Fatalf("ifacedcl")
	}

	if n.Sym.IsBlank() {
		yyerror("methods must have a unique non-blank name")
	}
}

// declare the function proper
// and declare the arguments.
// called in extern-declaration context
// returns in auto-declaration context.
func funchdr(n *Node) {
	// change the declaration context from extern to auto
	if Curfn == nil && dclcontext != PEXTERN { // 当前不是在一个函数中且当前解析的不是全局变量
		Fatalf("funchdr: dclcontext = %d", dclcontext)
	}

	dclcontext = PAUTO                   // 处理局部变量
	types.Markdcl()                      // 记录一个新的作用域栈帧,保存之前的声明信息
	funcstack = append(funcstack, Curfn) // 存储上一个处理的函数节点
	Curfn = n                            // 当前处理的函数设置为n

	if n.Func.Nname != nil { // 函数名符号对应的节点不为nil,说明这不是一个匿名函数且是在当前包中的定义的
		funcargs(n.Func.Nname.Name.Param.Ntype) // 处理函数的类型节点
	} else if n.Func.Ntype != nil {
		funcargs(n.Func.Ntype)
	} else { // 其他包的函数的ONAME节点
		funcargs2(n.Type)
	}
}

// 处理函数类型中的出参与入参
func funcargs(nt *Node) {
	if nt.Op != OTFUNC {
		Fatalf("funcargs %v", nt.Op)
	}

	// re-start the variable generation number
	// we want to use small numbers for the return variables,
	// so let them have the chunk starting at 1.
	//
	// TODO(mdempsky): This is ugly, and only necessary because
	// esc.go uses Vargen to figure out result parameters' index
	// within the result tuple.
	vargen = nt.Rlist.Len() // result列表的数量

	// declare the receiver and in arguments.
	if nt.Left != nil {
		funcarg(nt.Left, PPARAM) // 处理receiver,注意这里会将vargen加一
	}
	for _, n := range nt.List.Slice() {
		funcarg(n, PPARAM) // 处理入参列表,注意这里会将vargen加一
	}

	oldvargen := vargen // 此时的vargen是所有入参出参的数量
	vargen = 0

	// declare the out arguments.
	gen := nt.List.Len() // 形参length
	for _, n := range nt.Rlist.Slice() {
		if n.Sym == nil { // 返回值没有命名
			// Name so that escape analysis can track it. ~r stands for 'result'.
			n.Sym = lookupN("~r", gen) // 生成一个符号
			gen++
		}
		if n.Sym.IsBlank() { // 返回值是_
			// Give it a name so we can assign to it during return. ~b stands for 'blank'.
			// The name must be different from ~r above because if you have
			//	func f() (_ int)
			//	func g() int
			// f is allowed to use a plain 'return' with no arguments, while g is not.

			// So the two cases must be distinguished.
			n.Sym = lookupN("~b", gen)
			gen++
		}

		funcarg(n, PPARAMOUT)
	}

	vargen = oldvargen
}

func funcarg(n *Node, ctxt Class) {
	if n.Op != ODCLFIELD {
		Fatalf("funcarg %v", n.Op)
	}
	if n.Sym == nil {
		return
	}

	n.Right = newnamel(n.Pos, n.Sym)
	n.Right.Name.Param.Ntype = n.Left
	n.Right.SetIsDDD(n.IsDDD())
	declare(n.Right, ctxt)

	vargen++
	n.Right.Name.Vargen = int32(vargen)
}

// Same as funcargs, except run over an already constructed TFUNC.
// This happens during import, where the hidden_fndcl rule has
// used functype directly to parse the function's type.
func funcargs2(t *types.Type) {
	if t.Etype != TFUNC {
		Fatalf("funcargs2 %v", t)
	}

	for _, f := range t.Recvs().Fields().Slice() {
		funcarg2(f, PPARAM)
	}
	for _, f := range t.Params().Fields().Slice() {
		funcarg2(f, PPARAM)
	}
	for _, f := range t.Results().Fields().Slice() {
		funcarg2(f, PPARAMOUT)
	}
}

func funcarg2(f *types.Field, ctxt Class) {
	if f.Sym == nil {
		return
	}
	n := newnamel(f.Pos, f.Sym)
	f.Nname = asTypesNode(n)
	n.Type = f.Type
	n.SetIsDDD(f.IsDDD())
	declare(n, ctxt)
}

var funcstack []*Node // stack of previous values of Curfn

// finish the body.
// called in auto-declaration context.
// returns in extern-declaration context.
func funcbody() {
	// change the declaration context from auto to extern
	if dclcontext != PAUTO {
		Fatalf("funcbody: unexpected dclcontext %d", dclcontext)
	}
	types.Popdcl()                                                               // 恢复符号的上一个作用域声明
	funcstack, Curfn = funcstack[:len(funcstack)-1], funcstack[len(funcstack)-1] // 恢复Curfn为上一个Curfn
	if Curfn == nil {
		dclcontext = PEXTERN // 不在函数中了，上下文改成全局
	}
}

// structs, functions, and methods.
// they don't belong here, but where do they belong?
func checkembeddedtype(t *types.Type) {
	if t == nil {
		return
	}

	if t.Sym == nil && t.IsPtr() { // 内嵌的类型是一个指针
		t = t.Elem() // 获取指针指向的类型
		if t.IsInterface() {
			yyerror("embedded type cannot be a pointer to interface")
		}
	}

	if t.IsPtr() || t.IsUnsafePtr() {
		yyerror("embedded type cannot be a pointer")
	} else if t.Etype == TFORW && !t.ForwardType().Embedlineno.IsKnown() {
		t.ForwardType().Embedlineno = lineno
	}
}

func structfield(n *Node) *types.Field {
	lno := lineno
	lineno = n.Pos

	if n.Op != ODCLFIELD {
		Fatalf("structfield: oops %v\n", n)
	}

	f := types.NewField()
	f.Pos = n.Pos
	f.Sym = n.Sym

	if n.Left != nil { // 类型不为空
		n.Left = typecheck(n.Left, ctxType)
		n.Type = n.Left.Type
		n.Left = nil
	}

	f.Type = n.Type // 赋予field类型
	if f.Type == nil {
		f.SetBroke(true)
	}

	if n.Embedded() { // 当前的成员是另一种类型直接嵌入到该结构体中的
		checkembeddedtype(n.Type)
		f.Embedded = 1
	} else {
		f.Embedded = 0
	}

	switch u := n.Val().U.(type) { // 处理tag
	case string:
		f.Note = u
	default:
		yyerror("field tag must be a string")
	case nil:
		// no-op
	}

	lineno = lno
	return f
}

// checkdupfields emits errors for duplicately named fields or methods in
// a list of struct or interface types.
func checkdupfields(what string, fss ...[]*types.Field) {
	seen := make(map[*types.Sym]bool)
	for _, fs := range fss {
		for _, f := range fs {
			if f.Sym == nil || f.Sym.IsBlank() {
				continue
			}
			if seen[f.Sym] {
				yyerrorl(f.Pos, "duplicate %s %s", what, f.Sym.Name)
				continue
			}
			seen[f.Sym] = true
		}
	}
}

// convert a parsed id/type list into
// a type for struct/interface/arglist
func tostruct(l []*Node) *types.Type {
	t := types.New(TSTRUCT)

	fields := make([]*types.Field, len(l))
	for i, n := range l {
		f := structfield(n)
		if f.Broke() {
			t.SetBroke(true)
		}
		fields[i] = f
	}
	t.SetFields(fields)

	checkdupfields("field", t.FieldSlice()) // 检查结构体中是否有相同符号的字段

	if !t.Broke() {
		checkwidth(t)
	}

	return t
}

func tofunargs(l []*Node, funarg types.Funarg) *types.Type {
	t := types.New(TSTRUCT)
	t.StructType().Funarg = funarg

	fields := make([]*types.Field, len(l))
	for i, n := range l {
		f := structfield(n) // 用n来构造一个Field
		f.SetIsDDD(n.IsDDD())
		if n.Right != nil {
			n.Right.Type = f.Type          // 参数ONAME变量的类型赋值
			f.Nname = asTypesNode(n.Right) // Nname指向ONAME变量节点(仅在函数的recv,param,paramout时不为nil)
		}
		if f.Broke() {
			t.SetBroke(true)
		}
		fields[i] = f
	}
	t.SetFields(fields)
	return t
}

//funarg代表函数的参数的类型
func tofunargsfield(fields []*types.Field, funarg types.Funarg) *types.Type {
	t := types.New(TSTRUCT)
	t.StructType().Funarg = funarg
	t.SetFields(fields)
	return t
}

func interfacefield(n *Node) *types.Field {
	lno := lineno
	lineno = n.Pos

	if n.Op != ODCLFIELD {
		Fatalf("interfacefield: oops %v\n", n)
	}

	if n.Val().Ctype() != CTxxx {
		yyerror("interface method cannot have annotation")
	}

	// MethodSpec = MethodName Signature | InterfaceTypeName .
	//
	// If Sym != nil, then Sym is MethodName and Left is Signature.
	// Otherwise, Left is InterfaceTypeName.

	if n.Left != nil { // 类型
		n.Left = typecheck(n.Left, ctxType)
		n.Type = n.Left.Type
		n.Left = nil
	}

	f := types.NewField()
	f.Pos = n.Pos
	f.Sym = n.Sym
	f.Type = n.Type
	if f.Type == nil {
		f.SetBroke(true)
	}

	lineno = lno
	return f
}

func tointerface(l []*Node) *types.Type {
	if len(l) == 0 {
		return types.Types[TINTER]
	}
	t := types.New(TINTER)
	var fields []*types.Field
	for _, n := range l {
		f := interfacefield(n)
		if f.Broke() {
			t.SetBroke(true)
		}
		fields = append(fields, f)
	}
	t.SetInterface(fields)
	return t
}

func fakeRecv() *Node {
	return anonfield(types.FakeRecvType())
}

func fakeRecvField() *types.Field {
	f := types.NewField()
	f.Type = types.FakeRecvType()
	return f
}

// isifacemethod reports whether (field) m is
// an interface method. Such methods have the
// special receiver type types.FakeRecvType().
func isifacemethod(f *types.Type) bool {
	return f.Recv().Type == types.FakeRecvType()
}

// turn a parsed function declaration into a type
func functype(this *Node, in, out []*Node) *types.Type {
	t := types.New(TFUNC)

	var rcvr []*Node
	if this != nil {
		rcvr = []*Node{this}
	}
	t.FuncType().Receiver = tofunargs(rcvr, types.FunargRcvr)
	t.FuncType().Params = tofunargs(in, types.FunargParams)
	t.FuncType().Results = tofunargs(out, types.FunargResults)

	checkdupfields("argument", t.Recvs().FieldSlice(), t.Params().FieldSlice(), t.Results().FieldSlice()) // 检查recv,params,results中是否有相同名字的变量

	if t.Recvs().Broke() || t.Results().Broke() || t.Params().Broke() {
		t.SetBroke(true)
	}

	t.FuncType().Outnamed = t.NumResults() > 0 && origSym(t.Results().Field(0).Sym) != nil

	return t
}

// this不为空表示函数第一个参数是this，in是除了this外其他的形参列表，out是输出参数列表
func functypefield(this *types.Field, in, out []*types.Field) *types.Type {
	t := types.New(TFUNC)

	var rcvr []*types.Field
	if this != nil {
		rcvr = []*types.Field{this}
	}
	t.FuncType().Receiver = tofunargsfield(rcvr, types.FunargRcvr)
	t.FuncType().Params = tofunargsfield(in, types.FunargParams)
	t.FuncType().Results = tofunargsfield(out, types.FunargResults)

	t.FuncType().Outnamed = t.NumResults() > 0 && origSym(t.Results().Field(0).Sym) != nil

	return t
}

// origSym returns the original symbol written by the user.
func origSym(s *types.Sym) *types.Sym {
	if s == nil {
		return nil
	}

	if len(s.Name) > 1 && s.Name[0] == '~' {
		switch s.Name[1] {
		case 'r': // originally an unnamed result
			return nil
		case 'b': // originally the blank identifier _
			// TODO(mdempsky): Does s.Pkg matter here?
			return nblank.Sym
		}
		return s
	}

	if strings.HasPrefix(s.Name, ".anon") {
		// originally an unnamed or _ name (see subr.go: structargs)
		return nil
	}

	return s
}

// methodSym returns the method symbol representing a method name
// associated with a specific receiver type.
//
// Method symbols can be used to distinguish the same method appearing
// in different method sets. For example, T.M and (*T).M have distinct
// method symbols.
//
// The returned symbol will be marked as a function.
func methodSym(recv *types.Type, msym *types.Sym) *types.Sym {
	sym := methodSymSuffix(recv, msym, "")
	sym.SetFunc(true)
	return sym
}

// methodSymSuffix is like methodsym, but allows attaching a
// distinguisher suffix. To avoid collisions, the suffix must not
// start with a letter, number, or period.
func methodSymSuffix(recv *types.Type, msym *types.Sym, suffix string) *types.Sym {
	if msym.IsBlank() {
		Fatalf("blank method name")
	}

	rsym := recv.Sym // recv的符号
	if recv.IsPtr() {
		if rsym != nil { // 当类型是一个指针时，Sym是nil
			Fatalf("declared pointer receiver type: %v", recv)
		}
		rsym = recv.Elem().Sym
	}

	// Find the package the receiver type appeared in. For
	// anonymous receiver types (i.e., anonymous structs with
	// embedded fields), use the "go" pseudo-package instead.
	rpkg := gopkg
	if rsym != nil {
		rpkg = rsym.Pkg
	}

	var b bytes.Buffer
	if recv.IsPtr() {
		// The parentheses aren't really necessary, but
		// they're pretty traditional at this point.
		fmt.Fprintf(&b, "(%-S)", recv)
	} else {
		fmt.Fprintf(&b, "%-S", recv)
	}

	// A particular receiver type may have multiple non-exported
	// methods with the same name. To disambiguate them, include a
	// package qualifier for names that came from a different
	// package than the receiver type.
	if !types.IsExported(msym.Name) && msym.Pkg != rpkg {
		b.WriteString(".")
		b.WriteString(msym.Pkg.Prefix)
	}

	b.WriteString(".")
	b.WriteString(msym.Name)
	b.WriteString(suffix)

	return rpkg.LookupBytes(b.Bytes())
}

// Add a method, declared as a function.
// - msym is the method symbol
// - t is function type (with receiver)
// Returns a pointer to the existing or added Field; or nil if there's an error.
func addmethod(msym *types.Sym, t *types.Type, local, nointerface bool) *types.Field {
	if msym == nil {
		Fatalf("no method symbol")
	}

	// get parent type sym
	rf := t.Recv() // ptr to this structure
	if rf == nil {
		yyerror("missing receiver")
		return nil
	}

	mt := methtype(rf.Type)         // 获取receiver的底层类型
	if mt == nil || mt.Sym == nil { // mt为nil或者mt没有命名
		pa := rf.Type
		t := pa
		if t != nil && t.IsPtr() {
			if t.Sym != nil {
				yyerror("invalid receiver type %v (%v is a pointer type)", pa, t)
				return nil
			}
			t = t.Elem()
		}

		switch {
		case t == nil || t.Broke():
			// rely on typecheck having complained before
		case t.Sym == nil:
			yyerror("invalid receiver type %v (%v is not a defined type)", pa, t)
		case t.IsPtr():
			yyerror("invalid receiver type %v (%v is a pointer type)", pa, t)
		case t.IsInterface():
			yyerror("invalid receiver type %v (%v is an interface type)", pa, t)
		default:
			// Should have picked off all the reasons above,
			// but just in case, fall back to generic error.
			yyerror("invalid receiver type %v (%L / %L)", pa, pa, t)
		}
		return nil
	}

	if local && mt.Sym.Pkg != localpkg {
		yyerror("cannot define new methods on non-local type %v", mt)
		return nil
	}

	if msym.IsBlank() {
		return nil
	}

	if mt.IsStruct() { // 底层类型是结构体
		for _, f := range mt.Fields().Slice() {
			if f.Sym == msym { // 底层类型中出现了字段与函数名相同的情况
				yyerror("type %v has both field and method named %v", mt, msym)
				f.SetBroke(true)
				return nil
			}
		}
	}

	for _, f := range mt.Methods().Slice() { // 校验mt所声明的所有函数
		if msym.Name != f.Sym.Name {
			continue
		}
		// types.Identical only checks that incoming and result parameters match,
		// so explicitly check that the receiver parameters match too.
		if !types.Identical(t, f.Type) || !types.Identical(t.Recv().Type, f.Type.Recv().Type) { // 发现具有相同的函数名之后要判断函数的参数类型以及receiver的类型是否不匹配
			yyerror("method redeclared: %v.%v\n\t%v\n\t%v", mt, msym, f.Type, t)
		}
		return f
	}

	f := types.NewField()
	f.Pos = lineno
	f.Sym = msym
	f.Type = t
	f.SetNointerface(nointerface)

	mt.Methods().Append(f)
	return f
}

func funcsymname(s *types.Sym) string {
	return s.Name + "·f"
}

// funcsym returns s·f.
func funcsym(s *types.Sym) *types.Sym {
	// funcsymsmu here serves to protect not just mutations of funcsyms (below),
	// but also the package lookup of the func sym name,
	// since this function gets called concurrently from the backend.
	// There are no other concurrent package lookups in the backend,
	// except for the types package, which is protected separately.
	// Reusing funcsymsmu to also cover this package lookup
	// avoids a general, broader, expensive package lookup mutex.
	// Note makefuncsym also does package look-up of func sym names,
	// but that it is only called serially, from the front end.
	funcsymsmu.Lock()
	sf, existed := s.Pkg.LookupOK(funcsymname(s))
	// Don't export s·f when compiling for dynamic linking.
	// When dynamically linking, the necessary function
	// symbols will be created explicitly with makefuncsym.
	// See the makefuncsym comment for details.
	if !Ctxt.Flag_dynlink && !existed {
		funcsyms = append(funcsyms, s)
	}
	funcsymsmu.Unlock()
	return sf
}

// makefuncsym ensures that s·f is exported.
// It is only used with -dynlink.
// When not compiling for dynamic linking,
// the funcsyms are created as needed by
// the packages that use them.
// Normally we emit the s·f stubs as DUPOK syms,
// but DUPOK doesn't work across shared library boundaries.
// So instead, when dynamic linking, we only create
// the s·f stubs in s's package.
func makefuncsym(s *types.Sym) {
	if !Ctxt.Flag_dynlink {
		Fatalf("makefuncsym dynlink")
	}
	if s.IsBlank() {
		return
	}
	if compiling_runtime && (s.Name == "getg" || s.Name == "getclosureptr" || s.Name == "getcallerpc" || s.Name == "getcallersp") {
		// runtime.getg(), getclosureptr(), getcallerpc(), and
		// getcallersp() are not real functions and so do not
		// get funcsyms.
		return
	}
	if _, existed := s.Pkg.LookupOK(funcsymname(s)); !existed {
		funcsyms = append(funcsyms, s)
	}
}

// disableExport prevents sym from being included in package export
// data. To be effectual, it must be called before declare.
func disableExport(sym *types.Sym) {
	sym.SetOnExportList(true)
}

// sym是函数的符号,tfn是一个OTFUNC节点，相当于记录了函数的类型，该方法用于通过一个符号以及函数类型声明函数节点
func dclfunc(sym *types.Sym, tfn *Node) *Node {
	if tfn.Op != OTFUNC {
		Fatalf("expected OTFUNC node, got %v", tfn)
	}

	fn := nod(ODCLFUNC, nil, nil)
	fn.Func.Nname = newfuncnamel(lineno, sym)
	fn.Func.Nname.Name.Defn = fn
	fn.Func.Nname.Name.Param.Ntype = tfn
	declare(fn.Func.Nname, PFUNC)
	funchdr(fn)
	fn.Func.Nname.Name.Param.Ntype = typecheck(fn.Func.Nname.Name.Param.Ntype, ctxType)
	return fn
}

type nowritebarrierrecChecker struct {
	// extraCalls contains extra function calls that may not be
	// visible during later analysis. It maps from the ODCLFUNC of
	// the caller to a list of callees.
	extraCalls map[*Node][]nowritebarrierrecCall

	// curfn is the current function during AST walks.
	curfn *Node
}

type nowritebarrierrecCall struct {
	target *Node    // ODCLFUNC of caller or callee
	lineno src.XPos // line of call
}

type nowritebarrierrecCallSym struct {
	target *obj.LSym // LSym of callee
	lineno src.XPos  // line of call
}

// newNowritebarrierrecChecker creates a nowritebarrierrecChecker. It
// must be called before transformclosure and walk.
func newNowritebarrierrecChecker() *nowritebarrierrecChecker {
	c := &nowritebarrierrecChecker{
		extraCalls: make(map[*Node][]nowritebarrierrecCall),
	}

	// Find all systemstack calls and record their targets. In
	// general, flow analysis can't see into systemstack, but it's
	// important to handle it for this check, so we model it
	// directly. This has to happen before transformclosure since
	// it's a lot harder to work out the argument after.
	for _, n := range xtop {
		if n.Op != ODCLFUNC {
			continue
		}
		c.curfn = n
		inspect(n, c.findExtraCalls)
	}
	c.curfn = nil
	return c
}

func (c *nowritebarrierrecChecker) findExtraCalls(n *Node) bool {
	if n.Op != OCALLFUNC { // Left(List/Rlist) (function call f(args))
		return true
	}
	fn := n.Left // 获取函数节点
	if fn == nil || fn.Op != ONAME || fn.Class() != PFUNC || fn.Name.Defn == nil {
		return true
	}
	if !isRuntimePkg(fn.Sym.Pkg) || fn.Sym.Name != "systemstack" {
		return true
	}
	// n是一个函数调用，函数是runtime包下的全局函数或者是systemstack函数
	var callee *Node
	arg := n.List.First() // 第一个参数
	switch arg.Op {
	case ONAME:
		callee = arg.Name.Defn
	case OCLOSURE: // 参数是一个闭包函数
		callee = arg.Func.Closure
	default:
		Fatalf("expected ONAME or OCLOSURE node, got %+v", arg)
	}
	if callee.Op != ODCLFUNC { // 函数的第一个参数是一个函数声明
		Fatalf("expected ODCLFUNC node, got %+v", callee)
	}
	c.extraCalls[c.curfn] = append(c.extraCalls[c.curfn], nowritebarrierrecCall{callee, n.Pos})
	return true
}

// recordCall records a call from ODCLFUNC node "from", to function
// symbol "to" at position pos.
//
// This should be done as late as possible during compilation to
// capture precise call graphs. The target of the call is an LSym
// because that's all we know after we start SSA.
//
// This can be called concurrently for different from Nodes.
func (c *nowritebarrierrecChecker) recordCall(from *Node, to *obj.LSym, pos src.XPos) {
	if from.Op != ODCLFUNC {
		Fatalf("expected ODCLFUNC, got %v", from)
	}
	// We record this information on the *Func so this is
	// concurrent-safe.
	fn := from.Func
	if fn.nwbrCalls == nil {
		fn.nwbrCalls = new([]nowritebarrierrecCallSym)
	}
	*fn.nwbrCalls = append(*fn.nwbrCalls, nowritebarrierrecCallSym{to, pos})
}

func (c *nowritebarrierrecChecker) check() {
	// We walk the call graph as late as possible so we can
	// capture all calls created by lowering, but this means we
	// only get to see the obj.LSyms of calls. symToFunc lets us
	// get back to the ODCLFUNCs.
	symToFunc := make(map[*obj.LSym]*Node)
	// funcs records the back-edges of the BFS call graph walk. It
	// maps from the ODCLFUNC of each function that must not have
	// write barriers to the call that inhibits them. Functions
	// that are directly marked go:nowritebarrierrec are in this
	// map with a zero-valued nowritebarrierrecCall. This also
	// acts as the set of marks for the BFS of the call graph.
	funcs := make(map[*Node]nowritebarrierrecCall)
	// q is the queue of ODCLFUNC Nodes to visit in BFS order.
	var q nodeQueue

	for _, n := range xtop {
		if n.Op != ODCLFUNC {
			continue
		}

		symToFunc[n.Func.lsym] = n

		// Make nowritebarrierrec functions BFS roots.
		if n.Func.Pragma&Nowritebarrierrec != 0 {
			funcs[n] = nowritebarrierrecCall{}
			q.pushRight(n)
		}
		// Check go:nowritebarrier functions.
		if n.Func.Pragma&Nowritebarrier != 0 && n.Func.WBPos.IsKnown() {
			yyerrorl(n.Func.WBPos, "write barrier prohibited")
		}
	}

	// Perform a BFS of the call graph from all
	// go:nowritebarrierrec functions.
	enqueue := func(src, target *Node, pos src.XPos) {
		if target.Func.Pragma&Yeswritebarrierrec != 0 {
			// Don't flow into this function.
			return
		}
		if _, ok := funcs[target]; ok {
			// Already found a path to target.
			return
		}

		// Record the path.
		funcs[target] = nowritebarrierrecCall{target: src, lineno: pos}
		q.pushRight(target)
	}
	for !q.empty() {
		fn := q.popLeft()

		// Check fn.
		if fn.Func.WBPos.IsKnown() {
			var err bytes.Buffer
			call := funcs[fn]
			for call.target != nil {
				fmt.Fprintf(&err, "\n\t%v: called by %v", linestr(call.lineno), call.target.Func.Nname)
				call = funcs[call.target]
			}
			yyerrorl(fn.Func.WBPos, "write barrier prohibited by caller; %v%s", fn.Func.Nname, err.String())
			continue
		}

		// Enqueue fn's calls.
		for _, callee := range c.extraCalls[fn] {
			enqueue(fn, callee.target, callee.lineno)
		}
		if fn.Func.nwbrCalls == nil {
			continue
		}
		for _, callee := range *fn.Func.nwbrCalls {
			target := symToFunc[callee.target]
			if target != nil {
				enqueue(fn, target, callee.lineno)
			}
		}
	}
}

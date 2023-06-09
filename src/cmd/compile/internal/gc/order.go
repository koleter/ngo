// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import (
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"fmt"
)

// Rewrite tree to use separate statements to enforce
// order of evaluation. Makes walk easier, because it
// can (after this runs) reorder at will within an expression.
//
// Rewrite m[k] op= r into m[k] = m[k] op r if op is / or %.
//
// Introduce temporaries as needed by runtime routines.
// For example, the map runtime routines take the map key
// by reference, so make sure all map keys are addressable
// by copying them to temporaries as needed.
// The same is true for channel operations.
//
// Arrange that map index expressions only appear in direct
// assignments x = m[k] or m[k] = x, never in larger expressions.
//
// Arrange that receive expressions only appear in direct assignments
// x = <-c or as standalone statements <-c, never in larger expressions.

// TODO(rsc): The temporary introduction during multiple assignments
// should be moved into this file, so that the temporaries can be cleaned
// and so that conversions implicit in the OAS2FUNC and OAS2RECV
// nodes can be made explicit and then have their temporaries cleaned.

// TODO(rsc): Goto and multilevel break/continue can jump over
// inserted VARKILL annotations. Work out a way to handle these.
// The current implementation is safe, in that it will execute correctly.
// But it won't reuse temporaries as aggressively as it might, and
// it can result in unnecessary zeroing of those variables in the function
// prologue.

// Order holds state during the ordering process.
type Order struct {
	out  []*Node            // list of generated statements
	temp []*Node            // stack of temporary variables
	free map[string][]*Node // free list of unused temporaries, by type.LongString().
}

// Order rewrites fn.Nbody to apply the ordering constraints
// described in the comment at the top of the file.
func order(fn *Node) {
	if Debug['W'] > 1 {
		s := fmt.Sprintf("\nbefore order %v", fn.Func.Nname.Sym)
		dumplist(s, fn.Nbody)
	}

	orderBlock(&fn.Nbody, map[string][]*Node{})
}

// newTemp allocates a new temporary with the given type,
// pushes it onto the temp stack, and returns it.
// If clear is true, newTemp emits code to zero the temporary.
func (o *Order) newTemp(t *types.Type, clear bool) *Node {
	var v *Node
	// Note: LongString is close to the type equality we want,
	// but not exactly. We still need to double-check with types.Identical.
	key := t.LongString()
	a := o.free[key]
	for i, n := range a {
		if types.Identical(t, n.Type) {	// 存在与t类型相同的节点
			v = a[i]	// 赋给v
			a[i] = a[len(a)-1]	// a数组最后一个放到当前的位置
			a = a[:len(a)-1]	// 将a数组的长度减一
			o.free[key] = a	// 再将a数组赋回去
			break
		}
	}
	if v == nil {	// a数组中没有对应的可用变量
		v = temp(t)	// 创建一个新的临时变量，op类型为ONAME
	}
	if clear {
		a := nod(OAS, v, nil)	// 临时变量v赋值为nil
		a = typecheck(a, ctxStmt)
		o.out = append(o.out, a)
	}

	o.temp = append(o.temp, v)
	return v
}

// copyExpr behaves like newTemp but also emits
// code to initialize the temporary to the value n.
//
// The clear argument is provided for use when the evaluation
// of tmp = n turns into a function call that is passed a pointer
// to the temporary as the output space. If the call blocks before
// tmp has been written, the garbage collector will still treat the
// temporary as live, so we must zero it before entering that call.
// Today, this only happens for channel receive operations.
// (The other candidate would be map access, but map access
// returns a pointer to the result data instead of taking a pointer
// to be filled in.)
func (o *Order) copyExpr(n *Node, t *types.Type, clear bool) *Node {
	v := o.newTemp(t, clear)
	a := nod(OAS, v, n)	// v = n
	a = typecheck(a, ctxStmt)
	o.out = append(o.out, a)
	return v
}

// cheapExpr returns a cheap version of n.
// The definition of cheap is that n is a variable or constant.
// If not, cheapExpr allocates a new tmp, emits tmp = n,
// and then returns tmp.
func (o *Order) cheapExpr(n *Node) *Node {
	if n == nil {
		return nil
	}

	switch n.Op {
	case ONAME, OLITERAL:
		return n
	case OLEN, OCAP:
		l := o.cheapExpr(n.Left)
		if l == n.Left {
			return n
		}
		a := n.sepcopy()
		a.Left = l
		return typecheck(a, ctxExpr)
	}

	return o.copyExpr(n, n.Type, false)
}

// safeExpr returns a safe version of n.
// The definition of safe is that n can appear multiple times
// without violating the semantics of the original program,
// and that assigning to the safe version has the same effect
// as assigning to the original n.
//
// The intended use is to apply to x when rewriting x += y into x = x + y.
func (o *Order) safeExpr(n *Node) *Node {
	switch n.Op {
	case ONAME, OLITERAL:
		return n

	case ODOT, OLEN, OCAP:
		l := o.safeExpr(n.Left)
		if l == n.Left {
			return n
		}
		a := n.sepcopy()
		a.Left = l
		return typecheck(a, ctxExpr)

	case ODOTPTR, ODEREF:
		l := o.cheapExpr(n.Left)
		if l == n.Left {
			return n
		}
		a := n.sepcopy()
		a.Left = l
		return typecheck(a, ctxExpr)

	case OINDEX, OINDEXMAP:
		var l *Node
		if n.Left.Type.IsArray() {
			l = o.safeExpr(n.Left)
		} else {
			l = o.cheapExpr(n.Left)
		}
		r := o.cheapExpr(n.Right)
		if l == n.Left && r == n.Right {
			return n
		}
		a := n.sepcopy()
		a.Left = l
		a.Right = r
		return typecheck(a, ctxExpr)

	default:
		Fatalf("order.safeExpr %v", n.Op)
		return nil // not reached
	}
}

// isaddrokay reports whether it is okay to pass n's address to runtime routines.
// Taking the address of a variable makes the liveness and optimization analyses
// lose track of where the variable's lifetime ends. To avoid hurting the analyses
// of ordinary stack variables, those are not 'isaddrokay'. Temporaries are okay,
// because we emit explicit VARKILL instructions marking the end of those
// temporaries' lifetimes.
func isaddrokay(n *Node) bool {
	return islvalue(n) && (n.Op != ONAME || n.Class() == PEXTERN || n.IsAutoTmp())
}

// addrTemp ensures that n is okay to pass by address to runtime routines.
// If the original argument n is not okay, addrTemp creates a tmp, emits
// tmp = n, and then returns tmp.
// The result of addrTemp MUST be assigned back to n, e.g.
// 	n.Left = o.addrTemp(n.Left)
func (o *Order) addrTemp(n *Node) *Node {
	if consttype(n) != CTxxx {
		// TODO: expand this to all static composite literal nodes?
		n = defaultlit(n, nil)
		dowidth(n.Type)
		vstat := staticname(n.Type)
		vstat.MarkReadonly()
		var s InitSchedule
		s.staticassign(vstat, n)
		if s.out != nil {
			Fatalf("staticassign of const generated code: %+v", n)
		}
		vstat = typecheck(vstat, ctxExpr)
		return vstat
	}
	if isaddrokay(n) {
		return n
	}
	return o.copyExpr(n, n.Type, false)
}

// mapKeyTemp prepares n to be a key in a map runtime call and returns n.
// It should only be used for map runtime calls which have *_fast* versions.
func (o *Order) mapKeyTemp(t *types.Type, n *Node) *Node {
	// Most map calls need to take the address of the key.
	// Exception: map*_fast* calls. See golang.org/issue/19015.
	if mapfast(t) == mapslow {
		return o.addrTemp(n)
	}
	return n
}

// mapKeyReplaceStrConv replaces OBYTES2STR by OBYTES2STRTMP
// in n to avoid string allocations for keys in map lookups.
// Returns a bool that signals if a modification was made.
//
// For:
//  x = m[string(k)]
//  x = m[T1{... Tn{..., string(k), ...}]
// where k is []byte, T1 to Tn is a nesting of struct and array literals,
// the allocation of backing bytes for the string can be avoided
// by reusing the []byte backing array. These are special cases
// for avoiding allocations when converting byte slices to strings.
// It would be nice to handle these generally, but because
// []byte keys are not allowed in maps, the use of string(k)
// comes up in important cases in practice. See issue 3512.
func mapKeyReplaceStrConv(n *Node) bool {
	var replaced bool
	switch n.Op {
	case OBYTES2STR:
		n.Op = OBYTES2STRTMP
		replaced = true
	case OSTRUCTLIT:
		for _, elem := range n.List.Slice() {
			if mapKeyReplaceStrConv(elem.Left) {
				replaced = true
			}
		}
	case OARRAYLIT:
		for _, elem := range n.List.Slice() {
			if elem.Op == OKEY {
				elem = elem.Right
			}
			if mapKeyReplaceStrConv(elem) {
				replaced = true
			}
		}
	}
	return replaced
}

type ordermarker int

// markTemp returns the top of the temporary variable stack.
func (o *Order) markTemp() ordermarker {
	return ordermarker(len(o.temp))
}

// popTemp pops temporaries off the stack until reaching the mark,
// which must have been returned by markTemp.
func (o *Order) popTemp(mark ordermarker) {
	for _, n := range o.temp[mark:] {
		key := n.Type.LongString()
		o.free[key] = append(o.free[key], n)
	}
	o.temp = o.temp[:mark]
}

// cleanTempNoPop emits VARKILL and if needed VARLIVE instructions
// to *out for each temporary above the mark on the temporary stack.
// It does not pop the temporaries from the stack.
func (o *Order) cleanTempNoPop(mark ordermarker) []*Node {
	var out []*Node
	for i := len(o.temp) - 1; i >= int(mark); i-- {
		n := o.temp[i]
		if n.Name.Keepalive() {
			n.Name.SetKeepalive(false)
			n.Name.SetAddrtaken(true) // ensure SSA keeps the n variable
			live := nod(OVARLIVE, n, nil)
			live = typecheck(live, ctxStmt)
			out = append(out, live)
		}
		kill := nod(OVARKILL, n, nil)
		kill = typecheck(kill, ctxStmt)
		out = append(out, kill)
	}
	return out
}

// cleanTemp emits VARKILL instructions for each temporary above the
// mark on the temporary stack and removes them from the stack.
func (o *Order) cleanTemp(top ordermarker) {
	o.out = append(o.out, o.cleanTempNoPop(top)...)
	o.popTemp(top)
}

// stmtList orders each of the statements in the list.
func (o *Order) stmtList(l Nodes) {
	s := l.Slice()
	for i := range s {
		orderMakeSliceCopy(s[i:])	// Set  m = OMAKESLICE([]T, len(s)); OCOPY(m, s)  to OMAKESLICECOPY
		o.stmt(s[i])
	}
}

// orderMakeSliceCopy matches the pattern:
//  m = OMAKESLICE([]T, x); OCOPY(m, s)
// and rewrites it to:
//  m = OMAKESLICECOPY([]T, x, s); nil
func orderMakeSliceCopy(s []*Node) {
	const go115makeslicecopy = true
	if !go115makeslicecopy {
		return
	}

	if Debug['N'] != 0 || instrumenting {
		return
	}

	if len(s) < 2 {
		return
	}

	asn := s[0]
	copyn := s[1]

	if asn == nil || asn.Op != OAS {	// Left = Right or (if Colas=true) Left := Right
		return
	}
	if asn.Left.Op != ONAME {	// var or func name
		return
	}
	if asn.Left.isBlank() {
		return
	}
	maken := asn.Right
	if maken == nil || maken.Op != OMAKESLICE {	// make(Type, Left, Right) (type is slice)
		return
	}
	if maken.Esc == EscNone {	// Does not escape to heap, result, or parameters.
		return
	}
	if maken.Left == nil || maken.Right != nil {
		return
	}
	if copyn.Op != OCOPY {	// copy(Left, Right)
		return
	}
	if copyn.Left.Op != ONAME {	// var or func name
		return
	}
	if asn.Left.Sym != copyn.Left.Sym {
		return
	}
	if copyn.Right.Op != ONAME {	// var or func name
		return
	}

	if copyn.Left.Sym == copyn.Right.Sym {
		return
	}

	maken.Op = OMAKESLICECOPY
	maken.Right = copyn.Right
	// Set bounded when m = OMAKESLICE([]T, len(s)); OCOPY(m, s)
	maken.SetBounded(maken.Left.Op == OLEN && samesafeexpr(maken.Left.Left, copyn.Right))

	maken = typecheck(maken, ctxExpr)

	s[1] = nil // remove separate copy call

	return
}

// edge inserts coverage instrumentation for libfuzzer.
func (o *Order) edge() {
	if Debug_libfuzzer == 0 {
		return
	}

	// Create a new uint8 counter to be allocated in section
	// __libfuzzer_extra_counters.
	counter := staticname(types.Types[TUINT8])
	counter.Name.SetLibfuzzerExtraCounter(true)

	// counter += 1
	incr := nod(OASOP, counter, nodintconst(1))
	incr.SetSubOp(OADD)
	incr = typecheck(incr, ctxStmt)

	o.out = append(o.out, incr)
}

// orderBlock orders the block of statements in n into a new slice,
// and then replaces the old slice in n with the new slice.
// free is a map that can be used to obtain temporary variables by type.
func orderBlock(n *Nodes, free map[string][]*Node) {
	var order Order
	order.free = free
	mark := order.markTemp()	// len(order.temp)
	order.edge()
	order.stmtList(*n)
	order.cleanTemp(mark)
	n.Set(order.out)
}

// exprInPlace orders the side effects in *np and
// leaves them as the init list of the final *np.
// The result of exprInPlace MUST be assigned back to n, e.g.
// 	n.Left = o.exprInPlace(n.Left)
func (o *Order) exprInPlace(n *Node) *Node {
	var order Order
	order.free = o.free
	n = order.expr(n, nil)
	n = addinit(n, order.out)

	// insert new temporaries from order
	// at head of outer list.
	o.temp = append(o.temp, order.temp...)
	return n
}

// orderStmtInPlace orders the side effects of the single statement *np
// and replaces it with the resulting statement list.
// The result of orderStmtInPlace MUST be assigned back to n, e.g.
// 	n.Left = orderStmtInPlace(n.Left)
// free is a map that can be used to obtain temporary variables by type.
func orderStmtInPlace(n *Node, free map[string][]*Node) *Node {
	var order Order
	order.free = free
	mark := order.markTemp()
	order.stmt(n)
	order.cleanTemp(mark)
	return liststmt(order.out)
}

// init moves n's init list to o.out.
func (o *Order) init(n *Node) {
	if n.mayBeShared() {
		// For concurrency safety, don't mutate potentially shared nodes.
		// First, ensure that no work is required here.
		if n.Ninit.Len() > 0 {
			Fatalf("order.init shared node with ninit")
		}
		return
	}
	o.stmtList(n.Ninit)
	n.Ninit.Set(nil)
}

// call orders the call expression n.
// n.Op is OCALLMETH/OCALLFUNC/OCALLINTER or a builtin like OCOPY.
func (o *Order) call(n *Node) {
	if n.Ninit.Len() > 0 {
		// Caller should have already called o.init(n).
		Fatalf("%v with unexpected ninit", n.Op)
	}

	// Builtin functions.
	if n.Op != OCALLFUNC && n.Op != OCALLMETH && n.Op != OCALLINTER {
		n.Left = o.expr(n.Left, nil)
		n.Right = o.expr(n.Right, nil)
		o.exprList(n.List)
		return
	}

	fixVariadicCall(n)	// 将可变列表参数转化为一个切片
	n.Left = o.expr(n.Left, nil)
	o.exprList(n.List)

	if n.Op == OCALLINTER {	// 接口调用的函数就返回
		return
	}
	keepAlive := func(arg *Node) {
		// If the argument is really a pointer being converted to uintptr,
		// arrange for the pointer to be kept alive until the call returns,
		// by copying it into a temp and marking that temp
		// still alive when we pop the temp stack.
		if arg.Op == OCONVNOP && arg.Left.Type.IsUnsafePtr() {
			x := o.copyExpr(arg.Left, arg.Left.Type, false)
			x.Name.SetKeepalive(true)
			arg.Left = x
		}
	}

	// Check for "unsafe-uintptr" tag provided by escape analysis.
	for i, param := range n.Left.Type.Params().FieldSlice() {	// 遍历函数声明的入参
		if param.Note == unsafeUintptrTag || param.Note == uintptrEscapesTag {
			if arg := n.List.Index(i); arg.Op == OSLICELIT {	// 第i个参数是一个切片字面量
				for _, elt := range arg.List.Slice() {	// 遍历切片中的元素
					keepAlive(elt)
				}
			} else {
				keepAlive(arg)
			}
		}
	}
}

// mapAssign appends n to o.out, introducing temporaries
// to make sure that all map assignments have the form m[k] = x.
// (Note: expr has already been called on n, so we know k is addressable.)
//
// If n is the multiple assignment form ..., m[k], ... = ..., x, ..., the rewrite is
//	t1 = m
//	t2 = k
//	...., t3, ... = ..., x, ...
//	t1[t2] = t3
//
// The temporaries t1, t2 are needed in case the ... being assigned
// contain m or k. They are usually unnecessary, but in the unnecessary
// cases they are also typically registerizable, so not much harm done.
// And this only applies to the multiple-assignment form.
// We could do a more precise analysis if needed, like in walk.go.
func (o *Order) mapAssign(n *Node) {
	switch n.Op {
	default:
		Fatalf("order.mapAssign %v", n.Op)

	case OAS, OASOP:
		if n.Left.Op == OINDEXMAP {
			// Make sure we evaluate the RHS before starting the map insert.
			// We need to make sure the RHS won't panic.  See issue 22881.
			if n.Right.Op == OAPPEND {
				s := n.Right.List.Slice()[1:]
				for i, n := range s {
					s[i] = o.cheapExpr(n)
				}
			} else {
				n.Right = o.cheapExpr(n.Right)
			}
		}
		o.out = append(o.out, n)

	case OAS2, OAS2DOTTYPE, OAS2MAPR, OAS2FUNC:
		var post []*Node
		for i, m := range n.List.Slice() {
			switch {
			case m.Op == OINDEXMAP:
				if !m.Left.IsAutoTmp() {
					m.Left = o.copyExpr(m.Left, m.Left.Type, false)
				}
				if !m.Right.IsAutoTmp() {
					m.Right = o.copyExpr(m.Right, m.Right.Type, false)
				}
				fallthrough
			case instrumenting && n.Op == OAS2FUNC && !m.isBlank():
				t := o.newTemp(m.Type, false)
				n.List.SetIndex(i, t)
				a := nod(OAS, m, t)
				a = typecheck(a, ctxStmt)
				post = append(post, a)
			}
		}

		o.out = append(o.out, n)
		o.out = append(o.out, post...)
	}
}

// stmt orders the statement n, appending to o.out.
// Temporaries created during the statement are cleaned
// up using VARKILL instructions as possible.
func (o *Order) stmt(n *Node) {
	if n == nil {
		return
	}

	lno := setlineno(n)
	o.init(n)

	switch n.Op {
	default:
		Fatalf("order.stmt %v", n.Op)

	case OVARKILL, OVARLIVE, OINLMARK:
		o.out = append(o.out, n)

	case OAS:	// Left = Right or (if Colas=true) Left := Right	20
		t := o.markTemp()	// 获取o.temp的length
		n.Left = o.expr(n.Left, nil)
		n.Right = o.expr(n.Right, n.Left)
		o.mapAssign(n)
		o.cleanTemp(t)

	case OASOP:	// Left Etype= Right (x += y)
		t := o.markTemp()
		n.Left = o.expr(n.Left, nil)
		n.Right = o.expr(n.Right, nil)

		if instrumenting || n.Left.Op == OINDEXMAP && (n.SubOp() == ODIV || n.SubOp() == OMOD) {
			// Rewrite m[k] op= r into m[k] = m[k] op r so
			// that we can ensure that if op panics
			// because r is zero, the panic happens before
			// the map assignment.

			n.Left = o.safeExpr(n.Left)

			l := treecopy(n.Left, src.NoXPos)
			if l.Op == OINDEXMAP {
				l.SetIndexMapLValue(false)
			}
			l = o.copyExpr(l, n.Left.Type, false)
			n.Right = nod(n.SubOp(), l, n.Right)
			n.Right = typecheck(n.Right, ctxExpr)
			n.Right = o.expr(n.Right, nil)

			n.Op = OAS
			n.ResetAux()
		}

		o.mapAssign(n)
		o.cleanTemp(t)

	case OAS2:
		t := o.markTemp()
		o.exprList(n.List)
		o.exprList(n.Rlist)
		o.mapAssign(n)
		o.cleanTemp(t)

	// Special: avoid copy of func call n.Right
	case OAS2FUNC:
		t := o.markTemp()
		o.exprList(n.List)
		o.init(n.Right)
		o.call(n.Right)
		o.as2(n)
		o.cleanTemp(t)

	// Special: use temporary variables to hold result,
	// so that runtime can take address of temporary.
	// No temporary for blank assignment.
	//
	// OAS2MAPR: make sure key is addressable if needed,
	//           and make sure OINDEXMAP is not copied out.
	case OAS2DOTTYPE, OAS2RECV, OAS2MAPR:
		t := o.markTemp()
		o.exprList(n.List)

		switch r := n.Right; r.Op {
		case ODOTTYPE2, ORECV:
			r.Left = o.expr(r.Left, nil)
		case OINDEXMAP:
			r.Left = o.expr(r.Left, nil)
			r.Right = o.expr(r.Right, nil)
			// See similar conversion for OINDEXMAP below.
			_ = mapKeyReplaceStrConv(r.Right)
			r.Right = o.mapKeyTemp(r.Left.Type, r.Right)
		default:
			Fatalf("order.stmt: %v", r.Op)
		}

		o.okAs2(n)
		o.cleanTemp(t)

	// Special: does not save n onto out.
	case OBLOCK, OEMPTY:
		o.stmtList(n.List)

	// Special: n->left is not an expression; save as is.
	case OBREAK,
		OCONTINUE,
		ODCL,
		ODCLCONST,
		ODCLTYPE,
		OFALL,
		OGOTO,
		OLABEL,
		ORETJMP:
		o.out = append(o.out, n)

	// Special: handle call arguments.
	case OCALLFUNC, OCALLINTER, OCALLMETH:
		t := o.markTemp()
		o.call(n)
		o.out = append(o.out, n)
		o.cleanTemp(t)

	case OCLOSE,
		OCOPY,
		OPRINT,
		OPRINTN,
		ORECOVER,
		ORECV:
		t := o.markTemp()	// 记录当前o.temp的数组长度
		n.Left = o.expr(n.Left, nil)
		n.Right = o.expr(n.Right, nil)
		o.exprList(n.List)
		o.exprList(n.Rlist)
		o.out = append(o.out, n)	// o.out添加当前的节点
		o.cleanTemp(t)

	// Special: order arguments to inner call but not call itself.
	case ODEFER, OGO:
		t := o.markTemp()
		o.init(n.Left)
		o.call(n.Left)
		o.out = append(o.out, n)
		o.cleanTemp(t)

	case ODELETE:	// delete(Left, Right)
		t := o.markTemp()
		n.List.SetFirst(o.expr(n.List.First(), nil))
		n.List.SetSecond(o.expr(n.List.Second(), nil))
		n.List.SetSecond(o.mapKeyTemp(n.List.First().Type, n.List.Second()))
		o.out = append(o.out, n)
		o.cleanTemp(t)

	// Clean temporaries from condition evaluation at
	// beginning of loop body and after for statement.
	case OFOR:	// for Ninit; Left; Right { Nbody }
		t := o.markTemp()
		n.Left = o.exprInPlace(n.Left)
		n.Nbody.Prepend(o.cleanTempNoPop(t)...)
		orderBlock(&n.Nbody, o.free)
		n.Right = orderStmtInPlace(n.Right, o.free)
		o.out = append(o.out, n)
		o.cleanTemp(t)

	// Clean temporaries from condition at
	// beginning of both branches.
	case OIF:
		t := o.markTemp()
		n.Left = o.exprInPlace(n.Left)
		n.Nbody.Prepend(o.cleanTempNoPop(t)...)
		n.Rlist.Prepend(o.cleanTempNoPop(t)...)
		o.popTemp(t)
		orderBlock(&n.Nbody, o.free)
		orderBlock(&n.Rlist, o.free)
		o.out = append(o.out, n)

	// Special: argument will be converted to interface using convT2E
	// so make sure it is an addressable temporary.
	case OPANIC:	// panic(Left)
		t := o.markTemp()
		n.Left = o.expr(n.Left, nil)
		if !n.Left.Type.IsInterface() {
			n.Left = o.addrTemp(n.Left)
		}
		o.out = append(o.out, n)
		o.cleanTemp(t)

	case ORANGE:	 // for List = range Right { Nbody }
		// n.Right is the expression being ranged over.
		// order it, and then make a copy if we need one.
		// We almost always do, to ensure that we don't
		// see any value changes made during the loop.
		// Usually the copy is cheap (e.g., array pointer,
		// chan, slice, string are all tiny).
		// The exception is ranging over an array value
		// (not a slice, not a pointer to array),
		// which must make a copy to avoid seeing updates made during
		// the range body. Ranging over an array value is uncommon though.

		// Mark []byte(str) range expression to reuse string backing storage.
		// It is safe because the storage cannot be mutated.
		if n.Right.Op == OSTR2BYTES {
			n.Right.Op = OSTR2BYTESTMP
		}

		t := o.markTemp()
		n.Right = o.expr(n.Right, nil)

		orderBody := true
		switch n.Type.Etype {
		default:
			Fatalf("order.stmt range %v", n.Type)

		case TARRAY, TSLICE:
			if n.List.Len() < 2 || n.List.Second().isBlank() {
				// for i := range x will only use x once, to compute len(x).
				// No need to copy it.
				break
			}
			fallthrough

		case TCHAN, TSTRING:
			// chan, string, slice, array ranges use value multiple times.
			// make copy.
			r := n.Right	// 获取range后面的节点

			if r.Type.IsString() && r.Type != types.Types[TSTRING] {
				r = nod(OCONV, r, nil)	 // Type(Left) (type conversion)
				r.Type = types.Types[TSTRING]	// 将r转为String
				r = typecheck(r, ctxExpr)
			}

			n.Right = o.copyExpr(r, r.Type, false) 	// make copy

		case TMAP:
			if isMapClear(n) {
				// Preserve the body of the map clear pattern so it can
				// be detected during walk. The loop body will not be used
				// when optimizing away the range loop to a runtime call.
				orderBody = false
				break
			}

			// copy the map value in case it is a map literal.
			// TODO(rsc): Make tmp = literal expressions reuse tmp.
			// For maps tmp is just one word so it hardly matters.
			r := n.Right
			n.Right = o.copyExpr(r, r.Type, false)

			// prealloc[n] is the temp for the iterator.
			// hiter contains pointers and needs to be zeroed.
			prealloc[n] = o.newTemp(hiter(n.Type), true)
		}
		o.exprListInPlace(n.List)
		if orderBody {
			orderBlock(&n.Nbody, o.free)
		}
		o.out = append(o.out, n)
		o.cleanTemp(t)

	case ORETURN:	// return List
		o.exprList(n.List)
		o.out = append(o.out, n)

	// Special: clean case temporaries in each block entry.
	// Select must enter one of its blocks, so there is no
	// need for a cleaning at the end.
	// Doubly special: evaluation order for select is stricter
	// than ordinary expressions. Even something like p.c
	// has to be hoisted into a temporary, so that it cannot be
	// reordered after the channel evaluation for a different
	// case (if p were nil, then the timing of the fault would
	// give this away).
	case OSELECT:	// select { List } (List is list of OCASE)
		t := o.markTemp()	// 当前栈中临时变量的数量

		for _, n2 := range n.List.Slice() {	// 遍历select中的所有case块
			if n2.Op != OCASE {
				Fatalf("order select case %v", n2.Op)
			}
			r := n2.Left	// 获取case之后的expr
			setlineno(n2)

			// Append any new body prologue to ninit.
			// The next loop will insert ninit into nbody.
			if n2.Ninit.Len() != 0 {
				Fatalf("order select ninit")
			}
			if r == nil {
				continue
			}
			switch r.Op {
			default:
				Dump("select case", r)
				Fatalf("unknown op in select %v", r.Op)

			// If this is case x := <-ch or case x, y := <-ch, the case has
			// the ODCL nodes to declare x and y. We want to delay that
			// declaration (and possible allocation) until inside the case body.
			// Delete the ODCL nodes here and recreate them inside the body below.
			case OSELRECV, OSELRECV2:	// Left = <-Right.Left: (appears as .Left of OCASE; Right.Op == ORECV), List = <-Right.Left: (appears as .Left of OCASE; count(List) == 2, Right.Op == ORECV)
				if r.Colas() {	// 存在:=
					i := 0	// 存储这个case中声明的变量数量
					if r.Ninit.Len() != 0 && r.Ninit.First().Op == ODCL && r.Ninit.First().Left == r.Left {	// case 有一个变量接收,这里表示在Ninit中先声明了Left变量
						i++
					}
					if i < r.Ninit.Len() && r.Ninit.Index(i).Op == ODCL && r.List.Len() != 0 && r.Ninit.Index(i).Left == r.List.First() { // case 有两个变量接收
						i++
					}
					if i >= r.Ninit.Len() {	// Delete the ODCL nodes here
						r.Ninit.Set(nil)
					}
				}

				if r.Ninit.Len() != 0 {
					dumplist("ninit", r.Ninit)
					Fatalf("ninit on select recv")
				}

				// case x = <-c
				// case x, ok = <-c
				// r->left is x, r->ntest is ok, r->right is ORECV, r->right->left is c.
				// r->left == N means 'case <-c'.
				// c is always evaluated; x and ok are only evaluated when assigned.
				r.Right.Left = o.expr(r.Right.Left, nil)

				if r.Right.Left.Op != ONAME {
					r.Right.Left = o.copyExpr(r.Right.Left, r.Right.Left.Type, false)
				}

				// Introduce temporary for receive and move actual copy into case body.
				// avoids problems with target being addressed, as usual.
				// NOTE: If we wanted to be clever, we could arrange for just one
				// temporary per distinct type, sharing the temp among all receives
				// with that temp. Similarly one ok bool could be shared among all
				// the x,ok receives. Not worth doing until there's a clear need.
				if r.Left != nil && r.Left.isBlank() {	// 接收管道的是一个_	
					r.Left = nil	// 忽略接收的值
				}
				if r.Left != nil {	// 存在接收的值且只有一个
					// use channel element type for temporary to avoid conversions,
					// such as in case interfacevalue = <-intchan.
					// the conversion happens in the OAS instead.
					tmp1 := r.Left	// case后的第一个变量

					if r.Colas() {	// 通过:=的方式进行的赋值
						tmp2 := nod(ODCL, tmp1, nil)	// 声明tmp1变量
						tmp2 = typecheck(tmp2, ctxStmt)
						n2.Ninit.Append(tmp2)	// 添加被赋值的变量的临时变量的声明
					}

					r.Left = o.newTemp(r.Right.Left.Type.Elem(), r.Right.Left.Type.Elem().HasPointers())	// 新建一个与管道的元素相同类型的临时变量
					tmp2 := nod(OAS, tmp1, r.Left)	// case后的变量赋值为通过管道元素类型创建的临时变量
					tmp2 = typecheck(tmp2, ctxStmt)
					n2.Ninit.Append(tmp2)
				}

				if r.List.Len() != 0 && r.List.First().isBlank() {	// 如果存在第二个变量且第二个变量是_就忽略
					r.List.Set(nil)
				}
				if r.List.Len() != 0 {	// 两个变量接收
					tmp1 := r.List.First()	// 第二个变量节点
					if r.Colas() {	// 通过:=的方式进行的赋值
						tmp2 := nod(ODCL, tmp1, nil)	// 声明tmp1变量
						tmp2 = typecheck(tmp2, ctxStmt)
						n2.Ninit.Append(tmp2)	// 添加声明
					}

					r.List.Set1(o.newTemp(types.Types[TBOOL], false))	// 将一个布尔类型的临时变量放到List中
					tmp2 := okas(tmp1, r.List.First())	// 将第二个变量强转为布尔类型并赋值
					tmp2 = typecheck(tmp2, ctxStmt)
					n2.Ninit.Append(tmp2)
				}
				orderBlock(&n2.Ninit, o.free)

			case OSEND:	// Left <- Right, Left is channel
				if r.Ninit.Len() != 0 {
					dumplist("ninit", r.Ninit)
					Fatalf("ninit on select send")
				}

				// case c <- x
				// r->left is c, r->right is x, both are always evaluated.
				r.Left = o.expr(r.Left, nil)

				if !r.Left.IsAutoTmp() {	// 如果c不是临时变量就创建一个临时变量
					r.Left = o.copyExpr(r.Left, r.Left.Type, false)
				}
				r.Right = o.expr(r.Right, nil)
				if !r.Right.IsAutoTmp() {
					r.Right = o.copyExpr(r.Right, r.Right.Type, false)
				}
			}
		}
		// Now that we have accumulated all the temporaries, clean them.
		// Also insert any ninit queued during the previous loop.
		// (The temporary cleaning must follow that ninit work.)
		for _, n3 := range n.List.Slice() {	// 再次遍历所有的case
			orderBlock(&n3.Nbody, o.free)	// order case块中的语句
			n3.Nbody.Prepend(o.cleanTempNoPop(t)...)

			// TODO(mdempsky): Is this actually necessary?
			// walkselect appears to walk Ninit.
			n3.Nbody.Prepend(n3.Ninit.Slice()...)
			n3.Ninit.Set(nil)
		}

		o.out = append(o.out, n)
		o.popTemp(t)

	// Special: value being sent is passed as a pointer; make it addressable.
	case OSEND:	// Left <- Right, Left is channel, Right is value
		t := o.markTemp()
		n.Left = o.expr(n.Left, nil)
		n.Right = o.expr(n.Right, nil)
		if instrumenting {
			// Force copying to the stack so that (chan T)(nil) <- x
			// is still instrumented as a read of x.
			n.Right = o.copyExpr(n.Right, n.Right.Type, false)
		} else {
			n.Right = o.addrTemp(n.Right)	// 取Right的地址
		}
		o.out = append(o.out, n)
		o.cleanTemp(t)

	// TODO(rsc): Clean temporaries more aggressively.
	// Note that because walkswitch will rewrite some of the
	// switch into a binary search, this is not as easy as it looks.
	// (If we ran that code here we could invoke order.stmt on
	// the if-else chain instead.)
	// For now just clean all the temporaries at the end.
	// In practice that's fine.
	case OSWITCH:	// switch Ninit; Left { List } (List is a list of OCASE)
		if Debug_libfuzzer != 0 && !hasDefaultCase(n) {
			// Add empty "default:" case for instrumentation.
			n.List.Append(nod(OCASE, nil, nil))
		}

		t := o.markTemp()	//len(o.temp)
		n.Left = o.expr(n.Left, nil)
		for _, ncas := range n.List.Slice() {	// 遍历所有的case块
			if ncas.Op != OCASE {
				Fatalf("order switch case %v", ncas.Op)
			}
			o.exprListInPlace(ncas.List)	// 处理一个case关键字到:之间的多个表达式
			orderBlock(&ncas.Nbody, o.free)
		}

		o.out = append(o.out, n)
		o.cleanTemp(t)
	}

	lineno = lno
}

func hasDefaultCase(n *Node) bool {
	for _, ncas := range n.List.Slice() {
		if ncas.Op != OCASE {
			Fatalf("expected case, found %v", ncas.Op)
		}
		if ncas.List.Len() == 0 {
			return true
		}
	}
	return false
}

// exprList orders the expression list l into o.
func (o *Order) exprList(l Nodes) {
	s := l.Slice()
	for i := range s {
		s[i] = o.expr(s[i], nil)
	}
}

// exprListInPlace orders the expression list l but saves
// the side effects on the individual expression ninit lists.
func (o *Order) exprListInPlace(l Nodes) {
	s := l.Slice()
	for i := range s {
		s[i] = o.exprInPlace(s[i])
	}
}

// prealloc[x] records the allocation to use for x.  该空间是为临时变量申请的
var prealloc = map[*Node]*Node{}

// expr orders a single expression, appending side
// effects to o.out as needed.
// If this is part of an assignment lhs = *np, lhs is given.
// Otherwise lhs == nil. (When lhs != nil it may be possible
// to avoid copying the result of the expression to a temporary.)
// The result of expr MUST be assigned back to n, e.g.
// 	n.Left = o.expr(n.Left, lhs)
func (o *Order) expr(n, lhs *Node) *Node {
	if n == nil {
		return n
	}

	lno := setlineno(n)
	o.init(n)

	switch n.Op {
	default:
		n.Left = o.expr(n.Left, nil)
		n.Right = o.expr(n.Right, nil)
		o.exprList(n.List)
		o.exprList(n.Rlist)

	// Addition of strings turns into a function call.
	// Allocate a temporary to hold the strings.
	// Fewer than 5 strings use direct runtime helpers.
	case OADDSTR:	// +{List} (string addition, list elements are strings)
		o.exprList(n.List)

		if n.List.Len() > 5 {
			t := types.NewArray(types.Types[TSTRING], int64(n.List.Len()))
			prealloc[n] = o.newTemp(t, false)
		}

		// Mark string(byteSlice) arguments to reuse byteSlice backing
		// buffer during conversion. String concatenation does not
		// memorize the strings for later use, so it is safe.
		// However, we can do it only if there is at least one non-empty string literal.
		// Otherwise if all other arguments are empty strings,
		// concatstrings will return the reference to the temp string
		// to the caller.
		hasbyte := false	// 是否有byte强转为string后进行字符串拼接的

		haslit := false	// 是否有字符串常量
		for _, n1 := range n.List.Slice() {
			hasbyte = hasbyte || n1.Op == OBYTES2STR
			haslit = haslit || n1.Op == OLITERAL && len(strlit(n1)) != 0
		}

		if haslit && hasbyte {
			for _, n2 := range n.List.Slice() {
				if n2.Op == OBYTES2STR {
					n2.Op = OBYTES2STRTMP
				}
			}
		}

	case OINDEXMAP:	 // Left[Right] (index of map)
		n.Left = o.expr(n.Left, nil)
		n.Right = o.expr(n.Right, nil)
		needCopy := false

		if !n.IndexMapLValue() {	// 为true时，n.aux == 0，这里是判断是否是一个map[index] = xxx的赋值语句
			// Enforce that any []byte slices we are not copying
			// can not be changed before the map index by forcing
			// the map index to happen immediately following the
			// conversions. See copyExpr a few lines below.
			needCopy = mapKeyReplaceStrConv(n.Right)

			if instrumenting {
				// Race detector needs the copy so it can
				// call treecopy on the result.
				needCopy = true
			}
		}

		// key must be addressable
		n.Right = o.mapKeyTemp(n.Left.Type, n.Right)
		if needCopy {
			n = o.copyExpr(n, n.Type, false)
		}

	// concrete type (not interface) argument might need an addressable
	// temporary to pass to the runtime conversion routine.
	case OCONVIFACE:	// Type(Left) (type conversion, to interface)
		n.Left = o.expr(n.Left, nil)
		if n.Left.Type.IsInterface() {
			break
		}
		if _, needsaddr := convFuncName(n.Left.Type, n.Type); needsaddr || isStaticCompositeLiteral(n.Left) {
			// Need a temp if we need to pass the address to the conversion function.
			// We also process static composite literal node here, making a named static global
			// whose address we can put directly in an interface (see OCONVIFACE case in walk).
			n.Left = o.addrTemp(n.Left)
		}

	case OCONVNOP:
		if n.Type.IsKind(TUNSAFEPTR) && n.Left.Type.IsKind(TUINTPTR) && (n.Left.Op == OCALLFUNC || n.Left.Op == OCALLINTER || n.Left.Op == OCALLMETH) {	// unsafe.Pointer(f())
			// When reordering unsafe.Pointer(f()) into a separate
			// statement, the conversion and function call must stay
			// together. See golang.org/issue/15329.
			o.init(n.Left)
			o.call(n.Left)
			if lhs == nil || lhs.Op != ONAME || instrumenting {
				n = o.copyExpr(n, n.Type, false)
			}
		} else {
			n.Left = o.expr(n.Left, nil)
		}

	case OANDAND, OOROR:
		// ... = LHS && RHS
		//
		// var r bool
		// r = LHS
		// if r {       // or !r, for OROR
		//     r = RHS
		// }
		// ... = r

		r := o.newTemp(n.Type, false)	// var r bool

		// Evaluate left-hand side.
		lhs := o.expr(n.Left, nil)	
		o.out = append(o.out, typecheck(nod(OAS, r, lhs), ctxStmt))	// r = LHS

		// Evaluate right-hand side, save generated code.
		saveout := o.out
		o.out = nil
		t := o.markTemp()
		o.edge()
		rhs := o.expr(n.Right, nil)
		o.out = append(o.out, typecheck(nod(OAS, r, rhs), ctxStmt))	// r = RHS
		o.cleanTemp(t)
		gen := o.out	// 这里的gen是短路运算右部产生的
		o.out = saveout

		// If left-hand side doesn't cause a short-circuit, issue right-hand side.
		nif := nod(OIF, r, nil)	// if Ninit; Left { Nbody } else { Rlist }		这里判断了r的结果
		if n.Op == OANDAND {
			nif.Nbody.Set(gen)	// 这里的意思为先判断右边
		} else {
			nif.Rlist.Set(gen)
		}
		o.out = append(o.out, nif)
		n = r

	case OCALLFUNC,
		OCALLINTER,
		OCALLMETH,
		OCAP,
		OCOMPLEX,
		OCOPY,
		OIMAG,
		OLEN,
		OMAKECHAN,
		OMAKEMAP,
		OMAKESLICE,
		OMAKESLICECOPY,
		ONEW,
		OREAL,
		ORECOVER,
		OSTR2BYTES,
		OSTR2BYTESTMP,
		OSTR2RUNES:

		if isRuneCount(n) {
			// len([]rune(s)) is rewritten to runtime.countrunes(s) later.
			n.Left.Left = o.expr(n.Left.Left, nil)
		} else {
			o.call(n)
		}

		if lhs == nil || lhs.Op != ONAME || instrumenting {
			n = o.copyExpr(n, n.Type, false)
		}

	case OAPPEND:
		// Check for append(x, make([]T, y)...) .
		if isAppendOfMake(n) {
			n.List.SetFirst(o.expr(n.List.First(), nil))             // order x
			n.List.Second().Left = o.expr(n.List.Second().Left, nil) // order y
		} else {
			o.exprList(n.List)
		}

		if lhs == nil || lhs.Op != ONAME && !samesafeexpr(lhs, n.List.First()) {
			n = o.copyExpr(n, n.Type, false)
		}

	case OSLICE, OSLICEARR, OSLICESTR, OSLICE3, OSLICE3ARR:
		n.Left = o.expr(n.Left, nil)
		low, high, max := n.SliceBounds()
		low = o.expr(low, nil)
		low = o.cheapExpr(low)
		high = o.expr(high, nil)
		high = o.cheapExpr(high)
		max = o.expr(max, nil)
		max = o.cheapExpr(max)
		n.SetSliceBounds(low, high, max)
		if lhs == nil || lhs.Op != ONAME && !samesafeexpr(lhs, n.Left) {
			n = o.copyExpr(n, n.Type, false)
		}

	case OCLOSURE:
		if n.Transient() && n.Func.Closure.Func.Cvars.Len() > 0 {	// 未逃逸的闭包函数且外部函数被闭包引用的变量不为0
			prealloc[n] = o.newTemp(closureType(n), false)
		}

	case OSLICELIT, OCALLPART:
		n.Left = o.expr(n.Left, nil)
		n.Right = o.expr(n.Right, nil)
		o.exprList(n.List)
		o.exprList(n.Rlist)
		if n.Transient() {
			var t *types.Type
			switch n.Op {
			case OSLICELIT:
				t = types.NewArray(n.Type.Elem(), n.Right.Int64())
			case OCALLPART:
				t = partialCallType(n)
			}
			prealloc[n] = o.newTemp(t, false)
		}

	case ODOTTYPE, ODOTTYPE2:
		n.Left = o.expr(n.Left, nil)
		if !isdirectiface(n.Type) || instrumenting {
			n = o.copyExpr(n, n.Type, true)
		}

	case ORECV:	 // <-Left
		n.Left = o.expr(n.Left, nil)
		n = o.copyExpr(n, n.Type, true)

	case OEQ, ONE, OLT, OLE, OGT, OGE:
		n.Left = o.expr(n.Left, nil)
		n.Right = o.expr(n.Right, nil)

		t := n.Left.Type
		switch {
		case t.IsString():
			// Mark string(byteSlice) arguments to reuse byteSlice backing
			// buffer during conversion. String comparison does not
			// memorize the strings for later use, so it is safe.
			if n.Left.Op == OBYTES2STR {
				n.Left.Op = OBYTES2STRTMP
			}
			if n.Right.Op == OBYTES2STR {
				n.Right.Op = OBYTES2STRTMP
			}

		case t.IsStruct() || t.IsArray():
			// for complex comparisons, we need both args to be
			// addressable so we can pass them to the runtime.
			n.Left = o.addrTemp(n.Left)
			n.Right = o.addrTemp(n.Right)
		}
	case OMAPLIT:	// Type{List} (composite literal, Type is map)
		// Order map by converting:
		//   map[int]int{
		//     a(): b(),
		//     c(): d(),
		//     e(): f(),
		//   }
		// to
		//   m := map[int]int{}
		//   m[a()] = b()
		//   m[c()] = d()
		//   m[e()] = f()
		// Then order the result.
		// Without this special case, order would otherwise compute all
		// the keys and values before storing any of them to the map.
		// See issue 26552.
		entries := n.List.Slice()
		statics := entries[:0]
		var dynamics []*Node
		for _, r := range entries {	// 遍历所有键值对
			if r.Op != OKEY {
				Fatalf("OMAPLIT entry not OKEY: %v\n", r)
			}

			if !isStaticCompositeLiteral(r.Left) || !isStaticCompositeLiteral(r.Right) {	// r.Left与r.Right都不是编译时常量
				dynamics = append(dynamics, r)
				continue
			}

			// Recursively ordering some static entries can change them to dynamic;
			// e.g., OCONVIFACE nodes. See #31777.
			r = o.expr(r, nil)
			if !isStaticCompositeLiteral(r.Left) || !isStaticCompositeLiteral(r.Right) {
				dynamics = append(dynamics, r)
				continue
			}

			statics = append(statics, r)
		}
		n.List.Set(statics)	// key与value都是编译时常量的情况放到List中

		if len(dynamics) == 0 {
			break
		}

		// Emit the creation of the map (with all its static entries).
		m := o.newTemp(n.Type, false)
		as := nod(OAS, m, n)	// m = n
		typecheck(as, ctxStmt)
		o.stmt(as)
		n = m

		// Emit eval+insert of dynamic entries, one at a time.
		for _, r := range dynamics {
			as := nod(OAS, nod(OINDEX, n, r.Left), r.Right)	// Map[key] = value
			typecheck(as, ctxStmt) // Note: this converts the OINDEX to an OINDEXMAP
			o.stmt(as)
		}
	}

	lineno = lno
	return n
}

// okas creates and returns an assignment of val to ok,
// including an explicit conversion if necessary.
func okas(ok, val *Node) *Node {
	if !ok.isBlank() {
		val = conv(val, ok.Type)	// 将val强转为ok的类型
	}
	return nod(OAS, ok, val)	// ok = val
}

// as2 orders OAS2XXXX nodes. It creates temporaries to ensure left-to-right assignment.
// The caller should order the right-hand side of the assignment before calling order.as2.
// It rewrites,
// 	a, b, a = ...
// as
//	tmp1, tmp2, tmp3 = ...
// 	a, b, a = tmp1, tmp2, tmp3
// This is necessary to ensure left to right assignment order.
func (o *Order) as2(n *Node) {
	tmplist := []*Node{}
	left := []*Node{}
	for ni, l := range n.List.Slice() {
		if !l.isBlank() {
			tmp := o.newTemp(l.Type, l.Type.HasPointers())
			n.List.SetIndex(ni, tmp)
			tmplist = append(tmplist, tmp)
			left = append(left, l)
		}
	}

	o.out = append(o.out, n)

	as := nod(OAS2, nil, nil)
	as.List.Set(left)
	as.Rlist.Set(tmplist)
	as = typecheck(as, ctxStmt)
	o.stmt(as)
}

// okAs2 orders OAS2XXX with ok.
// Just like as2, this also adds temporaries to ensure left-to-right assignment.
func (o *Order) okAs2(n *Node) {
	var tmp1, tmp2 *Node
	if !n.List.First().isBlank() {
		typ := n.Right.Type
		tmp1 = o.newTemp(typ, typ.HasPointers())
	}

	if !n.List.Second().isBlank() {
		tmp2 = o.newTemp(types.Types[TBOOL], false)
	}

	o.out = append(o.out, n)

	if tmp1 != nil {
		r := nod(OAS, n.List.First(), tmp1)
		r = typecheck(r, ctxStmt)
		o.mapAssign(r)
		n.List.SetFirst(tmp1)
	}
	if tmp2 != nil {
		r := okas(n.List.Second(), tmp2)
		r = typecheck(r, ctxStmt)
		o.mapAssign(r)
		n.List.SetSecond(tmp2)
	}
}

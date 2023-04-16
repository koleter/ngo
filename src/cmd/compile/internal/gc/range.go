// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import (
	"cmd/compile/internal/types"
	"cmd/internal/sys"
	"unicode/utf8"
)

// range
func typecheckrange(n *Node) {
	// Typechecking order is important here:
	// 0. first typecheck range expression (slice/map/chan),
	//	it is evaluated only once and so logically it is not part of the loop.
	// 1. typecheck produced values,
	//	this part can declare new vars and so it must be typechecked before body,
	//	because body can contain a closure that captures the vars.
	// 2. decldepth++ to denote loop body.
	// 3. typecheck body.
	// 4. decldepth--.
	typecheckrangeExpr(n)

	// second half of dance, the first half being typecheckrangeExpr
	n.SetTypecheck(1)
	ls := n.List.Slice()
	for i1, n1 := range ls {
		if n1.Typecheck() == 0 {
			ls[i1] = typecheck(ls[i1], ctxExpr|ctxAssign)
		}
	}

	decldepth++
	typecheckslice(n.Nbody.Slice(), ctxStmt)
	decldepth--
}
// ORANGE:  List:=range Right    List表示左边的表达式列表
func typecheckrangeExpr(n *Node) {
	n.Right = typecheck(n.Right, ctxExpr)

	t := n.Right.Type
	if t == nil {
		return
	}
	// delicate little dance.  see typecheckas2
	ls := n.List.Slice()
	for i1, n1 := range ls {
		if n1.Name == nil || n1.Name.Defn != n {
			ls[i1] = typecheck(ls[i1], ctxExpr|ctxAssign)
		}
	}

	if t.IsPtr() && t.Elem().IsArray() {
		t = t.Elem()
	}
	n.Type = t
	// t1与t2代表了range前面接收变量的类型
	var t1, t2 *types.Type
	toomany := false
	switch t.Etype {
	default:
		yyerrorl(n.Pos, "cannot range over %L", n.Right)
		return

	case TARRAY, TSLICE:
		t1 = types.Types[TINT]	// 此时t1表示index的类型
		t2 = t.Elem()		// 此时t2表示数组或切片中元素的类型

	case TMAP:
		t1 = t.Key()
		t2 = t.Elem()

	case TCHAN:
		if !t.ChanDir().CanRecv() {
			yyerrorl(n.Pos, "invalid operation: range %v (receive from send-only type %v)", n.Right, n.Right.Type)
			return
		}

		t1 = t.Elem()
		t2 = nil
		if n.List.Len() == 2 {
			toomany = true
		}

	case TSTRING:
		t1 = types.Types[TINT]
		t2 = types.Runetype
	}

	if n.List.Len() > 2 || toomany {
		yyerrorl(n.Pos, "too many variables in range")
	}

	var v1, v2 *Node
	if n.List.Len() != 0 {
		v1 = n.List.First()
	}
	if n.List.Len() > 1 {
		v2 = n.List.Second()
	}

	// this is not only an optimization but also a requirement in the spec.
	// "if the second iteration variable is the blank identifier, the range
	// clause is equivalent to the same clause with only the first variable
	// present."
	if v2.isBlank() {
		if v1 != nil {
			n.List.Set1(v1)
		}
		v2 = nil
	}

	var why string
	if v1 != nil {
		if v1.Name != nil && v1.Name.Defn == n {
			v1.Type = t1
		} else if v1.Type != nil && assignop(t1, v1.Type, &why) == 0 {
			yyerrorl(n.Pos, "cannot assign type %v to %L in range%s", t1, v1, why)
		}
		checkassign(n, v1)
	}

	if v2 != nil {
		if v2.Name != nil && v2.Name.Defn == n {
			v2.Type = t2
		} else if v2.Type != nil && assignop(t2, v2.Type, &why) == 0 {
			yyerrorl(n.Pos, "cannot assign type %v to %L in range%s", t2, v2, why)
		}
		checkassign(n, v2)
	}
}

func cheapComputableIndex(width int64) bool {
	switch thearch.LinkArch.Family {
	// MIPS does not have R+R addressing
	// Arm64 may lack ability to generate this code in our assembler,
	// but the architecture supports it.
	case sys.PPC64, sys.S390X:
		return width == 1
	case sys.AMD64, sys.I386, sys.ARM64, sys.ARM:
		switch width {
		case 1, 2, 4, 8:
			return true
		}
	}
	return false
}

// walkrange transforms various forms of ORANGE into
// simpler forms.  The result must be assigned back to n.
// Node n may also be modified in place, and may also be
// the returned node.
func walkrange(n *Node) *Node {
	if isMapClear(n) {
		m := n.Right
		lno := setlineno(m)
		n = mapClear(m)	// 通过内置的mapclear函数处理map的清空操作
		lineno = lno
		return n
	}

	// variable name conventions:
	//	ohv1, hv1, hv2: hidden (old) val 1, 2
	//	ha, hit: hidden aggregate, iterator
	//	hn, hp: hidden len, pointer
	//	hb: hidden bool
	//	a, v1, v2: not hidden aggregate, val 1, 2

	t := n.Type

	a := n.Right	// 获取range后面的变量
	lno := setlineno(a)
	n.Right = nil
	// v1与v2分别是接收range操作的两个变量
	var v1, v2 *Node
	l := n.List.Len()	// 接收range的变量列表
	if l > 0 {
		v1 = n.List.First()
	}

	if l > 1 {
		v2 = n.List.Second()
	}

	if v2.isBlank() {
		v2 = nil
	}

	if v1.isBlank() && v2 == nil {	// _ := range xxx
		v1 = nil
	}

	if v1 == nil && v2 != nil {	// 这种情况应该不会发生
		Fatalf("walkrange: v2 != nil while v1 == nil")
	}

	// n.List has no meaning anymore, clear it
	// to avoid erroneous processing by racewalk.
	n.List.Set(nil)

	var ifGuard *Node

	translatedLoopOp := OFOR

	var body []*Node
	var init []*Node
	switch t.Etype {
	default:
		Fatalf("walkrange")

	case TARRAY, TSLICE:
		if arrayClear(n, v1, v2, a) {
			lineno = lno
			return n
		}

		// order.stmt arranged for a copy of the array/slice variable if needed.
		ha := a

		hv1 := temp(types.Types[TINT])
		hn := temp(types.Types[TINT])	// 数组容量	len(ha)

		init = append(init, nod(OAS, hv1, nil))	// hv1 := 0
		init = append(init, nod(OAS, hn, nod(OLEN, ha, nil)))	// hn = len(ha)

		n.Left = nod(OLT, hv1, hn)	// hv1 < len(a)
		n.Right = nod(OAS, hv1, nod(OADD, hv1, nodintconst(1)))	// hv1 = hv1 + 1

		// for range ha { body }
		if v1 == nil {
			break
		}

		// for v1 := range ha { body }
		if v2 == nil {
			body = []*Node{nod(OAS, v1, hv1)}	// 这表示只有一个接收变量时该变量是数组的index
			break
		}

		// for v1, v2 := range ha { body }
		if cheapComputableIndex(n.Type.Elem().Width) {
			// v1, v2 = hv1, ha[hv1]
			tmp := nod(OINDEX, ha, hv1)	// ha[hv1]
			tmp.SetBounded(true)	// 设置不需要边界检查
			// Use OAS2 to correctly handle assignments
			// of the form "v1, a[v1] := range".
			a := nod(OAS2, nil, nil)
			a.List.Set2(v1, v2)
			a.Rlist.Set2(hv1, tmp)
			body = []*Node{a}
			break
		}

		// TODO(austin): OFORUNTIL is a strange beast, but is
		// necessary for expressing the control flow we need
		// while also making "break" and "continue" work. It
		// would be nice to just lower ORANGE during SSA, but
		// racewalk needs to see many of the operations
		// involved in ORANGE's implementation. If racewalk
		// moves into SSA, consider moving ORANGE into SSA and
		// eliminating OFORUNTIL.

		// TODO(austin): OFORUNTIL inhibits bounds-check
		// elimination on the index variable (see #20711).
		// Enhance the prove pass to understand this.
		ifGuard = nod(OIF, nil, nil)	// if hv1 < len(ha)
		ifGuard.Left = nod(OLT, hv1, hn)	// hv1 < len(ha)
		translatedLoopOp = OFORUNTIL

		hp := temp(types.NewPtr(n.Type.Elem()))	// 根据数组元素类型创建临时变量
		tmp := nod(OINDEX, ha, nodintconst(0))	// ha[0]
		tmp.SetBounded(true)
		init = append(init, nod(OAS, hp, nod(OADDR, tmp, nil)))	// hp = &ha[0]

		// Use OAS2 to correctly handle assignments
		// of the form "v1, a[v1] := range".
		a := nod(OAS2, nil, nil)
		a.List.Set2(v1, v2)
		a.Rlist.Set2(hv1, nod(ODEREF, hp, nil))	// 对第二个变量取地址再解引用是个什么操作?????
		body = append(body, a)

		// Advance pointer as part of the late increment.
		//
		// This runs *after* the condition check, so we know
		// advancing the pointer is safe and won't go past the
		// end of the allocation.
		a = nod(OAS, hp, addptr(hp, t.Elem().Width))	// 指针操作,获取下一个元素
		a = typecheck(a, ctxStmt)
		n.List.Set1(a)	// 设置range的接收参数

	case TMAP:
		// order.stmt allocated the iterator for us.
		// we only use a once, so no copy needed.
		ha := a

		hit := prealloc[n]	// 查看是否有为n申请的临时空间
		th := hit.Type
		n.Left = nil
		keysym := th.Field(0).Sym  // depends on layout of iterator struct.  See reflect.go:hiter
		elemsym := th.Field(1).Sym // ditto

		fn := syslook("mapiterinit")	// 找到内置的mapiterinit函数

		fn = substArgTypes(fn, t.Key(), t.Elem(), th)	// 替换fn的参数类型
		init = append(init, mkcall1(fn, nil, nil, typename(t), ha, nod(OADDR, hit, nil)))
		n.Left = nod(ONE, nodSym(ODOT, hit, keysym), nodnil())

		fn = syslook("mapiternext")
		fn = substArgTypes(fn, th)
		n.Right = mkcall1(fn, nil, nil, nod(OADDR, hit, nil))

		key := nodSym(ODOT, hit, keysym)	// hit.keysym
		key = nod(ODEREF, key, nil)	// *(hit.keysym)
		if v1 == nil {
			body = nil
		} else if v2 == nil {
			body = []*Node{nod(OAS, v1, key)}	// v1 = key
		} else {
			elem := nodSym(ODOT, hit, elemsym)
			elem = nod(ODEREF, elem, nil)
			a := nod(OAS2, nil, nil)
			a.List.Set2(v1, v2)
			a.Rlist.Set2(key, elem)
			body = []*Node{a}
		}

	case TCHAN:
		// order.stmt arranged for a copy of the channel variable.
		ha := a

		n.Left = nil

		hv1 := temp(t.Elem())	// 管道中元素类型的临时变量
		hv1.SetTypecheck(1)
		if t.Elem().HasPointers() {	// 有指针就先将临时变量赋值为nil
			init = append(init, nod(OAS, hv1, nil))
		}
		hb := temp(types.Types[TBOOL])	// 第二个临时变量

		n.Left = nod(ONE, hb, nodbool(false))	// hb != false
		a := nod(OAS2RECV, nil, nil)
		a.SetTypecheck(1)
		a.List.Set2(hv1, hb)	// 设置两个接收变量
		a.Right = nod(ORECV, ha, nil)	// <- ha
		n.Left.Ninit.Set1(a)	// 先执行hv1, hb := <- ha, 再判断hb != false
		if v1 == nil {
			body = nil
		} else {
			body = []*Node{nod(OAS, v1, hv1)}
		}
		// Zero hv1. This prevents hv1 from being the sole, inaccessible
		// reference to an otherwise GC-able value during the next channel receive.
		// See issue 15281.
		body = append(body, nod(OAS, hv1, nil))	// 将hv1置为nil便于GC进行垃圾回收

	case TSTRING:
		// Transform string range statements like "for v1, v2 = range a" into
		//
		// ha := a
		// for hv1 := 0; hv1 < len(ha); {
		//   hv1t := hv1
		//   hv2 := rune(ha[hv1])
		//   if hv2 < utf8.RuneSelf {
		//      hv1++
		//   } else {
		//      hv2, hv1 = decoderune(ha, hv1)
		//   }
		//   v1, v2 = hv1t, hv2
		//   // original body
		// }

		// order.stmt arranged for a copy of the string variable.
		ha := a

		hv1 := temp(types.Types[TINT])
		hv1t := temp(types.Types[TINT])
		hv2 := temp(types.Runetype)

		// hv1 := 0
		init = append(init, nod(OAS, hv1, nil))

		// hv1 < len(ha)
		n.Left = nod(OLT, hv1, nod(OLEN, ha, nil))

		if v1 != nil {	// 至少有一个接收变量
			// hv1t = hv1
			body = append(body, nod(OAS, hv1t, hv1))
		}

		// hv2 := rune(ha[hv1])
		nind := nod(OINDEX, ha, hv1)	// ha[hv1]
		nind.SetBounded(true)
		body = append(body, nod(OAS, hv2, conv(nind, types.Runetype)))	// hv2 := rune(ha[hv1])

		// if hv2 < utf8.RuneSelf
		nif := nod(OIF, nil, nil)
		nif.Left = nod(OLT, hv2, nodintconst(utf8.RuneSelf))

		// hv1++
		nif.Nbody.Set1(nod(OAS, hv1, nod(OADD, hv1, nodintconst(1))))

		// } else {
		eif := nod(OAS2, nil, nil)
		nif.Rlist.Set1(eif)

		// hv2, hv1 = decoderune(ha, hv1)
		eif.List.Set2(hv2, hv1)
		fn := syslook("decoderune")
		eif.Rlist.Set1(mkcall1(fn, fn.Type.Results(), nil, ha, hv1))

		body = append(body, nif)

		if v1 != nil {
			if v2 != nil {
				// v1, v2 = hv1t, hv2
				a := nod(OAS2, nil, nil)
				a.List.Set2(v1, v2)
				a.Rlist.Set2(hv1t, hv2)
				body = append(body, a)
			} else {
				// v1 = hv1t
				body = append(body, nod(OAS, v1, hv1t))
			}
		}
	}

	n.Op = translatedLoopOp
	typecheckslice(init, ctxStmt)

	if ifGuard != nil {	// OFORUNTIL
		ifGuard.Ninit.Append(init...)
		ifGuard = typecheck(ifGuard, ctxStmt)
	} else {
		n.Ninit.Append(init...)
	}

	typecheckslice(n.Left.Ninit.Slice(), ctxStmt)

	n.Left = typecheck(n.Left, ctxExpr)
	n.Left = defaultlit(n.Left, nil)
	n.Right = typecheck(n.Right, ctxStmt)
	typecheckslice(body, ctxStmt)
	n.Nbody.Prepend(body...)

	if ifGuard != nil {
		ifGuard.Nbody.Set1(n)	// 设置true分支
		n = ifGuard
	}

	n = walkstmt(n)

	lineno = lno
	return n
}

// isMapClear checks if n is of the form:
//
// for k := range m {
//   delete(m, k)
// }
//
// where == for keys of map m is reflexive.
func isMapClear(n *Node) bool {
	if Debug['N'] != 0 || instrumenting {
		return false
	}
	// n.List存储了上方的k,保证不必出现第二个接收的变量
	if n.Op != ORANGE || n.Type.Etype != TMAP || n.List.Len() != 1 {
		return false
	}

	k := n.List.First()	// range语句中第一个接受的变量,上方注释中的k
	if k == nil || k.isBlank() {
		return false
	}

	// Require k to be a new variable name.
	if k.Name == nil || k.Name.Defn != n {	// k在之前定义过返回false
		return false
	}

	if n.Nbody.Len() != 1 {	// for range循环中只能有一条statement
		return false
	}

	stmt := n.Nbody.First() // only stmt in body
	if stmt == nil || stmt.Op != ODELETE {	// 这一条语句必须是delete
		return false
	}

	m := n.Right	// range右边的节点,这里是一个Map
	if !samesafeexpr(stmt.List.First(), m) || !samesafeexpr(stmt.List.Second(), k) {
		return false
	}

	// Keys where equality is not reflexive can not be deleted from maps.
	if !isreflexive(m.Type.Key()) {	// key要满足x == x这种比较为true的情况
		return false
	}

	return true
}

// mapClear constructs a call to runtime.mapclear for the map m.
func mapClear(m *Node) *Node {
	t := m.Type

	// instantiate mapclear(typ *type, hmap map[any]any)
	fn := syslook("mapclear")
	fn = substArgTypes(fn, t.Key(), t.Elem())
	n := mkcall1(fn, nil, nil, typename(t), m)

	n = typecheck(n, ctxStmt)
	n = walkstmt(n)

	return n
}

// Lower n into runtime·memclr if possible, for
// fast zeroing of slices and arrays (issue 5373).
// Look for instances of
//
// for i := range a {
// 	a[i] = zero
// }
//
// in which the evaluation of a is side-effect-free.
//
// Parameters are as in walkrange: "for v1, v2 = range a".
func arrayClear(n, v1, v2, a *Node) bool {
	if Debug['N'] != 0 || instrumenting {
		return false
	}

	if v1 == nil || v2 != nil {	// 这种情况应该不会出现
		return false
	}

	if n.Nbody.Len() != 1 || n.Nbody.First() == nil {	// 只能有一行statement
		return false
	}

	stmt := n.Nbody.First() // only stmt in body
	if stmt.Op != OAS || stmt.Left.Op != OINDEX {	// 这行语句需要是为数组的某个下标赋值
		return false
	}

	if !samesafeexpr(stmt.Left.Left, a) || !samesafeexpr(stmt.Left.Right, v1) {
		return false
	}

	elemsize := n.Type.Elem().Width	// 获取数组中元素的类型字节数
	if elemsize <= 0 || !isZero(stmt.Right) {	// 确定是要将一段内存赋值为0的操作
		return false
	}

	// Convert to
	// if len(a) != 0 {
	// 	hp = &a[0]
	// 	hn = len(a)*sizeof(elem(a))
	// 	memclr{NoHeap,Has}Pointers(hp, hn)
	// 	i = len(a) - 1
	// }
	n.Op = OIF

	n.Nbody.Set(nil)
	n.Left = nod(ONE, nod(OLEN, a, nil), nodintconst(0))	// if len(a) != 0

	// hp = &a[0]
	hp := temp(types.Types[TUNSAFEPTR])	// 创建一个unsafepointer类型的临时变量

	tmp := nod(OINDEX, a, nodintconst(0))	// a[0]
	tmp.SetBounded(true)	// 设置tmp不需要边界检查
	tmp = nod(OADDR, tmp, nil)	// &a[0]
	tmp = convnop(tmp, types.Types[TUNSAFEPTR])	// 将&a[0]转为unsafepointer类型
	n.Nbody.Append(nod(OAS, hp, tmp))	// 	hp = &a[0]

	// hn = len(a) * sizeof(elem(a))
	hn := temp(types.Types[TUINTPTR])

	tmp = nod(OLEN, a, nil)	// len(a)
	tmp = nod(OMUL, tmp, nodintconst(elemsize))	// len(a) * sizeof(elem(a))
	tmp = conv(tmp, types.Types[TUINTPTR])
	n.Nbody.Append(nod(OAS, hn, tmp))	// hn = len(a) * sizeof(elem(a))

	var fn *Node
	if a.Type.Elem().HasPointers() {	// 数组的元素类型中包含指针
		// memclrHasPointers(hp, hn)
		Curfn.Func.setWBPos(stmt.Pos)
		fn = mkcall("memclrHasPointers", nil, nil, hp, hn)
	} else {
		// memclrNoHeapPointers(hp, hn)
		fn = mkcall("memclrNoHeapPointers", nil, nil, hp, hn)
	}
	// 	memclr{NoHeap,Has}Pointers(hp, hn)
	n.Nbody.Append(fn)

	// i = len(a) - 1
	v1 = nod(OAS, v1, nod(OSUB, nod(OLEN, a, nil), nodintconst(1)))

	n.Nbody.Append(v1)

	n.Left = typecheck(n.Left, ctxExpr)
	n.Left = defaultlit(n.Left, nil)
	typecheckslice(n.Nbody.Slice(), ctxStmt)
	n = walkstmt(n)
	return true
}

// addptr returns (*T)(uintptr(p) + n).
func addptr(p *Node, n int64) *Node {
	t := p.Type
	// uintptr(p)
	p = nod(OCONVNOP, p, nil)
	p.Type = types.Types[TUINTPTR]

	p = nod(OADD, p, nodintconst(n))	// uintptr(p) + n
	// (*T)(uintptr(p) + n)
	p = nod(OCONVNOP, p, nil)
	p.Type = t

	return p
}

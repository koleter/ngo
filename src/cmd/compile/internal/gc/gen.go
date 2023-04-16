// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import (
	"cmd/compile/internal/types"
	"cmd/internal/obj"
	"cmd/internal/src"
	"strconv"
)

// sysfunc looks up Go function name in package runtime. This function
// must follow the internal calling convention.
func sysfunc(name string) *obj.LSym {
	s := Runtimepkg.Lookup(name)
	s.SetFunc(true)
	return s.Linksym()
}

// sysvar looks up a variable (or assembly function) name in package
// runtime. If this is a function, it may have a special calling
// convention.
func sysvar(name string) *obj.LSym {
	return Runtimepkg.Lookup(name).Linksym()
}

// isParamStackCopy reports whether this is the on-stack copy of a
// function parameter that moved to the heap.
func (n *Node) isParamStackCopy() bool {
	return n.Op == ONAME && (n.Class() == PPARAM || n.Class() == PPARAMOUT) && n.Name.Param.Heapaddr != nil
}

// isParamHeapCopy reports whether this is the on-heap copy of
// a function parameter that moved to the heap.
func (n *Node) isParamHeapCopy() bool {
	return n.Op == ONAME && n.Class() == PAUTOHEAP && n.Name.Param.Stackcopy != nil
}

// autotmpname returns the name for an autotmp variable numbered n.
func autotmpname(n int) string {
	// Give each tmp a different name so that they can be registerized.
	// Add a preceding . to avoid clashing with legal names.
	const prefix = ".autotmp_"
	// Start with a buffer big enough to hold a large n.
	b := []byte(prefix + "      ")[:len(prefix)]
	b = strconv.AppendInt(b, int64(n), 10)
	return types.InternString(b)
}

// make a new Node off the books	在curfn中创建一个新的t类型的临时变量
func tempAt(pos src.XPos, curfn *Node, t *types.Type) *Node {
	if curfn == nil {
		Fatalf("no curfn for tempAt")
	}
	if curfn.Func.Closure != nil && curfn.Op == OCLOSURE { // 处于闭包之中
		Dump("tempAt", curfn)
		Fatalf("adding tempAt to wrong closure function")
	}
	if t == nil {
		Fatalf("tempAt called with nil type")
	}
	// 创建一个新的供临时变量使用的Sym符号
	s := &types.Sym{
		Name: autotmpname(len(curfn.Func.Dcl)),
		Pkg:  localpkg,
	}
	n := newnamel(pos, s)  // 通过符号创建ONAME节点
	s.Def = asTypesNode(n) // 标记Sym在n上声明
	n.Type = t             // 设置临时变量的类型
	n.SetClass(PAUTO)      // local variables
	n.Esc = EscNever
	n.Name.Curfn = curfn
	n.Name.SetUsed(true)
	n.Name.SetAutoTemp(true)                   // 标记这是一个临时变量
	curfn.Func.Dcl = append(curfn.Func.Dcl, n) // 当前函数声明的变量列表中添加n

	dowidth(t)

	return n.Orig // 其实就是n
}

func temp(t *types.Type) *Node {
	return tempAt(lineno, Curfn, t)
}

func GenCallNode(call *Node, args ...*Node) *Node {
	node := nod(OCALL, call, nil)
	node.List.Set(args)
	return node
}

// 生成指定类型的切片字面量节点
func GenSliceLiteral(op Op, params []*Node) *Node {
	interfaceTypeNode := nod(op, nil, nil)
	array := nod(OTARRAY, nil, interfaceTypeNode)
	complit := nod(OCOMPLIT, nil, array)
	complit.List.Set(params)
	return complit
}

func GenOAS(l, r *Node) *Node {
	oas := nod(OAS, l, r)
	l.Name.Defn = oas
	oas.Ninit.Append(nod(ODCL, l, nil))
	return oas
}

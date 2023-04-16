// Copyright 2011 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

// Strongly connected components.
//
// Run analysis on minimal sets of mutually recursive functions
// or single non-recursive functions, bottom up.
//
// Finding these sets is finding strongly connected components
// by reverse topological order in the static call graph.
// The algorithm (known as Tarjan's algorithm) for doing that is taken from
// Sedgewick, Algorithms, Second Edition, p. 482, with two adaptations.
//
// First, a hidden closure function (n.Func.IsHiddenClosure()) cannot be the
// root of a connected component. Refusing to use it as a root
// forces it into the component of the function in which it appears.
// This is more convenient for escape analysis.
//
// Second, each function becomes two virtual nodes in the graph,
// with numbers n and n+1. We record the function's node number as n
// but search from node n+1. If the search tells us that the component
// number (min) is n+1, we know that this is a trivial component: one function
// plus its closures. If the search tells us that the component number is
// n, then there was a path from node n+1 back to node n, meaning that
// the function set is mutually recursive. The escape analysis can be
// more precise when analyzing a single non-recursive function than
// when analyzing a set of mutually recursive functions.

type bottomUpVisitor struct {
	analyze  func([]*Node, bool)
	visitgen uint32		// 自增的一个值
	nodeID   map[*Node]uint32	// 非闭包函数节点对应的唯一id编号
	stack    []*Node	// 保存非闭包函数节点的一个栈
}

// visitBottomUp invokes analyze on the ODCLFUNC nodes listed in list.
// It calls analyze with successive groups of functions, working from
// the bottom of the call graph upward. Each time analyze is called with
// a list of functions, every function on that list only calls other functions
// on the list or functions that have been passed in previous invocations of
// analyze. Closures appear in the same list as their outer functions.
// The lists are as short as possible while preserving those requirements.
// (In a typical program, many invocations of analyze will be passed just
// a single function.) The boolean argument 'recursive' passed to analyze
// specifies whether the functions on the list are mutually recursive.
// If recursive is false, the list consists of only a single function and its closures.
// If recursive is true, the list may still contain only a single function,
// if that function is itself recursive.
func visitBottomUp(list []*Node, analyze func(list []*Node, recursive bool)) {
	var v bottomUpVisitor
	v.analyze = analyze
	v.nodeID = make(map[*Node]uint32)
	for _, n := range list {
		if n.Op == ODCLFUNC && !n.Func.IsHiddenClosure() {	// n是一个非闭包的函数声明,说明内联优化以及逃逸分析要从非闭包函数的声明开始
			v.visit(n)
		}
	}
}

func (v *bottomUpVisitor) visit(n *Node) uint32 {
	if id := v.nodeID[n]; id > 0 {	// 是之前已经处理过的非闭包函数,表示找到了一个递归链条
		// already visited
		return id
	}

	v.visitgen++
	id := v.visitgen
	v.nodeID[n] = id
	v.visitgen++
	min := v.visitgen	// min代表递归寻找的所有的函数中的最小的id
	v.stack = append(v.stack, n)	// 添加到栈中

	// 对n.Nbody这个列表中的所有抽象语法树中的每个节点作为参数执行指定的函数(传进去的第二个参数)
	inspectList(n.Nbody, func(n *Node) bool {
		switch n.Op {
		case OCALLFUNC, OCALLMETH:	// Left(List/Rlist) (function call f(args)) 28    Left(List/Rlist) (direct method call x.Method(args)) 29
			fn := asNode(n.Left.Type.Nname())	// 获取被调用的函数的函数名节点
			if fn != nil && fn.Op == ONAME && fn.Class() == PFUNC && fn.Name.Defn != nil {	// 是在全局声明的函数
				if m := v.visit(fn.Name.Defn); m < min {	// 递归处理函数声明
					min = m
				}
			}
		case OCALLPART:		// Left.Right (method expression x.Method, not called)  31
			fn := asNode(callpartMethod(n).Type.Nname())
			if fn != nil && fn.Op == ONAME && fn.Class() == PFUNC && fn.Name.Defn != nil {
				if m := v.visit(fn.Name.Defn); m < min {
					min = m
				}
			}
		case OCLOSURE:	// func Type { Body } (func literal) 34
			if m := v.visit(n.Func.Closure); m < min {	// 这里是直接处理了定义闭包函数的外部函数
				min = m
			}
		}
		return true
	})
	// min == id表示找到了一个递归链条而当前函数节点就是递归遍历的起始点
	// min == id+1表示没有找到递归链条,所有的被调用的函数都是在遍历完了所有的子节点后自然返回了,表示当前函数是一个不会递归的单独的函数
	// 还要确保不是声明在函数内部的闭包函数
	if (min == id || min == id+1) && !n.Func.IsHiddenClosure() {
		// This node is the root of a strongly connected component.

		// The original min passed to visitcodelist was v.nodeID[n]+1.
		// If visitcodelist found its way back to v.nodeID[n], then this
		// block is a set of mutually recursive functions.
		// Otherwise it's just a lone function that does not recurse.
		recursive := min == id

		// Remove connected component from stack.
		// Mark walkgen so that future visits return a large number
		// so as not to affect the caller's min.

		var i int
		for i = len(v.stack) - 1; i >= 0; i-- {		// 倒序遍历stack
			x := v.stack[i]		// 获取栈中的函数节点
			if x == n {		// 一直找到保存在栈中的与当前节点相同的节点,这样会找到一个单独的节点或者一个递归函数节点列表
				break
			}
			v.nodeID[x] = ^uint32(0)	// 将被找到的节点的id设置为最大值
		}
		v.nodeID[n] = ^uint32(0)	// 将自己的id设置为最大值
		block := v.stack[i:]	// 取出i之后的所有相互递归的节点列表或者此时可能只有自己一个函数节点
		// Run escape analysis on this set of functions.
		v.stack = v.stack[:i]
		v.analyze(block, recursive)
	}

	return min
}

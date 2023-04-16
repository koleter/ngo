// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import "cmd/internal/src"

// trim removes blocks with no code in them.
// These blocks were inserted to remove critical edges.
func trim(f *Func) {
	n := 0
	for _, b := range f.Blocks {
		if !trimmableBlock(b) {		// 不可以被删除的块
			f.Blocks[n] = b
			n++
			continue
		}
		// 到这一步,b块的后继只有一个且不是自己,前驱可能有一个或者块中没有除了phi之外的其他value
		// 将这个块从控制流图中删除
		bPos := b.Pos
		bIsStmt := bPos.IsStmt() == src.PosIsStmt	// 记录是否是语句边界

		// Splice b out of the graph. NOTE: `mergePhi` depends on the
		// order, in which the predecessors edges are merged here.
		p, i := b.Preds[0].b, b.Preds[0].i
		s, j := b.Succs[0].b, b.Succs[0].i
		ns := len(s.Preds)	// 删除b块之前后继块的前驱数量
		p.Succs[i] = Edge{s, j}	// 以下两行代码连接前驱与后继块以将当前块从控制流图中去除
		s.Preds[j] = Edge{p, i}

		for _, e := range b.Preds[1:] {		// 遍历其他的前驱块并将这些前驱块都连接到s块
			p, i := e.b, e.i
			p.Succs[i] = Edge{s, len(s.Preds)}
			s.Preds = append(s.Preds, Edge{p, i})
		}

		// Attempt to preserve a statement boundary
		if bIsStmt {	// 被删除的块是一个语句边界
			sawStmt := false
			for _, v := range s.Values {
				if isPoorStatementOp(v.Op) {
					continue
				}
				if v.Pos.SameFileAndLine(bPos) {
					v.Pos = v.Pos.WithIsStmt()
				}
				sawStmt = true
				break
			}
			if !sawStmt && s.Pos.SameFileAndLine(bPos) {	// 后继块s中没有可以作为语句边界的value且s块与b块的位置相同就将s块设置为语句边界
				s.Pos = s.Pos.WithIsStmt()
			}
		}
		// If `s` had more than one predecessor, update its phi-ops to
		// account for the merge.
		if ns > 1 {		// 删除b块之前b的后继的前驱数量大于1,说明有phi函数
			for _, v := range s.Values {	// 遍历s的values
				if v.Op == OpPhi {	// 找到其中的phi
					mergePhi(v, j, b)	// 整理v的参数
				}

			}
			// Remove the phi-ops from `b` if they were merged into the
			// phi-ops of `s`.
			k := 0
			for _, v := range b.Values {
				if v.Op == OpPhi {
					if v.Uses == 0 {
						v.resetArgs()
						continue
					}
					// Pad the arguments of the remaining phi-ops so
					// they match the new predecessor count of `s`.
					// Since s did not have a Phi op corresponding to
					// the phi op in b, the other edges coming into s
					// must be loopback edges from s, so v is the right
					// argument to v!

					// b块中有被使用的phi,将其合并到s块中
					args := make([]*Value, len(v.Args))
					copy(args, v.Args)	// 拷贝
					v.resetArgs()
					// v本身是个phi,说明phi中的参数是由前驱传入的,放到s块后,前驱数量变多,多出来的那些,也就是从s的前驱传进来的其实都可以认为是v,用v自己代替即可
					for x := 0; x < j; x++ {
						v.AddArg(v)
					}
					v.AddArg(args[0])
					for x := j + 1; x < ns; x++ {
						v.AddArg(v)
					}
					for _, a := range args[1:] {
						v.AddArg(a)
					}
				}
				b.Values[k] = v
				k++
			}
			b.Values = b.Values[:k]
		}

		// Merge the blocks' values.
		for _, v := range b.Values {
			v.Block = s
		}
		k := len(b.Values)
		m := len(s.Values)
		for i := 0; i < k; i++ {
			s.Values = append(s.Values, nil)
		}
		copy(s.Values[k:], s.Values[:m])
		copy(s.Values, b.Values)
	}
	if n < len(f.Blocks) {	// 有块被移除了,截断块切片
		f.invalidateCFG()
		tail := f.Blocks[n:]
		for i := range tail {
			tail[i] = nil
		}
		f.Blocks = f.Blocks[:n]
	}
}

// emptyBlock reports whether the block does not contain actual
// instructions
func emptyBlock(b *Block) bool {
	for _, v := range b.Values {
		if v.Op != OpPhi {
			return false
		}
	}
	return true
}

// trimmableBlock reports whether the block can be trimmed from the CFG,
// subject to the following criteria:
//  - it should not be the first block
//  - it should be BlockPlain
//  - it should not loop back to itself
//  - it either is the single predecessor of the successor block or
//    contains no actual instructions
func trimmableBlock(b *Block) bool {
	if b.Kind != BlockPlain || b == b.Func.Entry {
		return false
	}
	s := b.Succs[0].b
	return s != b && (len(s.Preds) == 1 || emptyBlock(b))
}

// mergePhi adjusts the number of `v`s arguments to account for merge
// of `b`, which was `i`th predecessor of the `v`s block.
func mergePhi(v *Value, i int, b *Block) {
	u := v.Args[i]
	if u.Block == b {	// u是从b块中传下来的参数,在b中定义
		if u.Op != OpPhi {	// b块不该只有一个前驱,否则b块会与后继块直接合并了,所以u必定是个phi,同时如果有别的value的话,那么b块不会被认为是死块
			b.Func.Fatalf("value %s is not a phi operation", u.LongString())
		}
		// If the original block contained u = φ(u0, u1, ..., un) and
		// the current phi is
		//    v = φ(v0, v1, ..., u, ..., vk)
		// then the merged phi is
		//    v = φ(v0, v1, ..., u0, ..., vk, u1, ..., un)
		v.SetArg(i, u.Args[0])
		v.AddArgs(u.Args[1:]...)
	} else {	// b的所有前驱都没有定义这个value,表示这个value至少是在最近支配b的所有前驱的某个块上定义的
		// If the original block contained u = φ(u0, u1, ..., un) and
		// the current phi is
		//    v = φ(v0, v1, ...,  vi, ..., vk)
		// i.e. it does not use a value from the predecessor block,
		// then the merged phi is
		//    v = φ(v0, v1, ..., vk, vi, vi, ...)
		for j := 1; j < len(b.Preds); j++ {
			v.AddArg(v.Args[i])
		}
	}
}

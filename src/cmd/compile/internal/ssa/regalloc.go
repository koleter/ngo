// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Register allocation.
//
// We use a version of a linear scan register allocator. We treat the
// whole function as a single long basic block and run through
// it using a greedy register allocator. Then all merge edges
// (those targeting a block with len(Preds)>1) are processed to
// shuffle data into the place that the target of the edge expects.
//
// The greedy allocator moves values into registers just before they
// are used, spills registers only when necessary, and spills the
// value whose next use is farthest in the future.
//
// The register allocator requires that a block is not scheduled until
// at least one of its predecessors have been scheduled. The most recent
// such predecessor provides the starting register state for a block.
//
// It also requires that there are no critical edges (critical =
// comes from a block with >1 successor and goes to a block with >1
// predecessor).  This makes it easy to add fixup code on merge edges -
// the source of a merge edge has only one successor, so we can add
// fixup code to the end of that block.

// Spilling
//
// During the normal course of the allocator, we might throw a still-live
// value out of all registers. When that value is subsequently used, we must
// load it from a slot on the stack. We must also issue an instruction to
// initialize that stack location with a copy of v.
//
// pre-regalloc:
//   (1) v = Op ...
//   (2) x = Op ...
//   (3) ... = Op v ...
//
// post-regalloc:
//   (1) v = Op ...    : AX // computes v, store result in AX
//       s = StoreReg v     // spill v to a stack slot
//   (2) x = Op ...    : AX // some other op uses AX
//       c = LoadReg s : CX // restore v from stack slot
//   (3) ... = Op c ...     // use the restored value
//
// Allocation occurs normally until we reach (3) and we realize we have
// a use of v and it isn't in any register. At that point, we allocate
// a spill (a StoreReg) for v. We can't determine the correct place for
// the spill at this point, so we allocate the spill as blockless initially.
// The restore is then generated to load v back into a register so it can
// be used. Subsequent uses of v will use the restored value c instead.
//
// What remains is the question of where to schedule the spill.
// During allocation, we keep track of the dominator of all restores of v.
// The spill of v must dominate that block. The spill must also be issued at
// a point where v is still in a register.
//
// To find the right place, start at b, the block which dominates all restores.
//  - If b is v.Block, then issue the spill right after v.
//    It is known to be in a register at that point, and dominates any restores.
//  - Otherwise, if v is in a register at the start of b,
//    put the spill of v at the start of b.
//  - Otherwise, set b = immediate dominator of b, and repeat.
//
// Phi values are special, as always. We define two kinds of phis, those
// where the merge happens in a register (a "register" phi) and those where
// the merge happens in a stack location (a "stack" phi).
//
// A register phi must have the phi and all of its inputs allocated to the
// same register. Register phis are spilled similarly to regular ops.
//
// A stack phi must have the phi and all of its inputs allocated to the same
// stack location. Stack phis start out life already spilled - each phi
// input must be a store (using StoreReg) at the end of the corresponding
// predecessor block.
//     b1: y = ... : AX        b2: z = ... : BX
//         y2 = StoreReg y         z2 = StoreReg z
//         goto b3                 goto b3
//     b3: x = phi(y2, z2)
// The stack allocator knows that StoreReg args of stack-allocated phis
// must be allocated to the same stack slot as the phi that uses them.
// x is now a spilled value and a restore must appear before its first use.

// TODO

// Use an affinity graph to mark two values which should use the
// same register. This affinity graph will be used to prefer certain
// registers for allocation. This affinity helps eliminate moves that
// are required for phi implementations and helps generate allocations
// for 2-register architectures.

// Note: regalloc generates a not-quite-SSA output. If we have:
//
//             b1: x = ... : AX
//                 x2 = StoreReg x
//                 ... AX gets reused for something else ...
//                 if ... goto b3 else b4
//
//   b3: x3 = LoadReg x2 : BX       b4: x4 = LoadReg x2 : CX
//       ... use x3 ...                 ... use x4 ...
//
//             b2: ... use x3 ...
//
// If b3 is the primary predecessor of b2, then we use x3 in b2 and
// add a x4:CX->BX copy at the end of b4.
// But the definition of x3 doesn't dominate b2.  We should really
// insert a dummy phi at the start of b2 (x5=phi(x3,x4):BX) to keep
// SSA form. For now, we ignore this problem as remaining in strict
// SSA form isn't needed after regalloc. We'll just leave the use
// of x3 not dominated by the definition of x3, and the CX->BX copy
// will have no use (so don't run deadcode after regalloc!).
// TODO: maybe we should introduce these extra phis?

package ssa

import (
	"cmd/compile/internal/types"
	"cmd/internal/objabi"
	"cmd/internal/src"
	"cmd/internal/sys"
	"fmt"
	"math/bits"
	"unsafe"
)

const (
	moveSpills = iota
	logSpills
	regDebug
	stackDebug
)

// distance is a measure of how far into the future values are used.
// distance is measured in units of instructions.
const (
	likelyDistance   = 1
	normalDistance   = 10
	unlikelyDistance = 100
)

// regalloc performs register allocation on f. It sets f.RegAlloc
// to the resulting allocation.
func regalloc(f *Func) {
	var s regAllocState
	s.init(f)
	s.regalloc(f)
}

type register uint8

const noRegister register = 255

// A regMask encodes a set of machine registers.
// TODO: regMask -> regSet?
type regMask uint64

func (m regMask) String() string {
	s := ""
	for r := register(0); m != 0; r++ {
		if m>>r&1 == 0 {
			continue
		}
		m &^= regMask(1) << r
		if s != "" {
			s += " "
		}
		s += fmt.Sprintf("r%d", r)
	}
	return s
}

func (s *regAllocState) RegMaskString(m regMask) string {
	str := ""
	for r := register(0); m != 0; r++ {
		if m>>r&1 == 0 {
			continue
		}
		m &^= regMask(1) << r
		if str != "" {
			str += " "
		}
		str += s.registers[r].String()
	}
	return str
}

// countRegs returns the number of set bits in the register mask.
func countRegs(r regMask) int {
	return bits.OnesCount64(uint64(r))
}

// pickReg picks an arbitrary register from the register mask.
func pickReg(r regMask) register {
	if r == 0 {
		panic("can't pick a register from an empty set")
	}
	// pick the lowest one
	return register(bits.TrailingZeros64(uint64(r)))
}

type use struct {
	dist int32    // distance from start of the block to a use of a value
	pos  src.XPos // source position of the use
	next *use     // linked list of uses of a value in nondecreasing dist order
}

// A valState records the register allocation state for a (pre-regalloc) value.
type valState struct {
	regs              regMask // the set of registers holding a Value (usually just one)	记录当前的value保存在哪个寄存器中了
	uses              *use    // list of uses in this block		一个链表,如果不为nil,表示这个value在当前块中还有要被使用到的地方
	spill             *Value  // spilled copy of the Value (if any)		s.f.newValueNoBlock(OpStoreReg, v.Type, v.Pos),一个通过这种方式创建的value
	restoreMin        int32   // minimum of all restores' blocks' sdom.entry
	restoreMax        int32   // maximum of all restores' blocks' sdom.exit
	needReg           bool    // cached value of !v.Type.IsMemory() && !v.Type.IsVoid() && !.v.Type.IsFlags()
	rematerializeable bool    // cached value of v.rematerializeable()  and !v.Type.IsMemory() && !v.Type.IsVoid() && !.v.Type.IsFlags()
}

type regState struct {
	v *Value // Original (preregalloc) Value stored in this register.
	c *Value // A Value equal to v which is currently in a register.  Might be v or a copy of it.
	// If a register is unused, v==c==nil
}

type regAllocState struct {
	f *Func // 当前处理的函数

	sdom        SparseTree
	registers   []Register
	numRegs     register // len(registers)
	SPReg       register // SP
	SBReg       register // SB
	GReg        register // g
	allocatable regMask  // 可以使用的所有寄存器掩码,一般应该是除SP,SB,fp(rbp),g寄存器以外的所有通用寄存器及R8到R15，还有xmm0到xmm15

	// for each block, its primary predecessor.
	// A predecessor of b is primary if it is the closest
	// predecessor that appears before b in the layout order.
	// We record the index in the Preds list where the primary predecessor sits.
	primary []int32	// 块ID对应某个最近前驱的索引

	// live values at the end of each block.  live[b.ID] is a list of value IDs
	// which are live at the end of b, together with a count of how many instructions
	// forward to the next use.
	live [][]liveInfo
	// desired register assignments at the end of each block.
	// Note that this is a static map computed before allocation occurs. Dynamic
	// register desires (from partially completed allocations) will trump
	// this information.
	desired []desiredState

	// current state of each (preregalloc) Value
	values []valState // value ID -> valState

	// ID of SP, SB values
	sp, sb ID

	// For each Value, map from its value ID back to the
	// preregalloc Value it was derived from.
	orig []*Value // value ID -> value

	// current state of each register
	regs []regState // 如果regs[r] != nil,表示寄存器r在使用中

	// registers that contain values which can't be kicked out
	nospill regMask

	// mask of registers currently in use
	used regMask	// 已经使用的寄存器

	// mask of registers used in the current instruction
	tmpused regMask

	// current block we're working on
	curBlock *Block

	// cache of use records
	freeUseRecords *use		// 一个use链表

	// endRegs[blockid] is the register state at the end of each block.
	// encoded as a set of endReg records.
	endRegs [][]endReg	// 每个块结束时的所有已使用的寄存器状态

	// startRegs[blockid] is the register state at the start of merge blocks.
	// saved state does not include the state of phi ops in the block.
	startRegs [][]startReg		// 块ID对应该块起始寄存器状态(除去分配给phi的寄存器)

	// spillLive[blockid] is the set of live spills at the end of each block
	spillLive [][]ID	// 在后继块中会使用且不能重新实现的value会为其创建一个spill并添加到对应块ID的切片中

	// a set of copies we generated to move things around, and
	// whether it is used in shuffle. Unused copies will be deleted.
	copies map[*Value]bool	// 为true表示使用了,前驱创建,用于

	loopnest *loopnest

	// choose a good order in which to visit blocks for allocation purposes.
	visitOrder []*Block // layout pass排序之后的块顺序
}

type endReg struct {
	r register
	v *Value // pre-regalloc value held in this register (TODO: can we use ID here?)
	c *Value // cached version of the value
}

type startReg struct {
	r   register
	v   *Value   // pre-regalloc value needed in this register
	c   *Value   // cached version of the value
	pos src.XPos // source position of use of this register
}

// freeReg frees up register r. Any current user of r is kicked out.
func (s *regAllocState) freeReg(r register) {
	v := s.regs[r].v	// 获取保存在这个寄存器中的原始value
	if v == nil {
		s.f.Fatalf("tried to free an already free register %d\n", r)
	}

	// Mark r as unused.
	if s.f.pass.debug > regDebug {
		fmt.Printf("freeReg %s (dump %s/%s)\n", &s.registers[r], v, s.regs[r].c)
	}
	s.regs[r] = regState{}	// 表示寄存器不再处于被分配状态
	s.values[v.ID].regs &^= regMask(1) << r		// 解除value与寄存器的绑定
	s.used &^= regMask(1) << r	// 当前所有已被使用的寄存器中排除r
}

// freeRegs frees up all registers listed in m.
func (s *regAllocState) freeRegs(m regMask) {
	for m&s.used != 0 {
		s.freeReg(pickReg(m & s.used))
	}
}

// setOrig records that c's original value is the same as
// v's original value.
func (s *regAllocState) setOrig(c *Value, v *Value) {
	for int(c.ID) >= len(s.orig) {
		s.orig = append(s.orig, nil)
	}
	if s.orig[c.ID] != nil {
		s.f.Fatalf("orig value set twice %s %s", c, v)
	}
	s.orig[c.ID] = s.orig[v.ID]
}

// assignReg assigns register r to hold c, a copy of v.
// r must be unused.
func (s *regAllocState) assignReg(r register, v *Value, c *Value) {
	if s.f.pass.debug > regDebug {
		fmt.Printf("assignReg %s %s/%s\n", &s.registers[r], v, c)
	}
	if s.regs[r].v != nil {		// 确保寄存器r没有被使用
		s.f.Fatalf("tried to assign register %d to %s/%s but it is already used by %s", r, v, c, s.regs[r].v)
	}

	// Update state.
	s.regs[r] = regState{v, c}
	s.values[v.ID].regs |= regMask(1) << r	// 标记v使用了寄存器r
	s.used |= regMask(1) << r	// 所有使用的寄存器中记录r
	s.f.setHome(c, &s.registers[r])		// f.RegAlloc[c.ID] = &s.registers[r]
}

// allocReg chooses a register from the set of registers in mask.
// If there is no unused register, a Value will be kicked out of
// a register to make room.
func (s *regAllocState) allocReg(mask regMask, v *Value) register {	//
	if v.OnWasmStack {
		return noRegister
	}

	mask &= s.allocatable	// mask中保留可以分配的寄存器列表
	mask &^= s.nospill	// mask中不能分配不能spill的寄存器
	if mask == 0 {
		s.f.Fatalf("no register available for %s", v.LongString())
	}

	// Pick an unused register if one is available.
	if mask&^s.used != 0 {	// 存在可以分配的寄存器
		return pickReg(mask &^ s.used)	// 从这些可分配的寄存器中返回一个
	}

	// Pick a value to spill. Spill the value with the
	// farthest-in-the-future use.
	// TODO: Prefer registers with already spilled Values?
	// TODO: Modify preference using affinity graph.
	// TODO: if a single value is in multiple registers, spill one of them
	// before spilling a value in just a single register.

	// Find a register to spill. We spill the register containing the value
	// whose next use is as far in the future as possible.
	// https://en.wikipedia.org/wiki/Page_replacement_algorithm#The_theoretically_optimal_page_replacement_algorithm
	var r register	// 待spill的寄存器
	maxuse := int32(-1)		// 记录所有可以spill的寄存器中最远使用的
	for t := register(0); t < s.numRegs; t++ {	// 遍历所有的寄存器
		if mask>>t&1 == 0 {	// 找到一个可使用的寄存器
			continue
		}
		v := s.regs[t].v	// 获取寄存器当前保存的value
		if n := s.values[v.ID].uses.dist; n > maxuse {
			// v's next use is farther in the future than any value
			// we've seen so far. A new best spill candidate.
			r = t
			maxuse = n
		}
	}
	if maxuse == -1 {	// 没有找到可用寄存器
		s.f.Fatalf("couldn't find register to spill")
	}

	if s.f.Config.ctxt.Arch.Arch == sys.ArchWasm {
		// TODO(neelance): In theory this should never happen, because all wasm registers are equal.
		// So if there is still a free register, the allocation should have picked that one in the first place instead of
		// trying to kick some other value out. In practice, this case does happen and it breaks the stack optimization.
		s.freeReg(r)
		return r
	}

	// Try to move it around before kicking out, if there is a free register.
	// We generate a Copy and record it. It will be deleted if never used.
	v2 := s.regs[r].v	// 获取寄存器r中保存的value
	m := s.compatRegs(v2.Type) &^ s.used &^ s.tmpused &^ (regMask(1) << r)	// 尝试找到一个可以容纳v的类型的可用寄存器
	if m != 0 && !s.values[v2.ID].rematerializeable && countRegs(s.values[v2.ID].regs) == 1 {	// 存在其他可以容纳v2的类型的寄存器
		r2 := pickReg(m)	// 获取寄存器
		c := s.curBlock.NewValue1(v2.Pos, OpCopy, v2.Type, s.regs[r].c)		// 创建一个对目标value的拷贝
		s.copies[c] = false		// 记录到s.copies中
		if s.f.pass.debug > regDebug {
			fmt.Printf("copy %s to %s : %s\n", v2, c, &s.registers[r2])
		}
		s.setOrig(c, v2)
		s.assignReg(r2, v2, c)
	}
	s.freeReg(r)	// 释放寄存器r
	return r
}

// makeSpill returns a Value which represents the spilled value of v.
// b is the block in which the spill is used.
func (s *regAllocState) makeSpill(v *Value, b *Block) *Value {
	vi := &s.values[v.ID]
	if vi.spill != nil {	// 之前已经spill过了
		// Final block not known - keep track of subtree where restores reside.
		vi.restoreMin = min32(vi.restoreMin, s.sdom[b.ID].entry)
		vi.restoreMax = max32(vi.restoreMax, s.sdom[b.ID].exit)
		return vi.spill
	}
	// Make a spill for v. We don't know where we want
	// to put it yet, so we leave it blockless for now.
	spill := s.f.newValueNoBlock(OpStoreReg, v.Type, v.Pos)		// 创建一个不属于任何块的value
	// We also don't know what the spill's arg will be.
	// Leave it argless for now.
	s.setOrig(spill, v)
	vi.spill = spill
	vi.restoreMin = s.sdom[b.ID].entry
	vi.restoreMax = s.sdom[b.ID].exit
	return spill
}

// allocValToReg allocates v to a register selected from regMask and
// returns the register copy of v. Any previous user is kicked out and spilled
// (if necessary). Load code is added at the current pc. If nospill is set the
// allocated register is marked nospill so the assignment cannot be
// undone until the caller allows it by clearing nospill. Returns a
// *Value which is either v or a copy of v allocated to the chosen register.
func (s *regAllocState) allocValToReg(v *Value, mask regMask, nospill bool, pos src.XPos) *Value {
	if s.f.Config.ctxt.Arch.Arch == sys.ArchWasm && v.rematerializeable() {
		c := v.copyIntoWithXPos(s.curBlock, pos)
		c.OnWasmStack = true
		s.setOrig(c, v)
		return c
	}
	if v.OnWasmStack {
		return v
	}

	vi := &s.values[v.ID]
	pos = pos.WithNotStmt()
	// Check if v is already in a requested register.
	if mask&vi.regs != 0 {	// vi已经在一个想要被分配的寄存器列表中了
		r := pickReg(mask & vi.regs)	// 获取一个寄存器
		if s.regs[r].v != v || s.regs[r].c == nil {
			panic("bad register state")
		}
		if nospill {	// r寄存器不能被spill
			s.nospill |= regMask(1) << r	// 标记r寄存器不能被spill
		}
		return s.regs[r].c	// 返回当前在寄存器r中的value
	}

	var r register	// 分配给v的寄存器
	// If nospill is set, the value is used immediately, so it can live on the WebAssembly stack.
	onWasmStack := nospill && s.f.Config.ctxt.Arch.Arch == sys.ArchWasm
	if !onWasmStack {
		// Allocate a register.
		r = s.allocReg(mask, v)		// 从可分配的寄存器列表中找到一个分配给v的寄存器或者spill一个寄存器给v使用
	}

	// Allocate v to the new register.
	var c *Value	// 分配到寄存器中的新value
	if vi.regs != 0 {	// value当前有分配给它的寄存器
		// Copy from a register that v is already in.
		r2 := pickReg(vi.regs)	// 从v已经在的寄存器中获取一个寄存器
		if s.regs[r2].v != v {
			panic("bad register state")
		}
		c = s.curBlock.NewValue1(pos, OpCopy, v.Type, s.regs[r2].c)		// 拷贝现在的value
	} else if v.rematerializeable() {	// v可重新实现
		// Rematerialize instead of loading from the spill location.
		c = v.copyIntoWithXPos(s.curBlock, pos)		// 重新创建一个相同的value
	} else {
		// Load v from its spill location.
		spill := s.makeSpill(v, s.curBlock)
		if s.f.pass.debug > logSpills {
			s.f.Warnl(vi.spill.Pos, "load spill for %v from %v", v, spill)
		}
		c = s.curBlock.NewValue1(pos, OpLoadReg, v.Type, spill)		// OpLoadReg加载之前OpStoreReg存储的值
	}

	s.setOrig(c, v)

	if onWasmStack {
		c.OnWasmStack = true
		return c
	}

	s.assignReg(r, v, c)
	if c.Op == OpLoadReg && s.isGReg(r) {
		s.f.Fatalf("allocValToReg.OpLoadReg targeting g: " + c.LongString())
	}
	if nospill {
		s.nospill |= regMask(1) << r
	}
	return c
}

// isLeaf reports whether f performs any calls.
func isLeaf(f *Func) bool {
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if opcodeTable[v.Op].call {
				return false
			}
		}
	}
	return true
}

func (s *regAllocState) init(f *Func) {
	s.f = f
	s.f.RegAlloc = s.f.Cache.locs[:0]
	s.registers = f.Config.registers
	if nr := len(s.registers); nr == 0 || nr > int(noRegister) || nr > int(unsafe.Sizeof(regMask(0))*8) {
		s.f.Fatalf("bad number of registers: %d", nr)
	} else {
		s.numRegs = register(nr)
	}
	// Locate SP, SB, and g registers.
	s.SPReg = noRegister
	s.SBReg = noRegister
	s.GReg = noRegister
	for r := register(0); r < s.numRegs; r++ {
		switch s.registers[r].String() {
		case "SP":
			s.SPReg = r
		case "SB":
			s.SBReg = r
		case "g":
			s.GReg = r
		}
	}
	// Make sure we found all required registers.
	switch noRegister {
	case s.SPReg:
		s.f.Fatalf("no SP register found")
	case s.SBReg:
		s.f.Fatalf("no SB register found")
	case s.GReg:
		if f.Config.hasGReg {
			s.f.Fatalf("no g register found")
		}
	}

	// Figure out which registers we're allowed to use.
	s.allocatable = s.f.Config.gpRegMask | s.f.Config.fpRegMask | s.f.Config.specialRegMask
	s.allocatable &^= 1 << s.SPReg
	s.allocatable &^= 1 << s.SBReg
	if s.f.Config.hasGReg {
		s.allocatable &^= 1 << s.GReg
	}
	if s.f.Config.ctxt.Framepointer_enabled && s.f.Config.FPReg >= 0 {
		s.allocatable &^= 1 << uint(s.f.Config.FPReg)
	}
	if s.f.Config.LinkReg != -1 {
		if isLeaf(f) { // 函数f中没有函数调用
			// Leaf functions don't save/restore the link register.
			s.allocatable &^= 1 << uint(s.f.Config.LinkReg)
		}
		if s.f.Config.arch == "arm" && objabi.GOARM == 5 {
			// On ARMv5 we insert softfloat calls at each FP instruction.
			// This clobbers LR almost everywhere. Disable allocating LR
			// on ARMv5.
			s.allocatable &^= 1 << uint(s.f.Config.LinkReg)
		}
	}
	if s.f.Config.ctxt.Flag_dynlink {
		switch s.f.Config.arch {
		case "amd64":
			s.allocatable &^= 1 << 15 // R15
		case "arm":
			s.allocatable &^= 1 << 9 // R9
		case "ppc64le": // R2 already reserved.
			// nothing to do
		case "arm64":
			// nothing to do?
		case "386":
			// nothing to do.
			// Note that for Flag_shared (position independent code)
			// we do need to be careful, but that carefulness is hidden
			// in the rewrite rules so we always have a free register
			// available for global load/stores. See gen/386.rules (search for Flag_shared).
		case "s390x":
			s.allocatable &^= 1 << 11 // R11
		default:
			s.f.fe.Fatalf(src.NoXPos, "arch %s not implemented", s.f.Config.arch)
		}
	}
	if s.f.Config.use387 {
		s.allocatable &^= 1 << 15 // X7 disallowed (one 387 register is used as scratch space during SSE->387 generation in ../x86/387.go)
	}

	// Linear scan register allocation can be influenced by the order in which blocks appear.
	// Decouple the register allocation order from the generated block order.
	// This also creates an opportunity for experiments to find a better order.
	s.visitOrder = layoutRegallocOrder(f)

	// Compute block order. This array allows us to distinguish forward edges
	// from backward edges and compute how far they go.
	blockOrder := make([]int32, f.NumBlocks()) // 块ID对应该块在s.visitOrder中的索引
	for i, b := range s.visitOrder {
		blockOrder[b.ID] = int32(i) // 块ID指向该块在visitOrder中的索引
	}

	s.regs = make([]regState, s.numRegs)	// 记录所有寄存器的使用情况
	nv := f.NumValues()                      // 函数中的values总数
	if cap(s.f.Cache.regallocValues) >= nv { // s.f.Cache.regallocValues = make([]valState, nv)
		s.f.Cache.regallocValues = s.f.Cache.regallocValues[:nv]
	} else {
		s.f.Cache.regallocValues = make([]valState, nv)
	}
	s.values = s.f.Cache.regallocValues
	s.orig = make([]*Value, nv)
	s.copies = make(map[*Value]bool)
	for _, b := range s.visitOrder { // 遍历排序好的所有块
		for _, v := range b.Values { // 遍历块中所有values
			if !v.Type.IsMemory() && !v.Type.IsVoid() && !v.Type.IsFlags() && !v.Type.IsTuple() {
				s.values[v.ID].needReg = true
				s.values[v.ID].rematerializeable = v.rematerializeable()
				s.orig[v.ID] = v	// 设置value ID对应的最原始value
			}
			// Note: needReg is false for values returning Tuple types.
			// Instead, we mark the corresponding Selects as needReg.
		}
	}
	s.computeLive()

	// Compute primary predecessors.
	s.primary = make([]int32, f.NumBlocks())
	for _, b := range s.visitOrder { // 遍历排序后的所有块
		best := -1 // 记录前驱中离当前块最近的块的前驱索引
		for i, e := range b.Preds {
			p := e.b
			if blockOrder[p.ID] >= blockOrder[b.ID] {	// 前驱块在s.visitOrder中的索引大于等于当前块,这是一个向前跳转的块
				continue // backward edge
			}
			// 到这里表示前驱块在s.visitOrder中的索引小于当前块
			if best == -1 || blockOrder[p.ID] > blockOrder[b.Preds[best].b.ID] {	// 找到所有前驱块在s.visitOrder中的索引小于当前块中索引最大的那个,这也表示距离当前块最近
				best = i
			}
		}
		s.primary[b.ID] = int32(best)
	}

	s.endRegs = make([][]endReg, f.NumBlocks())
	s.startRegs = make([][]startReg, f.NumBlocks())
	s.spillLive = make([][]ID, f.NumBlocks())
	s.sdom = f.Sdom()

	// wasm: Mark instructions that can be optimized to have their values only on the WebAssembly stack.
	if f.Config.ctxt.Arch.Arch == sys.ArchWasm {
		canLiveOnStack := f.newSparseSet(f.NumValues())
		defer f.retSparseSet(canLiveOnStack)
		for _, b := range f.Blocks {
			// New block. Clear candidate set.
			canLiveOnStack.clear()
			for _, c := range b.ControlValues() {
				if c.Uses == 1 && !opcodeTable[c.Op].generic {
					canLiveOnStack.add(c.ID)
				}
			}
			// Walking backwards.
			for i := len(b.Values) - 1; i >= 0; i-- {
				v := b.Values[i]
				if canLiveOnStack.contains(v.ID) {
					v.OnWasmStack = true
				} else {
					// Value can not live on stack. Values are not allowed to be reordered, so clear candidate set.
					canLiveOnStack.clear()
				}
				for _, arg := range v.Args {
					// Value can live on the stack if:
					// - it is only used once
					// - it is used in the same basic block
					// - it is not a "mem" value
					// - it is a WebAssembly op
					if arg.Uses == 1 && arg.Block == v.Block && !arg.Type.IsMemory() && !opcodeTable[arg.Op].generic {
						canLiveOnStack.add(arg.ID)
					}
				}
			}
		}
	}
}

// Adds a use record for id at distance dist from the start of the block.
// All calls to addUse must happen with nonincreasing dist.
func (s *regAllocState) addUse(id ID, dist int32, pos src.XPos) {	// 创建一个use并头插到s.values[id].uses中
	r := s.freeUseRecords
	if r != nil {
		s.freeUseRecords = r.next
	} else {
		r = &use{}
	}
	r.dist = dist
	r.pos = pos
	r.next = s.values[id].uses	// 头插到s.values[id].uses中
	s.values[id].uses = r
	if r.next != nil && dist > r.next.dist {
		s.f.Fatalf("uses added in wrong order")
	}
}

// advanceUses advances the uses of v's args from the state before v to the state after v.
// Any values which have no more uses are deallocated from registers.
func (s *regAllocState) advanceUses(v *Value) {
	for _, a := range v.Args {	// 遍历v的所有参数,将参数的use从链表头释放一个
		if !s.values[a.ID].needReg {	// 参数不需要寄存器就处理下一个参数
			continue
		}
		ai := &s.values[a.ID]	// 获取参数的寄存器状态
		r := ai.uses	// 从uses的头部获取一个节点
		ai.uses = r.next	// 指向链表的下一个节点
		if r.next == nil {
			// Value is dead, free all registers that hold it.
			s.freeRegs(ai.regs) // 释放掉a所占用的寄存器
		}
		r.next = s.freeUseRecords
		s.freeUseRecords = r
	}
}

// liveAfterCurrentInstruction reports whether v is live after
// the current instruction is completed.  v must be used by the
// current instruction.
func (s *regAllocState) liveAfterCurrentInstruction(v *Value) bool {	// 判断在本次之后这个v是否还有被使用的机会
	u := s.values[v.ID].uses
	d := u.dist
	for u != nil && u.dist == d {
		u = u.next
	}
	return u != nil && u.dist > d
}

// Sets the state of the registers to that encoded in regs.
func (s *regAllocState) setState(regs []endReg) {
	s.freeRegs(s.used)	// 释放所有的寄存器
	for _, x := range regs {
		s.assignReg(x.r, x.v, x.c)
	}
}

// compatRegs returns the set of registers which can store a type t.
func (s *regAllocState) compatRegs(t *types.Type) regMask {
	var m regMask
	if t.IsTuple() || t.IsFlags() {
		return 0
	}
	if t.IsFloat() || t == types.TypeInt128 {
		if t.Etype == types.TFLOAT32 && s.f.Config.fp32RegMask != 0 {
			m = s.f.Config.fp32RegMask
		} else if t.Etype == types.TFLOAT64 && s.f.Config.fp64RegMask != 0 {
			m = s.f.Config.fp64RegMask
		} else {
			m = s.f.Config.fpRegMask
		}
	} else {
		m = s.f.Config.gpRegMask
	}
	return m & s.allocatable
}

// regspec returns the regInfo for operation op.
func (s *regAllocState) regspec(op Op) regInfo {
	if op == OpConvert {
		// OpConvert is a generic op, so it doesn't have a
		// register set in the static table. It can use any
		// allocatable integer register.
		m := s.allocatable & s.f.Config.gpRegMask
		return regInfo{inputs: []inputInfo{{regs: m}}, outputs: []outputInfo{{regs: m}}}
	}
	return opcodeTable[op].reg
}

func (s *regAllocState) isGReg(r register) bool {
	return s.f.Config.hasGReg && s.GReg == r
}

func (s *regAllocState) regalloc(f *Func) {
	regValLiveSet := f.newSparseSet(f.NumValues()) // set of values that may be live in register
	defer f.retSparseSet(regValLiveSet)
	var oldSched []*Value
	var phis []*Value	// 保存当前块中的phi values
	var phiRegs []register	// 当前的块中的phi用什么寄存器存储
	var args []*Value	// 保存当前处理的value的args

	// Data structure used for computing desired registers.
	var desired desiredState

	// Desired registers for inputs & outputs for each instruction in the block.
	type dentry struct {
		out [4]register    // desired output registers
		in  [3][4]register // desired input registers (for inputs 0,1, and 2)
	}
	var dinfo []dentry	// oldSched中的索引对应这个value的输入输出寄存器信息

	if f.Entry != f.Blocks[0] {
		f.Fatalf("entry block must be first")
	}

	for _, b := range s.visitOrder { // 遍历排序后的所有块
		if s.f.pass.debug > regDebug {
			fmt.Printf("Begin processing block %v\n", b)
		}
		s.curBlock = b

		// Initialize regValLiveSet and uses fields for this block.
		// Walk backwards through the block doing liveness analysis.
		regValLiveSet.clear()
		for _, e := range s.live[b.ID] {	// 为当前块末尾的live values创建一个use并记录valueId到regValLiveSet中
			s.addUse(e.ID, int32(len(b.Values))+e.dist, e.pos) // pseudo-uses from beyond end of block
			regValLiveSet.add(e.ID)		// 记录e.ID可能会占用一个寄存器
		}
		for _, v := range b.ControlValues() {
			if s.values[v.ID].needReg {		// 控制语句需要寄存器的话视为live value
				s.addUse(v.ID, int32(len(b.Values)), b.Pos) // pseudo-use by control values
				regValLiveSet.add(v.ID)
			}
		}
		for i := len(b.Values) - 1; i >= 0; i-- {	// 倒序遍历当前块中的values,这个循环相当于找到进入b块时的活跃values,这些values的ID保存到regValLiveSet中
			v := b.Values[i]
			regValLiveSet.remove(v.ID)	// 当前为倒序遍历,在这个value前面这个value不会出现,所以从live values中移除
			if v.Op == OpPhi {
				// Remove v from the live set, but don't add
				// any inputs. This is the state the len(b.Preds)>1
				// case below desires; it wants to process phis specially.
				continue
			}
			if opcodeTable[v.Op].call {	// 当前是一个函数调用
				// Function call clobbers all the registers but SP and SB.
				regValLiveSet.clear()	// 函数调用前将所有寄存器中的值保存到栈上
				if s.sp != 0 && s.values[s.sp].uses != nil {
					regValLiveSet.add(s.sp)
				}
				if s.sb != 0 && s.values[s.sb].uses != nil {
					regValLiveSet.add(s.sb)
				}
			}
			for _, a := range v.Args {	// 遍历v的参数
				if !s.values[a.ID].needReg {
					continue
				}
				s.addUse(a.ID, int32(i), v.Pos)		// 记录参数被使用
				regValLiveSet.add(a.ID)
			}
		}
		if s.f.pass.debug > regDebug {
			fmt.Printf("use distances for %s\n", b)
			for i := range s.values {
				vi := &s.values[i]
				u := vi.uses
				if u == nil {
					continue
				}
				fmt.Printf("  v%d:", i)
				for u != nil {
					fmt.Printf(" %d", u.dist)
					u = u.next
				}
				fmt.Println()
			}
		}

		// Make a copy of the block schedule so we can generate a new one in place.
		// We make a separate copy for phis and regular values.
		nphi := 0	// 记录当前块中phi的数量
		for _, v := range b.Values {
			if v.Op != OpPhi {
				break
			}
			nphi++
		}
		phis = append(phis[:0], b.Values[:nphi]...)		// 将当前块中的phi values添加到phis中
		oldSched = append(oldSched[:0], b.Values[nphi:]...)		// 除了phi values,其他的values保存为oldSched
		b.Values = b.Values[:0]		// 暂时将当前块中的values列表清空

		// Initialize start state of block.
		if b == f.Entry {
			// Regalloc state is empty to start.
			if nphi > 0 {
				f.Fatalf("phis in entry block")
			}
		} else if len(b.Preds) == 1 {	// 当前块的前驱只有一个
			// Start regalloc state with the end state of the previous block.
			s.setState(s.endRegs[b.Preds[0].b.ID])	// 将当前的寄存器状态设置为前驱块结尾的寄存器状态
			if nphi > 0 {	// 只有一个前驱的话不应该有phi
				f.Fatalf("phis in single-predecessor block")
			}
			// Drop any values which are no longer live.
			// This may happen because at the end of p, a value may be
			// live but only used by some other successor of p.
			for r := register(0); r < s.numRegs; r++ {
				v := s.regs[r].v	// 获取寄存器中存储的原始value
				if v != nil && !regValLiveSet.contains(v.ID) {	// r中存储了v的值,但是v在当前的块起始处并不活跃,这表示r这个寄存器可以释放以供其他value使用
					s.freeReg(r)	// 释放r寄存器
				}
			}
		} else {	// 存在多个前驱
			// This is the complicated case. We have more than one predecessor,
			// which means we may have Phi ops.

			// Start with the final register state of the primary predecessor
			idx := s.primary[b.ID]	// 获取b块的主要前驱的索引
			if idx < 0 {
				f.Fatalf("block with no primary predecessor %s", b)
			}
			p := b.Preds[idx].b		// 获取主要前驱块
			s.setState(s.endRegs[p.ID])		// 将当前的寄存器状态设置为主要前驱块结尾的寄存器状态

			if s.f.pass.debug > regDebug {
				fmt.Printf("starting merge block %s with end state of %s:\n", b, p)
				for _, x := range s.endRegs[p.ID] {
					fmt.Printf("  %s: orig:%s cache:%s\n", &s.registers[x.r], x.v, x.c)
				}
			}

			// Decide on registers for phi ops. Use the registers determined
			// by the primary predecessor if we can.
			// TODO: pick best of (already processed) predecessors?
			// Majority vote? Deepest nesting level?
			phiRegs = phiRegs[:0]	// 当前块的第i个phi对应存储这个phi的寄存器
			var phiUsed regMask

			for _, v := range phis {	// 遍历当前块中的phi values,为phi分配寄存器保存到phiRegs中
				if !s.values[v.ID].needReg {
					phiRegs = append(phiRegs, noRegister)
					continue
				}
				a := v.Args[idx]	// 获取主要前驱的索引传递的参数
				// Some instructions target not-allocatable registers.
				// They're not suitable for further (phi-function) allocation.
				m := s.values[a.ID].regs &^ phiUsed & s.allocatable		// 找到可以分配给参数的寄存器列表且该列表与当前块中的已经分配给phi的列表不冲突
				if m != 0 {		// 参数a中有分配的寄存器且该寄存器不与当前分配给phi的寄存器冲突
					r := pickReg(m)	// 从可分配寄存器列表中获取一个寄存器
					phiUsed |= regMask(1) << r	// 记录到phi使用的寄存器列表中
					phiRegs = append(phiRegs, r)	// 添加这个参数的寄存器到phiRegs中,这表示可以直接用参数的寄存器作为这个phi的寄存器
				} else {
					phiRegs = append(phiRegs, noRegister)	// 参数使用的寄存器可能由于已经被本块中的其他phi占用了导致无寄存器可以分配
				}
			}

			// Second pass - deallocate all in-register phi inputs.
			for i, v := range phis {	// 遍历所有的phi
				if !s.values[v.ID].needReg {
					continue
				}
				a := v.Args[idx]	// 获取主要前驱的索引传递的参数
				r := phiRegs[i]		// 获取为这个phi分配的寄存器,这个寄存器可能是主要参数的寄存器
				if r == noRegister {	// 不是从参数直接使用的寄存器
					continue
				}
				if regValLiveSet.contains(a.ID) {	// a的结果保存在r中,a依旧活跃,表示除了phi,还有其他的value使用了a作为参数
					// Input value is still live (it is used by something other than Phi).
					// Try to move it around before kicking out, if there is a free register.
					// We generate a Copy in the predecessor block and record it. It will be
					// deleted later if never used.
					//
					// Pick a free register. At this point some registers used in the predecessor
					// block may have been deallocated. Those are the ones used for Phis. Exclude
					// them (and they are not going to be helpful anyway).
					m := s.compatRegs(a.Type) &^ s.used &^ phiUsed	// 找到一个可以保存主要参数的类型的寄存器
					// 存在可以保存主要参数的可用寄存器且主要参数不能重新实现且主要参数当前只占用了一个寄存器
					if m != 0 && !s.values[a.ID].rematerializeable && countRegs(s.values[a.ID].regs) == 1 {
						r2 := pickReg(m)	// 获取一个可用寄存器
						c := p.NewValue1(a.Pos, OpCopy, a.Type, s.regs[r].c)	// 在前驱块中创建一个副本,对r中存储的参数进行拷贝,这里的s.regs[r].c应该就是a
						s.copies[c] = false	// 记录拷贝的value
						if s.f.pass.debug > regDebug {
							fmt.Printf("copy %s to %s : %s\n", a, c, &s.registers[r2])
						}
						s.setOrig(c, a)
						s.assignReg(r2, a, c)	// 将c的结果用r2保存并记录c的源value是a
						s.endRegs[p.ID] = append(s.endRegs[p.ID], endReg{r2, a, c})	// 记录前驱块的末尾寄存器r2的状态,保存的value从a变成了c
					}
				}
				s.freeReg(r)	// r寄存器保存的value已经赋值给r2了,那么r就可以被分配给别的value使用了,或者当前块中除了phi没有其他的value使用了参数,那么这个参数占用的寄存器也就可以释放以供其他value使用了
			}

			// Copy phi ops into new schedule.
			b.Values = append(b.Values, phis...)

			// Third pass - pick registers for phis whose inputs
			// were not in a register.
			for i, v := range phis {	// 遍历所有的phi,为需要寄存器却没有分配寄存器的phi分配一个寄存器
				if !s.values[v.ID].needReg {
					continue
				}
				if phiRegs[i] != noRegister {	// 找到主要参数的分配寄存器与当前块中的phi冲突的情况
					continue
				}
				if s.f.Config.use387 && v.Type.IsFloat() {
					continue // 387 can't handle floats in registers between blocks
				}
				// 到这里表示当前的phi的参数的寄存器不可直接用于在当前块的phi上,很可能是被其他的phi使用了
				m := s.compatRegs(v.Type) &^ phiUsed &^ s.used	// 希望找到一个可以使用的且适配v的类型的寄存器
				if m != 0 {	// 存在这样的寄存器
					r := pickReg(m)	// 提取一个可分配的寄存器
					phiRegs[i] = r
					phiUsed |= regMask(1) << r
				}
			}

			// Set registers for phis. Add phi spill code.
			for i, v := range phis {	// 遍历phi values,为phis设置存储的寄存器,没有分配寄存器的将会spill
				if !s.values[v.ID].needReg {
					continue
				}
				r := phiRegs[i]		// 获取分配给phi的寄存器
				if r == noRegister {	// 这说明实在没有多余的寄存器分配给这个phi了
					// stack-based phi
					// Spills will be inserted in all the predecessors below.
					s.values[v.ID].spill = v // v starts life spilled
					continue
				}
				// register-based phi
				s.assignReg(r, v, v)	// 用寄存器r保存v
			}

			// Deallocate any values which are no longer live. Phis are excluded.
			for r := register(0); r < s.numRegs; r++ {	// 遍历所有的寄存器,释放phi没有使用且在块开头不活跃的寄存器
				if phiUsed>>r&1 != 0 {	// phi value在使用这个寄存器
					continue
				}
				// 到这里表示当前块中的phi values没有使用到r这个寄存器
				v := s.regs[r].v	// 获取占据了寄存器的源value
				if v != nil && !regValLiveSet.contains(v.ID) {	// 没有占用这个寄存器的value且这个value不在当前块的开头活跃
					s.freeReg(r)	// 释放寄存器r
				}
			}

			// Save the starting state for use by merge edges.
			// We append to a stack allocated variable that we'll
			// later copy into s.startRegs in one fell swoop, to save
			// on allocations.
			regList := make([]startReg, 0, 32)	// 记录当前块中除了分配给phi value以外的寄存器起始状态
			for r := register(0); r < s.numRegs; r++ {	// 找到所有没有被分配给phi的寄存器,创建startReg并添加到regList中
				v := s.regs[r].v	// 获取分配了该寄存器的value
				if v == nil {	// 当前这个寄存器本身是空闲的
					continue
				}
				if phiUsed>>r&1 != 0 {	// 这个寄存器被phi占用了
					// Skip registers that phis used, we'll handle those
					// specially during merge edge processing.
					continue
				}
				regList = append(regList, startReg{r, v, s.regs[r].c, s.values[v.ID].uses.pos})
			}
			s.startRegs[b.ID] = make([]startReg, len(regList))
			copy(s.startRegs[b.ID], regList)

			if s.f.pass.debug > regDebug {
				fmt.Printf("after phis\n")
				for _, x := range s.startRegs[b.ID] {
					fmt.Printf("  %s: v%d\n", &s.registers[x.r], x.v.ID)
				}
			}
		}

		// Allocate space to record the desired registers for each value.
		if l := len(oldSched); cap(dinfo) < l {
			dinfo = make([]dentry, l)
		} else {
			dinfo = dinfo[:l]
			for i := range dinfo {
				dinfo[i] = dentry{}
			}
		}

		// Load static desired register info at the end of the block.
		desired.copy(&s.desired[b.ID])	// 获取当前块末尾所需的寄存器信息

		// Check actual assigned registers at the start of the next block(s).
		// Dynamically assigned registers will trump the static
		// desired registers computed during liveness analysis.
		// Note that we do this phase after startRegs is set above, so that
		// we get the right behavior for a block which branches to itself.
		for _, e := range b.Succs {		// 遍历所有后继,将传给后继的phi中的参数的所需寄存器记录下来
			succ := e.b
			// TODO: prioritize likely successor?
			for _, x := range s.startRegs[succ.ID] {	// 遍历后继块中起始寄存器状态
				desired.add(x.v.ID, x.r)	// 添加到当前块末尾想要的寄存器中
			}
			// Process phi ops in succ.
			pidx := e.i
			for _, v := range succ.Values {		// 遍历后继块中的values
				if v.Op != OpPhi {	// 找到后继块中的phi values
					break
				}
				if !s.values[v.ID].needReg {	// 这个phi需要用寄存器存储
					continue
				}
				rp, ok := s.f.getHome(v.ID).(*Register)		// 获取保存phi的寄存器
				if !ok {
					continue
				}
				desired.add(v.Args[pidx].ID, register(rp.num))	// 记录参数所需寄存器
			}
		}
		// Walk values backwards computing desired register info.
		// See computeLive for more comments.
		for i := len(oldSched) - 1; i >= 0; i-- {	// 倒序遍历values并记录每个value的所需输入以及输出寄存器
			v := oldSched[i]	// 获取value
			prefs := desired.remove(v.ID)	// 获取v所需的寄存器
			regspec := s.regspec(v.Op)	// 获取该操作对应的寄存器信息
			desired.clobber(regspec.clobbers)
			for _, j := range regspec.inputs {	// 遍历操作的输入信息并记录参数的所需寄存器
				if countRegs(j.regs) != 1 {	// 没有特定的寄存器作为输入
					continue
				}
				desired.clobber(j.regs)		// 令前面的value可以使用j.regs寄存器列表以保存v的参数
				desired.add(v.Args[j.idx].ID, pickReg(j.regs))	// 从j.regs寄存器列表中选择一个寄存器添加到参数所需寄存器中
			}
			if opcodeTable[v.Op].resultInArg0 {		// 结果保存在输入的寄存器中那么输入的参数所需寄存器也要加上当前value的所需寄存器
				if opcodeTable[v.Op].commutative {	// 参数交换后结果不变
					desired.addList(v.Args[1].ID, prefs)
				}
				desired.addList(v.Args[0].ID, prefs)
			}
			// Save desired registers for this value.
			dinfo[i].out = prefs
			for j, a := range v.Args {	// 遍历v的所有参数
				if j >= len(dinfo[i].in) {	// 从dentry结构体的定义来看,这里最多3个参数
					break
				}
				dinfo[i].in[j] = desired.get(a.ID)	// 获取参数所需寄存器最为当前value的寄存器输入
			}
		}

		// Process all the non-phi values.
		for idx, v := range oldSched {	// 遍历所有非phi values
			if s.f.pass.debug > regDebug {
				fmt.Printf("  processing %s\n", v.LongString())
			}
			regspec := s.regspec(v.Op)	// 获取该操作对应的寄存器信息
			if v.Op == OpPhi {
				f.Fatalf("phi %s not at start of block", v)
			}
			if v.Op == OpSP {
				s.assignReg(s.SPReg, v, v)
				b.Values = append(b.Values, v)
				s.advanceUses(v)
				s.sp = v.ID
				continue
			}
			if v.Op == OpSB {
				s.assignReg(s.SBReg, v, v)
				b.Values = append(b.Values, v)
				s.advanceUses(v)
				s.sb = v.ID
				continue
			}
			if v.Op == OpSelect0 || v.Op == OpSelect1 {
				if s.values[v.ID].needReg {
					var i = 0
					if v.Op == OpSelect1 {
						i = 1
					}
					s.assignReg(register(s.f.getHome(v.Args[0].ID).(LocPair)[i].(*Register).num), v, v)
				}
				b.Values = append(b.Values, v)
				s.advanceUses(v)
				goto issueSpill
			}
			if v.Op == OpGetG && s.f.Config.hasGReg {
				// use hardware g register
				if s.regs[s.GReg].v != nil {
					s.freeReg(s.GReg) // kick out the old value
				}
				s.assignReg(s.GReg, v, v)
				b.Values = append(b.Values, v)
				s.advanceUses(v)
				goto issueSpill
			}
			if v.Op == OpArg {
				// Args are "pre-spilled" values. We don't allocate
				// any register here. We just set up the spill pointer to
				// point at itself and any later user will restore it to use it.
				s.values[v.ID].spill = v
				b.Values = append(b.Values, v)
				s.advanceUses(v)
				continue
			}
			if v.Op == OpKeepAlive {
				// Make sure the argument to v is still live here.
				s.advanceUses(v)
				a := v.Args[0]		// 获取活跃的变量
				vi := &s.values[a.ID]
				if vi.regs == 0 && !vi.rematerializeable {	// 没有为该value分配寄存器且不可重新实现
					// Use the spill location.
					// This forces later liveness analysis to make the
					// value live at this point.
					v.SetArg(0, s.makeSpill(a, b))
				} else if _, ok := a.Aux.(GCNode); ok && vi.rematerializeable {
					// Rematerializeable value with a gc.Node. This is the address of
					// a stack object (e.g. an LEAQ). Keep the object live.
					// Change it to VarLive, which is what plive expects for locals.
					v.Op = OpVarLive
					v.SetArgs1(v.Args[1])
					v.Aux = a.Aux
				} else {
					// In-register and rematerializeable values are already live.
					// These are typically rematerializeable constants like nil,
					// or values of a variable that were modified since the last call.
					v.Op = OpCopy
					v.SetArgs1(v.Args[1])
				}
				b.Values = append(b.Values, v)
				continue
			}
			if len(regspec.inputs) == 0 && len(regspec.outputs) == 0 {	// 这个Op没有输入与输出的寄存器
				// No register allocation required (or none specified yet)
				s.freeRegs(regspec.clobbers)	// 释放影响的寄存器,之后可分配这些寄存器
				b.Values = append(b.Values, v)
				s.advanceUses(v)
				continue
			}

			if s.values[v.ID].rematerializeable {
				// Value is rematerializeable, don't issue it here.
				// It will get issued just before each use (see
				// allocValueToReg).
				for _, a := range v.Args {	// 所有参数的使用计数减一
					a.Uses--
				}
				s.advanceUses(v)
				continue
			}

			if s.f.pass.debug > regDebug {
				fmt.Printf("value %s\n", v.LongString())
				fmt.Printf("  out:")
				for _, r := range dinfo[idx].out {
					if r != noRegister {
						fmt.Printf(" %s", &s.registers[r])
					}
				}
				fmt.Println()
				for i := 0; i < len(v.Args) && i < 3; i++ {
					fmt.Printf("  in%d:", i)
					for _, r := range dinfo[idx].in[i] {
						if r != noRegister {
							fmt.Printf(" %s", &s.registers[r])
						}
					}
					fmt.Println()
				}
			}

			// Move arguments to registers. Process in an ordering defined
			// by the register specification (most constrained first).
			args = append(args[:0], v.Args...)	// 将当前value的参数都添加到args中
			for _, i := range regspec.inputs {	// 遍历输入的寄存器,为所有参数分配寄存器
				mask := i.regs	// 获取可输入的寄存器列表
				if mask&s.values[args[i.idx].ID].regs == 0 {	// 对应参数所在寄存器不在可作为输入的寄存器列表中
					// Need a new register for the input.
					mask &= s.allocatable
					mask &^= s.nospill
					// Used desired register if available.
					if i.idx < 3 {
						for _, r := range dinfo[idx].in[i.idx] {	// 遍历这个value的第i.idx个参数想要的输入寄存器,找到一个当前可用的寄存器保存到mask中,如果有所需寄存器的话
							if r != noRegister && (mask&^s.used)>>r&1 != 0 {	// 想要的寄存器与当前已使用的寄存器不冲突且可分配
								// Desired register is allowed and unused.
								mask = regMask(1) << r
								break
							}
						}
					}
					// Avoid registers we're saving for other values.
					if mask&^desired.avoid != 0 {	// 有与Avoid registers不冲突的寄存器
						mask &^= desired.avoid	// mask中去除Avoid registers
					}
				}
				args[i.idx] = s.allocValToReg(args[i.idx], mask, true, v.Pos)	// 从mask列表中找到一个可分配的寄存器分配给参数
			}

			// If the output clobbers the input register, make sure we have
			// at least two copies of the input register so we don't
			// have to reload the value from the spill location.
			if opcodeTable[v.Op].resultInArg0 {		// 操作的结果保存在第一个寄存器中,尝试为输出结果分配一个寄存器
				var m regMask
				if !s.liveAfterCurrentInstruction(v.Args[0]) {	// 第一个参数以后不再使用
					// arg0 is dead.  We can clobber its register.
					goto ok
				}
				if opcodeTable[v.Op].commutative && !s.liveAfterCurrentInstruction(v.Args[1]) {	// 该操作可交换参数且第二个参数在以后不再使用了
					args[0], args[1] = args[1], args[0]		// 交换,破坏掉以后不再使用的参数
					goto ok
				}
				if s.values[v.Args[0].ID].rematerializeable {
					// We can rematerialize the input, don't worry about clobbering it.
					goto ok
				}
				if opcodeTable[v.Op].commutative && s.values[v.Args[1].ID].rematerializeable {	// 参数可交换且第二个参数可以重新计算
					args[0], args[1] = args[1], args[0]
					goto ok
				}
				if countRegs(s.values[v.Args[0].ID].regs) >= 2 {	// 通过2个以上的寄存器保存第一个参数
					// we have at least 2 copies of arg0.  We can afford to clobber one.
					goto ok
				}
				if opcodeTable[v.Op].commutative && countRegs(s.values[v.Args[1].ID].regs) >= 2 {
					args[0], args[1] = args[1], args[0]
					goto ok
				}
				// 到这里表示参数不能被重新计算且以后还会用得到
				// We can't overwrite arg0 (or arg1, if commutative).  So we
				// need to make a copy of an input so we have a register we can modify.

				// Possible new registers to copy into.
				m = s.compatRegs(v.Args[0].Type) &^ s.used	// 获取可以存储第一个参数类型的可以使用的寄存器列表
				if m == 0 {
					// No free registers.  In this case we'll just clobber
					// an input and future uses of that input must use a restore.
					// TODO(khr): We should really do this like allocReg does it,
					// spilling the value with the most distant next use.
					goto ok
				}

				// 到这里表示有空闲的寄存器可以保存第一个参数
				// Try to move an input to the desired output.
				for _, r := range dinfo[idx].out {	// 遍历输出寄存器,先尽量满足输出保存
					if r != noRegister && m>>r&1 != 0 {	// 输出的结果所在寄存器与第一个参数所在寄存器列表拥有相同的寄存器
						m = regMask(1) << r	// 使用这个输出寄存器掩码
						args[0] = s.allocValToReg(v.Args[0], m, true, v.Pos)	// 将寄存器r分配给第一个参数
						// Note: we update args[0] so the instruction will
						// use the register copy we just made.
						goto ok
					}
				}
				// Try to copy input to its desired location & use its old
				// location as the result register.
				for _, r := range dinfo[idx].in[0] {	// 遍历第一个参数想要的寄存器,如果有就分配这个寄存器给第一个参数
					if r != noRegister && m>>r&1 != 0 {	// 找到一个可以使用的寄存器r
						m = regMask(1) << r
						c := s.allocValToReg(v.Args[0], m, true, v.Pos)	// 用寄存器r保存第一个参数
						s.copies[c] = false
						// Note: no update to args[0] so the instruction will
						// use the original copy.
						goto ok
					}
				}
				if opcodeTable[v.Op].commutative {	// 参数可交换,交换参数后原本的第二个参数就成了第一个
					for _, r := range dinfo[idx].in[1] {	// 为第二个参数分配寄存器
						if r != noRegister && m>>r&1 != 0 {
							m = regMask(1) << r
							c := s.allocValToReg(v.Args[1], m, true, v.Pos)
							s.copies[c] = false
							args[0], args[1] = args[1], args[0]
							goto ok
						}
					}
				}
				// m代表的可用的寄存器列表不匹配当前value的输入以及输出列表
				// Avoid future fixed uses if we can.
				if m&^desired.avoid != 0 {	// 排除避免分配的列表后还有可用寄存器
					m &^= desired.avoid
				}
				// Save input 0 to a new register so we can clobber it.
				c := s.allocValToReg(v.Args[0], m, true, v.Pos)	// 为第一个参数分配一个新寄存器
				s.copies[c] = false
			}

		ok:
			// Now that all args are in regs, we're ready to issue the value itself.
			// Before we pick a register for the output value, allow input registers
			// to be deallocated. We do this here so that the output can use the
			// same register as a dying input.
			if !opcodeTable[v.Op].resultNotInArgs {	// 当前value的result可以保存在参数寄存器中
				s.tmpused = s.nospill	// 设置当前指令使用的寄存器为s.nospill
				s.nospill = 0	// 清空s.nospill
				s.advanceUses(v) // frees any registers holding args that are no longer live
			}

			// Dump any registers which will be clobbered
			s.freeRegs(regspec.clobbers)	// 被破坏的寄存器可以使用了
			s.tmpused |= regspec.clobbers	// 被破坏的寄存器视为临时使用中

			// Pick registers for outputs.
			{
				outRegs := [2]register{noRegister, noRegister}
				var used regMask	// 记录使用的寄存器
				for _, out := range regspec.outputs {	// 处理所有输出的可用作输出的寄存器
					mask := out.regs & s.allocatable &^ used	// 可分配可用作输出寄存器且不处于使用中
					if mask == 0 {	// 输出的寄存器都被占用了
						continue
					}
					if opcodeTable[v.Op].resultInArg0 && out.idx == 0 {	// 参数保存在第一个寄存器中且当前是第一个输出寄存器
						if !opcodeTable[v.Op].commutative {	// 参数不能交换
							// Output must use the same register as input 0.
							r := register(s.f.getHome(args[0].ID).(*Register).num)	// 输出就是第一个寄存器的输入,获取这个寄存器
							mask = regMask(1) << r
						} else {	// 参数可交换
							// Output must use the same register as input 0 or 1.
							r0 := register(s.f.getHome(args[0].ID).(*Register).num)
							r1 := register(s.f.getHome(args[1].ID).(*Register).num)
							// Check r0 and r1 for desired output register.
							found := false
							for _, r := range dinfo[idx].out {	// 遍历当前value想要的的输出寄存器
								if (r == r0 || r == r1) && (mask&^s.used)>>r&1 != 0 {	// r是r0或者r1且r可分配可用作输出寄存器且不处于使用中
									mask = regMask(1) << r
									found = true
									// 如果value希望的输出寄存器是参数2的寄存器,因为结果要保存在参数1中,那么交换两个参数
									if r == r1 {	// 至少保证第一个参数是未被使用的,这样可以减少分配的寄存器数量
										args[0], args[1] = args[1], args[0]
									}
									break
								}
							}
							if !found {		// r0与r1都处于使用中
								// Neither are desired, pick r0.
								mask = regMask(1) << r0
							}
						}
					}
					for _, r := range dinfo[idx].out {	// 遍历想要的输出寄存器
						if r != noRegister && (mask&^s.used)>>r&1 != 0 {	// 想要的寄存器未使用
							// Desired register is allowed and unused.
							mask = regMask(1) << r
							break
						}
					}
					// Avoid registers we're saving for other values.
					if mask&^desired.avoid&^s.nospill != 0 {
						mask &^= desired.avoid	// 没有&^s.nospill,表示可以分配s.nospill中的寄存器吗
					}
					r := s.allocReg(mask, v)	// 为v分配一个寄存器
					outRegs[out.idx] = r	// 记录为输出分配的寄存器
					used |= regMask(1) << r		// 记录r已被使用
					s.tmpused |= regMask(1) << r	// 记录当前指令使用了寄存器r
				}
				// Record register choices
				if v.Type.IsTuple() {	// v的返回值是一个tuple类型,这个类型用2个寄存器
					var outLocs LocPair
					if r := outRegs[0]; r != noRegister {
						outLocs[0] = &s.registers[r]
					}
					if r := outRegs[1]; r != noRegister {
						outLocs[1] = &s.registers[r]
					}
					s.f.setHome(v, outLocs)
					// Note that subsequent SelectX instructions will do the assignReg calls.
				} else {	// 非tuple类型,第一个输出即是结果
					if r := outRegs[0]; r != noRegister {
						s.assignReg(r, v, v)	// 关联r与v
					}
				}
			}

			// deallocate dead args, if we have not done so
			if opcodeTable[v.Op].resultNotInArgs {	// 结果不保存在参数中
				s.nospill = 0	// 表示之后的寄存器都可以spill
				s.advanceUses(v) // frees any registers holding args that are no longer live	既然参数已经使用过了都应该要释放寄存器吧,当前这行带啊是不是应该放到if的外面?????????
			}
			s.tmpused = 0	// 临时使用的寄存器清零

			// Issue the Value itself.
			for i, a := range args {
				v.SetArg(i, a) // use register version of arguments
			}
			b.Values = append(b.Values, v)

		issueSpill:
		}
		// 所有values处理完毕

		// Copy the control values - we need this so we can reduce the
		// uses property of these values later.
		controls := append(make([]*Value, 0, 2), b.ControlValues()...)

		// Load control values into registers.
		for i, v := range b.ControlValues() {	// 遍历控制语句
			if !s.values[v.ID].needReg {
				continue
			}
			if s.f.pass.debug > regDebug {
				fmt.Printf("  processing control %s\n", v.LongString())
			}
			// We assume that a control input can be passed in any
			// type-compatible register. If this turns out not to be true,
			// we'll need to introduce a regspec for a block's control value.
			b.ReplaceControl(i, s.allocValToReg(v, s.compatRegs(v.Type), false, b.Pos))	// 为控制语句分配寄存器
		}

		// Reduce the uses of the control values once registers have been loaded.
		// This loop is equivalent to the advanceUses method.
		for _, v := range controls {	// 释放控制语句的uses
			vi := &s.values[v.ID]
			if !vi.needReg {
				continue
			}
			// Remove this use from the uses list.
			u := vi.uses
			vi.uses = u.next
			if u.next == nil {
				s.freeRegs(vi.regs) // value is dead
			}
			u.next = s.freeUseRecords
			s.freeUseRecords = u
		}

		// Spill any values that can't live across basic block boundaries.
		if s.f.Config.use387 {
			s.freeRegs(s.f.Config.fpRegMask)
		}

		// If we are approaching a merge point and we are the primary
		// predecessor of it, find live values that we use soon after
		// the merge point and promote them to registers now.
		if len(b.Succs) == 1 {	// 只有一个后继块,这里处理即将进入循环头块的情况,尽量为活跃且不可重新实现的values分配寄存器
			if s.f.Config.hasGReg && s.regs[s.GReg].v != nil {	// 有g寄存器且处于使用中
				s.freeReg(s.GReg) // Spill value in G register before any merge.
			}
			// For this to be worthwhile, the loop must have no calls in it.
			top := b.Succs[0].b		// 获取后继块
			loop := s.loopnest.b2l[top.ID]
			if loop == nil || loop.header != top || loop.containsUnavoidableCall {
				goto badloop
			}
			// 后继块是一个循环头且不存在不可避免地函数调用
			// TODO: sort by distance, pick the closest ones?
			for _, live := range s.live[b.ID] {		// 遍历b块结束时的活跃values
				if live.dist >= unlikelyDistance {
					// Don't preload anything live after the loop.
					continue
				}
				vid := live.ID	// 获取活跃value的ID
				vi := &s.values[vid]	// 获取这个value的状态结构体
				if vi.regs != 0 {	// 有已分配的寄存器
					continue
				}
				if vi.rematerializeable {	// 可重新实现
					continue
				}
				v := s.orig[vid]	// 获取原始的value
				if s.f.Config.use387 && v.Type.IsFloat() {
					continue // 387 can't handle floats in registers between blocks
				}
				m := s.compatRegs(v.Type) &^ s.used		// 获取未使用的可以装载v的寄存器列表
				if m&^desired.avoid != 0 {	// 除去避免分配的寄存器后还有可用寄存器
					m &^= desired.avoid
				}
				if m != 0 {
					s.allocValToReg(v, m, false, b.Pos)
				}
			}
		}
	badloop:
		;

		// Save end-of-block register state.
		// First count how many, this cuts allocations in half.
		k := 0	// 分配了多少个寄存器
		for r := register(0); r < s.numRegs; r++ {
			v := s.regs[r].v
			if v == nil {
				continue
			}
			k++
		}
		regList := make([]endReg, 0, k)	// 保存块结束时的寄存器状态
		for r := register(0); r < s.numRegs; r++ {
			v := s.regs[r].v
			if v == nil {
				continue
			}
			regList = append(regList, endReg{r, v, s.regs[r].c})
		}
		s.endRegs[b.ID] = regList

		if checkEnabled {
			regValLiveSet.clear()
			for _, x := range s.live[b.ID] {
				regValLiveSet.add(x.ID)
			}
			for r := register(0); r < s.numRegs; r++ {
				v := s.regs[r].v
				if v == nil {
					continue
				}
				if !regValLiveSet.contains(v.ID) {
					s.f.Fatalf("val %s is in reg but not live at end of %s", v, b)
				}
			}
		}

		// If a value is live at the end of the block and
		// isn't in a register, generate a use for the spill location.
		// We need to remember this information so that
		// the liveness analysis in stackalloc is correct.
		for _, e := range s.live[b.ID] {	// 遍历b块末尾的活跃信息
			vi := &s.values[e.ID]	// 获取活跃value的状态信息
			if vi.regs != 0 {	// 已分配了寄存器
				// in a register, we'll use that source for the merge.
				continue
			}
			if vi.rematerializeable {
				// we'll rematerialize during the merge.
				continue
			}
			//fmt.Printf("live-at-end spill for %s at %s\n", s.orig[e.ID], b)
			spill := s.makeSpill(s.orig[e.ID], b)
			s.spillLive[b.ID] = append(s.spillLive[b.ID], spill.ID)		// 记录b块末尾的live spill
		}

		// Clear any final uses.
		// All that is left should be the pseudo-uses added for values which
		// are live at the end of b.
		for _, e := range s.live[b.ID] {	// 遍历b块末尾的活跃信息,将value的uses置为nil
			u := s.values[e.ID].uses	// 获取live value对应的uses
			if u == nil {
				f.Fatalf("live at end, no uses v%d", e.ID)
			}
			if u.next != nil {
				f.Fatalf("live at end, too many uses v%d", e.ID)
			}
			s.values[e.ID].uses = nil
			u.next = s.freeUseRecords
			s.freeUseRecords = u
		}
	}

	// Decide where the spills we generated will go.
	s.placeSpills()

	// Anything that didn't get a register gets a stack location here.
	// (StoreReg, stack-based phis, inputs, ...)
	stacklive := stackalloc(s.f, s.spillLive)

	// Fix up all merge edges.
	s.shuffle(stacklive)

	// Erase any copies we never used.
	// Also, an unused copy might be the only use of another copy,
	// so continue erasing until we reach a fixed point.
	for {	// 删掉没有使用的copy
		progress := false
		for c, used := range s.copies {
			if !used && c.Uses == 0 {	// 未使用的copy
				if s.f.pass.debug > regDebug {
					fmt.Printf("delete copied value %s\n", c.LongString())
				}
				c.RemoveArg(0)	// 释放第一个参数
				f.freeValue(c)
				delete(s.copies, c)
				progress = true
			}
		}
		if !progress {
			break
		}
	}
	// 整理所有块中的values,去掉不合法的values
	for _, b := range s.visitOrder {
		i := 0
		for _, v := range b.Values {
			if v.Op == OpInvalid {
				continue
			}
			b.Values[i] = v
			i++
		}
		b.Values = b.Values[:i]
	}
}
// 将spill value放到一个合适的地方
func (s *regAllocState) placeSpills() {
	f := s.f	// 获取当前处理的函数

	// Precompute some useful info.
	phiRegs := make([]regMask, f.NumBlocks())	// 块ID -> 这个块中分配给phi的寄存器掩码信息
	for _, b := range s.visitOrder {	// 遍历所有的块,整理块中分配给phi的寄存器掩码信息
		var m regMask
		for _, v := range b.Values {	// 遍历块中所有values
			if v.Op != OpPhi {	// 只处理每个块中的phi
				break
			}
			if r, ok := f.getHome(v.ID).(*Register); ok {	// 获取分配给phi的寄存器
				m |= regMask(1) << uint(r.num)
			}
		}
		phiRegs[b.ID] = m
	}

	// Start maps block IDs to the list of spills
	// that go at the start of the block (but after any phis).
	start := map[ID][]*Value{}
	// After maps value IDs to the list of spills
	// that go immediately after that value ID.
	after := map[ID][]*Value{}

	for i := range s.values {	// 遍历这个函数中所有values的状态
		vi := s.values[i]	// 获取value对应的状态信息
		spill := vi.spill	// 获取这个value的spill
		if spill == nil {
			continue
		}
		if spill.Block != nil {
			// Some spills are already fully set up,
			// like OpArgs and stack-based phis.
			continue
		}
		v := s.orig[i]	// 获取初始value

		// Walk down the dominator tree looking for a good place to
		// put the spill of v.  At the start "best" is the best place
		// we have found so far.
		// TODO: find a way to make this O(1) without arbitrary cutoffs.
		best := v.Block	// 最佳spill的地方,在这个块的起始处,默认是初始value所在块
		bestArg := v	// spill的最佳arg,如果spill在别的块,那么需要换成那个块开头进入的copy的value
		var bestDepth int16		// 如果best是一个循环头的话,记录这个循环的深度
		if l := s.loopnest.b2l[best.ID]; l != nil {		// best块在一个循环内
			bestDepth = l.depth
		}
		b := best
		const maxSpillSearch = 100	// 表示最多遍历支配树中100个节点
		for i := 0; i < maxSpillSearch; i++ {
			// Find the child of b in the dominator tree which
			// dominates all restores.
			p := b	// 从value所在块开始遍历
			b = nil
			for c := s.sdom.Child(p); c != nil && i < maxSpillSearch; c, i = s.sdom.Sibling(c), i+1 {	// 向下遍历支配树
				if s.sdom[c.ID].entry <= vi.restoreMin && s.sdom[c.ID].exit >= vi.restoreMax {	// 找到支配v所在块的节点,按理说找的都是块的子孙节点,向下找到一个支配自己的块的话,想必当前块是在循环中
					// c also dominates all restores.  Walk down into c.
					b = c
					break
				}
			}
			if b == nil {	// 找了支配树中maxSpillSearch个节点也没有找到或者已经遍历完了p下面的所有支配节点
				// Ran out of blocks which dominate all restores.
				break
			}

			var depth int16		// b所在循环的深度
			if l := s.loopnest.b2l[b.ID]; l != nil {	// b在一个循环内
				depth = l.depth
			}
			if depth > bestDepth {	// b块处于p块的循环内
				// Don't push the spill into a deeper loop.
				continue
			}

			// If v is in a register at the start of b, we can
			// place the spill here (after the phis).
			if len(b.Preds) == 1 {	// 仅有一个前驱
				for _, e := range s.endRegs[b.Preds[0].b.ID] {	// 遍历前驱末尾所有寄存器状态
					if e.v == v {	// 找到了保存v的寄存器
						// Found a better spot for the spill.
						best = b
						bestArg = e.c
						bestDepth = depth
						break
					}
				}
			} else {
				for _, e := range s.startRegs[b.ID] {	// 遍历当前块的起始寄存器状态
					if e.v == v {	// 找到了保存v的寄存器
						// Found a better spot for the spill.
						best = b
						bestArg = e.c
						bestDepth = depth
						break
					}
				}
			}
		}

		// Put the spill in the best block we found.
		spill.Block = best
		spill.AddArg(bestArg)
		if best == v.Block && v.Op != OpPhi {	// spill的块就在初始value的块且不是spill一个phi
			// Place immediately after v.
			after[v.ID] = append(after[v.ID], spill)	// spill要放到v后面
		} else {
			// Place at the start of best block.
			start[best.ID] = append(start[best.ID], spill)	// spill放在best块的phi的后面
		}
	}

	// Insert spill instructions into the block schedules.
	var oldSched []*Value
	for _, b := range s.visitOrder {	// 遍历所有的块
		nphi := 0	// 记录b块的phi的数量
		for _, v := range b.Values {
			if v.Op != OpPhi {
				break
			}
			nphi++
		}
		oldSched = append(oldSched[:0], b.Values[nphi:]...)		// 将非phi的values添加到oldSched中
		b.Values = b.Values[:nphi]
		b.Values = append(b.Values, start[b.ID]...)		// 将spill放到phis的后面
		for _, v := range oldSched {	// 添加value以及要放在value后面的spill
			b.Values = append(b.Values, v)
			b.Values = append(b.Values, after[v.ID]...)
		}
	}
}

// shuffle fixes up all the merge edges (those going into blocks of indegree > 1).
// stacklive: 块ID -> 块末尾通过栈槽保存的live values或者spill values
func (s *regAllocState) shuffle(stacklive [][]ID) {
	var e edgeState
	e.s = s
	e.cache = map[ID][]*Value{}
	e.contents = map[Location]contentRecord{}
	if s.f.pass.debug > regDebug {
		fmt.Printf("shuffle %s\n", s.f.Name)
		fmt.Println(s.f.String())
	}

	for _, b := range s.visitOrder {	// 遍历所有快
		if len(b.Preds) <= 1 {	// 找到有多个前驱的块
			continue
		}
		e.b = b
		for i, edge := range b.Preds {	// 遍历b的前驱
			p := edge.b	// 获取前驱块
			e.p = p
			// 设置p块结束时的寄存器状态为当前状态,整理b块开始时希望的寄存器
			e.setup(i, s.endRegs[p.ID], s.startRegs[b.ID], stacklive[p.ID])
			e.process()	// 生成相关代码将values移动到目标Location中
		}
	}

	if s.f.pass.debug > regDebug {
		fmt.Printf("post shuffle %s\n", s.f.Name)
		fmt.Println(s.f.String())
	}
}

type edgeState struct {
	s    *regAllocState
	p, b *Block // edge goes from p->b.

	// for each pre-regalloc value, a list of equivalent cached values
	cache      map[ID][]*Value
	cachedVals []ID // (superset of) keys of the above map, for deterministic iteration		cache的keys

	// map from location to the value it contains
	contents map[Location]contentRecord

	// desired destination locations
	destinations []dstRecord	// 相当于记录当前块起始的value存储的Location或者phi的参数所要存储的Location
	extra        []dstRecord

	usedRegs              regMask // registers currently holding something
	uniqueRegs            regMask // registers holding the only copy of a value
	finalRegs             regMask // registers holding final target
	rematerializeableRegs regMask // registers that hold rematerializeable values
}
// 应该是记录一个栈槽或者寄存器当前记录的信息
type contentRecord struct {
	vid   ID       // pre-regalloc value		org value ID
	c     *Value   // cached value				current value
	final bool     // this is a satisfied destination
	pos   src.XPos // source position of use of the value
}

type dstRecord struct {
	loc    Location // register or stack slot
	vid    ID       // pre-regalloc value it should contain
	splice **Value  // place to store reference to the generating instruction		这个一般是phi中的参数value的引用
	pos    src.XPos // source position of use of this location
}

// setup initializes the edge state for shuffling.
/*
p视为b的前驱块
idx代表p是b的第几个前驱
srcReg记录p结尾的寄存器状态
dstReg记录b起始的寄存器状态
stacklive记录p块末尾通过栈槽保存的live values或者spill values
*/
func (e *edgeState) setup(idx int, srcReg []endReg, dstReg []startReg, stacklive []ID) {
	if e.s.f.pass.debug > regDebug {
		fmt.Printf("edge %s->%s\n", e.p, e.b)
	}

	// Clear state.
	for _, vid := range e.cachedVals {
		delete(e.cache, vid)
	}
	e.cachedVals = e.cachedVals[:0]
	for k := range e.contents {
		delete(e.contents, k)
	}
	e.usedRegs = 0
	e.uniqueRegs = 0
	e.finalRegs = 0
	e.rematerializeableRegs = 0

	// Live registers can be sources.
	for _, x := range srcReg {	// 先记录从p块进入当前块时的活跃的寄存器状态	x.c保存在e.s.registers[x.r]中
		e.set(&e.s.registers[x.r], x.v.ID, x.c, false, src.NoXPos) // don't care the position of the source
	}
	// So can all of the spill locations.
	for _, spillID := range stacklive {		// 遍历p块末尾通过栈槽保存的live values或者spill values
		v := e.s.orig[spillID]	// 获取初始value
		spill := e.s.values[v.ID].spill		// 获取spill value
		if !e.s.sdom.IsAncestorEq(spill.Block, e.p) {	// 找到spill所在块支配前驱块的情况
			// Spills were placed that only dominate the uses found
			// during the first regalloc pass. The edge fixup code
			// can't use a spill location if the spill doesn't dominate
			// the edge.
			// We are guaranteed that if the spill doesn't dominate this edge,
			// then the value is available in a register (because we called
			// makeSpill for every value not in a register at the start
			// of an edge).
			continue
		}
		e.set(e.s.f.getHome(spillID), v.ID, spill, false, src.NoXPos) // don't care the position of the source
	}

	// Figure out all the destinations we need.
	dsts := e.destinations[:0]
	for _, x := range dstReg {	// 遍历当前块起始的寄存器状态
		dsts = append(dsts, dstRecord{&e.s.registers[x.r], x.v.ID, nil, x.pos})
	}
	// Phis need their args to end up in a specific location.
	for _, v := range e.b.Values {
		if v.Op != OpPhi {	// 找到phi
			break
		}
		loc := e.s.f.getHome(v.ID)	// 获取phi的Location
		if loc == nil {
			continue
		}
		dsts = append(dsts, dstRecord{loc, v.Args[idx].ID, &v.Args[idx], v.Pos})	// 参数进入到当前存储phi的Location中
	}
	e.destinations = dsts

	if e.s.f.pass.debug > regDebug {
		for _, vid := range e.cachedVals {
			a := e.cache[vid]
			for _, c := range a {
				fmt.Printf("src %s: v%d cache=%s\n", e.s.f.getHome(c.ID), vid, c)
			}
		}
		for _, d := range e.destinations {
			fmt.Printf("dst %s: v%d\n", d.loc, d.vid)
		}
	}
}

// process generates code to move all the values to the right destination locations.
func (e *edgeState) process() {
	dsts := e.destinations

	// Process the destinations until they are all satisfied.
	for len(dsts) > 0 {
		i := 0
		for _, d := range dsts {	// 相当于记录当前块起始的value存储的Location或者phi的参数所要存储的Location
			if !e.processDest(d.loc, d.vid, d.splice, d.pos) {	// 将d.vid代表的value的copy存储到d.loc中
				// Failed - save for next iteration.
				// 为false时仅有vid只有一处copy且不可重新实现
				dsts[i] = d
				i++
			}
		}
		if i < len(dsts) {	// 表示e.processDest存在返回true的情况
			// Made some progress. Go around again.
			dsts = dsts[:i]

			// Append any extras destinations we generated.
			dsts = append(dsts, e.extra...)
			e.extra = e.extra[:0]
			continue
		}

		// 到这一步表示e.processDest遍历所有的dsts返回的都是false

		// We made no progress. That means that any
		// remaining unsatisfied moves are in simple cycles.
		// For example, A -> B -> C -> D -> A.
		//   A ----> B
		//   ^       |
		//   |       |
		//   |       v
		//   D <---- C

		// To break the cycle, we pick an unused register, say R,
		// and put a copy of B there.
		//   A ----> B
		//   ^       |
		//   |       |
		//   |       v
		//   D <---- C <---- R=copyofB
		// When we resume the outer loop, the A->B move can now proceed,
		// and eventually the whole cycle completes.

		// Copy any cycle location to a temp register. This duplicates
		// one of the cycle entries, allowing the just duplicated value
		// to be overwritten and the cycle to proceed.
		d := dsts[0]	// 获取第一项
		loc := d.loc
		vid := e.contents[loc].vid
		c := e.contents[loc].c	// 当前存储在loc中的value
		r := e.findRegFor(c.Type)	// 找到可以存储c.Type的一个可用寄存器
		if e.s.f.pass.debug > regDebug {
			fmt.Printf("breaking cycle with v%d in %s:%s\n", vid, loc, c)
		}
		e.erase(r)
		pos := d.pos.WithNotStmt()
		if _, isReg := loc.(*Register); isReg {	// loc是一个寄存器
			c = e.p.NewValue1(pos, OpCopy, c.Type, c)
		} else {
			c = e.p.NewValue1(pos, OpLoadReg, c.Type, c)
		}
		e.set(r, vid, c, false, pos)	// 将c从原来的loc转存到寄存器r中
		if c.Op == OpLoadReg && e.s.isGReg(register(r.(*Register).num)) {
			e.s.f.Fatalf("process.OpLoadReg targeting g: " + c.LongString())
		}
	}
}

// processDest generates code to put value vid into location loc. Returns true
// if progress was made.
func (e *edgeState) processDest(loc Location, vid ID, splice **Value, pos src.XPos) bool {
	pos = pos.WithNotStmt()
	occupant := e.contents[loc]		// 获取loc包含的信息
	if occupant.vid == vid {	// value已经在这个localtion里了
		// Value is already in the correct place.
		e.contents[loc] = contentRecord{vid, occupant.c, true, pos}	// 设置contentRecord.final为true
		if splice != nil {	// 存储了一个phi的参数的引用
			(*splice).Uses--
			*splice = occupant.c
			occupant.c.Uses++
		}
		// Note: if splice==nil then c will appear dead. This is
		// non-SSA formed code, so be careful after this pass not to run
		// deadcode elimination.
		if _, ok := e.s.copies[occupant.c]; ok {	// c是一个copy
			// The copy at occupant.c was used to avoid spill.
			e.s.copies[occupant.c] = true	// 标记这个copy value为true,表示被使用了
		}
		return true
	}

	// Check if we're allowed to clobber the destination location.
	if len(e.cache[occupant.vid]) == 1 && !e.s.values[occupant.vid].rematerializeable {	// 等价的拷贝value只有一个且不可重新实现
		// We can't overwrite the last copy
		// of a value that needs to survive.
		return false
	}

	// Copy from a source of v, register preferred.
	v := e.s.orig[vid]	// 获取source value
	var c *Value	// 存储在src这个Location中的value
	var src Location	// 对于source value的所有拷贝,找到一个Location(寄存器存储优先)
	if e.s.f.pass.debug > regDebug {
		fmt.Printf("moving v%d to %s\n", vid, loc)
		fmt.Printf("sources of v%d:", vid)
	}
	for _, w := range e.cache[vid] {	// 遍历对source value的拷贝,找到一个Location(寄存器优先)
		h := e.s.f.getHome(w.ID)	// 获取存储w这个拷贝的Location
		if e.s.f.pass.debug > regDebug {
			fmt.Printf(" %s:%s", h, w)
		}
		_, isreg := h.(*Register)	// h是寄存器
		if src == nil || isreg {
			c = w
			src = h
		}
	}
	if e.s.f.pass.debug > regDebug {
		if src != nil {
			fmt.Printf(" [use %s]\n", src)
		} else {
			fmt.Printf(" [no source]\n")
		}
	}
	// 如果loc也就是存储目标是一个寄存器,那么dstReg就是true
	_, dstReg := loc.(*Register)

	// Pre-clobber destination. This avoids the
	// following situation:
	//   - v is currently held in R0 and stacktmp0.
	//   - We want to copy stacktmp1 to stacktmp0.
	//   - We choose R0 as the temporary register.
	// During the copy, both R0 and stacktmp0 are
	// clobbered, losing both copies of v. Oops!
	// Erasing the destination early means R0 will not
	// be chosen as the temp register, as it will then
	// be the last copy of v.
	e.erase(loc)	// 清除loc中的存储
	var x *Value
	// c == nil表示vid没有拷贝的value
	if c == nil || e.s.values[vid].rematerializeable {
		if !e.s.values[vid].rematerializeable {	// 到这里vid对应的value必定可重新实现
			e.s.f.Fatalf("can't find source for %s->%s: %s\n", e.p, e.b, v.LongString())
		}
		if dstReg {		// 打算将可重新实现的value存储到寄存器中
			x = v.copyInto(e.p)		// 在e.p块中拷贝一个与v一样的value
		} else {	// 打算将value存储到栈槽中
			// Rematerialize into stack slot. Need a free
			// register to accomplish this.
			r := e.findRegFor(v.Type)	// 找到一个可以存放v.Type的寄存器r
			e.erase(r)	// 清除寄存器中存储的value
			x = v.copyIntoWithXPos(e.p, pos)	// 在p块中创建一个v的拷贝
			e.set(r, vid, x, false, pos)	// p块末尾寄存器r存储x
			// Make sure we spill with the size of the slot, not the
			// size of x (which might be wider due to our dropping
			// of narrowing conversions).
			x = e.p.NewValue1(pos, OpStoreReg, loc.(LocalSlot).Type, x)	// 从x所在的寄存器中存储到栈槽中
		}
	} else {
		// Emit move from src to dst.
		_, srcReg := src.(*Register)
		if srcReg {	// src是寄存器
			if dstReg {		// 寄存器存储到寄存器中
				x = e.p.NewValue1(pos, OpCopy, c.Type, c)
			} else {	// 寄存器存到栈上
				x = e.p.NewValue1(pos, OpStoreReg, loc.(LocalSlot).Type, c)
			}
		} else {
			if dstReg {	// src是内存,dst是寄存器
				x = e.p.NewValue1(pos, OpLoadReg, c.Type, c)
			} else {
				// mem->mem. Use temp register.
				r := e.findRegFor(c.Type)	// 找到一个临时寄存器用于存储
				e.erase(r)	// 清除寄存器中保存的value
				t := e.p.NewValue1(pos, OpLoadReg, c.Type, c)	//	加载c到寄存器
				e.set(r, vid, t, false, pos)	// 寄存器r存储t这个value执行的结果
				x = e.p.NewValue1(pos, OpStoreReg, loc.(LocalSlot).Type, t)	// 创建一个OpStoreReg的value用于存储寄存器到栈槽
			}
		}
	}
	e.set(loc, vid, x, true, pos)	// x这个操作的结果保存到loc中
	if x.Op == OpLoadReg && e.s.isGReg(register(loc.(*Register).num)) {		// 把数据加载到了GReg中了
		e.s.f.Fatalf("processDest.OpLoadReg targeting g: " + x.LongString())
	}
	if splice != nil {
		(*splice).Uses--
		*splice = x
		x.Uses++
	}
	return true
}

// set changes the contents of location loc to hold the given value and its cached representative.
func (e *edgeState) set(loc Location, vid ID, c *Value, final bool, pos src.XPos) {
	e.s.f.setHome(c, loc)	// 设置c当前占用的Location
	e.contents[loc] = contentRecord{vid, c, final, pos}	// 记录loc中当前存储的是vid对应的value的拷贝c
	a := e.cache[vid]
	if len(a) == 0 {
		e.cachedVals = append(e.cachedVals, vid)
	}
	a = append(a, c)
	e.cache[vid] = a
	if r, ok := loc.(*Register); ok {	// loc是一个寄存器
		if e.usedRegs&(regMask(1)<<uint(r.num)) != 0 {	// 是一个使用中的寄存器
			e.s.f.Fatalf("%v is already set (v%d/%v)", r, vid, c)
		}
		e.usedRegs |= regMask(1) << uint(r.num)		// 标记该寄存器已被使用
		if final {	// 是最终的结果
			e.finalRegs |= regMask(1) << uint(r.num)
		}
		if len(a) == 1 {
			e.uniqueRegs |= regMask(1) << uint(r.num)
		}
		if len(a) == 2 {	// vid对应的value有多个要用寄存器保存
			if t, ok := e.s.f.getHome(a[0].ID).(*Register); ok {
				e.uniqueRegs &^= regMask(1) << uint(t.num)	// 从e.uniqueRegs中去掉上方if块中标记的寄存器
			}
		}
		if e.s.values[vid].rematerializeable {
			e.rematerializeableRegs |= regMask(1) << uint(r.num)
		}
	}
	if e.s.f.pass.debug > regDebug {
		fmt.Printf("%s\n", c.LongString())
		fmt.Printf("v%d now available in %s:%s\n", vid, loc, c)
	}
}

// erase removes any user of loc.
func (e *edgeState) erase(loc Location) {
	cr := e.contents[loc]	// 获取loc中存储的value信息
	if cr.c == nil {	// 没有存储value,不需要清除
		return
	}
	vid := cr.vid	// source value的ID

	if cr.final {
		// Add a destination to move this value back into place.
		// Make sure it gets added to the tail of the destination queue
		// so we make progress on other moves first.
		e.extra = append(e.extra, dstRecord{loc, cr.vid, nil, cr.pos})
	}

	// Remove c from the list of cached values.
	a := e.cache[vid]	// 获取vid的拷贝列表
	for i, c := range a {	// 遍历拷贝列表
		if e.s.f.getHome(c.ID) == loc {	// 当前存储在loc中的value就是c
			if e.s.f.pass.debug > regDebug {
				fmt.Printf("v%d no longer available in %s:%s\n", vid, loc, c)
			}
			a[i], a = a[len(a)-1], a[:len(a)-1]		// 将c从a中移除
			break
		}
	}
	e.cache[vid] = a

	// Update register masks.
	if r, ok := loc.(*Register); ok {	// 如果loc是一个寄存器那就释放寄存器
		e.usedRegs &^= regMask(1) << uint(r.num)
		if cr.final {
			e.finalRegs &^= regMask(1) << uint(r.num)
		}
		e.rematerializeableRegs &^= regMask(1) << uint(r.num)
	}
	if len(a) == 1 {	// 只剩最后一个了
		if r, ok := e.s.f.getHome(a[0].ID).(*Register); ok {	// 最后一个元素使用寄存器存储的
			e.uniqueRegs |= regMask(1) << uint(r.num)	// 记录当前寄存器存储的copy value只有一个了
		}
	}
}

// findRegFor finds a register we can use to make a temp copy of type typ.
func (e *edgeState) findRegFor(typ *types.Type) Location {
	// Which registers are possibilities.
	types := &e.s.f.Config.Types
	m := e.s.compatRegs(typ)	// 找出符合typ类型的寄存器掩码列表

	// Pick a register. In priority order:
	// 1) an unused register
	// 2) a non-unique register not holding a final value
	// 3) a non-unique register
	// 4) a register holding a rematerializeable value
	x := m &^ e.usedRegs
	if x != 0 {
		return &e.s.registers[pickReg(x)]
	}
	x = m &^ e.uniqueRegs &^ e.finalRegs
	if x != 0 {
		return &e.s.registers[pickReg(x)]
	}
	x = m &^ e.uniqueRegs
	if x != 0 {
		return &e.s.registers[pickReg(x)]
	}
	x = m & e.rematerializeableRegs
	if x != 0 {
		return &e.s.registers[pickReg(x)]
	}

	// No register is available.
	// Pick a register to spill.
	for _, vid := range e.cachedVals {
		a := e.cache[vid]	// vid的所有拷贝values
		for _, c := range a {
			if r, ok := e.s.f.getHome(c.ID).(*Register); ok && m>>uint(r.num)&1 != 0 {	// 找到用寄存器存放的拷贝value且该寄存器可用于这个类型
				if !c.rematerializeable() {		// c不可重新实现,那么需要将寄存器spill
					x := e.p.NewValue1(c.Pos, OpStoreReg, c.Type, c)	// 创建一个c的spill
					// Allocate a temp location to spill a register to.
					// The type of the slot is immaterial - it will not be live across
					// any safepoint. Just use a type big enough to hold any register.
					t := LocalSlot{N: e.s.f.fe.Auto(c.Pos, types.Int64), Type: types.Int64}	// 创建一个栈槽,寄存器的size是64位,所以类型为Int64
					// TODO: reuse these slots. They'll need to be erased first.
					e.set(t, vid, x, false, c.Pos)		// 用栈槽保存这个spill
					if e.s.f.pass.debug > regDebug {
						fmt.Printf("  SPILL %s->%s %s\n", r, t, x.LongString())
					}
				}
				// r will now be overwritten by the caller. At some point
				// later, the newly saved value will be moved back to its
				// final destination in processDest.
				return r	// 将寄存器返回
			}
		}
	}

	fmt.Printf("m:%d unique:%d final:%d rematerializable:%d\n", m, e.uniqueRegs, e.finalRegs, e.rematerializeableRegs)
	for _, vid := range e.cachedVals {
		a := e.cache[vid]
		for _, c := range a {
			fmt.Printf("v%d: %s %s\n", vid, c, e.s.f.getHome(c.ID))
		}
	}
	e.s.f.Fatalf("can't find empty register on edge %s->%s", e.p, e.b)
	return nil
}

// rematerializeable reports whether the register allocator should recompute
// a value instead of spilling/restoring it.
func (v *Value) rematerializeable() bool {
	if !opcodeTable[v.Op].rematerializeable {
		return false
	}
	for _, a := range v.Args {
		// SP and SB (generated by OpSP and OpSB) are always available.
		if a.Op != OpSP && a.Op != OpSB {
			return false
		}
	}
	return true
}

type liveInfo struct {
	ID   ID       // ID of value
	dist int32    // # of instructions before next use		一个计算的距离
	pos  src.XPos // source position of next use
}

// computeLive computes a map from block ID to a list of value IDs live at the end
// of that block. Together with the value ID is a count of how many instructions
// to the next use of that value. The resulting map is stored in s.live.
// computeLive also computes the desired register information at the end of each block.
// This desired register information is stored in s.desired.
// TODO: this could be quadratic if lots of variables are live across lots of
// basic blocks. Figure out a way to make this function (or, more precisely, the user
// of this function) require only linear size & time.
func (s *regAllocState) computeLive() {
	f := s.f
	s.live = make([][]liveInfo, f.NumBlocks())
	s.desired = make([]desiredState, f.NumBlocks())
	var phis []*Value

	live := f.newSparseMap(f.NumValues()) // 临时记录当前块中的活跃变量
	defer f.retSparseMap(live)
	t := f.newSparseMap(f.NumValues()) // 保存当前块的前驱块的活跃valueID以及最短被再次使用的距离
	defer f.retSparseMap(t)

	// Keep track of which value we want in each register.
	var desired desiredState

	// Instead of iterating over f.Blocks, iterate over their postordering.
	// Liveness information flows backward, so starting at the end
	// increases the probability that we will stabilize quickly.
	// TODO: Do a better job yet. Here's one possibility:
	// Calculate the dominator tree and locate all strongly connected components.
	// If a value is live in one block of an SCC, it is live in all.
	// Walk the dominator tree from end to beginning, just once, treating SCC
	// components as single blocks, duplicated calculated liveness information
	// out to all of them.
	po := f.postorder()
	s.loopnest = f.loopnest()
	s.loopnest.calculateDepths()
	for {
		changed := false

		for _, b := range po { // 倒序遍历块
			// Start with known live values at the end of the block.
			// Add len(b.Values) to adjust from end-of-block distance
			// to beginning-of-block distance.
			live.clear()
			for _, e := range s.live[b.ID] {	// 记录当前块中的活跃values到live中
				live.set(e.ID, e.dist+int32(len(b.Values)), e.pos)
			}

			// Mark control values as live
			for _, c := range b.ControlValues() {
				if s.values[c.ID].needReg { // 需要用到寄存器的控制value也加入到live中
					live.set(c.ID, int32(len(b.Values)), b.Pos) // 设置控制value的距离为b块中的values数量
				}
			}

			// Propagate backwards to the start of the block
			// Assumes Values have been scheduled.
			phis = phis[:0]                           // 存储当前块中的phi
			for i := len(b.Values) - 1; i >= 0; i-- { // 反向遍历块的values
				v := b.Values[i]  // 获取第i个values
				live.remove(v.ID) // 因为是倒序遍历values，所以之后该value不是活跃的
				if v.Op == OpPhi {
					// save phi ops for later
					phis = append(phis, v)
					continue
				}
				if opcodeTable[v.Op].call { // 当前value是一个函数调用
					c := live.contents()
					for i := range c { // 遍历当前活跃的value，在函数调用之前活跃的value到下一个次使用的距离加长
						c[i].val += unlikelyDistance
					}
				}
				for _, a := range v.Args { // 遍历v的参数，参数需要使用寄存器的话就将参数设置为活跃
					if s.values[a.ID].needReg {
						live.set(a.ID, int32(i), v.Pos) // 参数的距离设置为value在块中定义的下标
					}
				}
			}
			// Propagate desired registers backwards.
			desired.copy(&s.desired[b.ID])
			for i := len(b.Values) - 1; i >= 0; i-- { // 倒序遍历块中的values
				v := b.Values[i]
				prefs := desired.remove(v.ID)	// 获取v希望被分配到的寄存器数组
				if v.Op == OpPhi {
					// TODO: if v is a phi, save desired register for phi inputs.
					// For now, we just drop it and don't propagate
					// desired registers back though phi nodes.
					continue
				}
				regspec := s.regspec(v.Op)	// 获取v.Op的寄存器信息
				// Cancel desired registers if they get clobbered.
				desired.clobber(regspec.clobbers)
				// Update desired registers if there are any fixed register inputs.
				for _, j := range regspec.inputs {
					if countRegs(j.regs) != 1 {		// 有明确希望获取的一个寄存器
						continue
					}
					desired.clobber(j.regs)
					desired.add(v.Args[j.idx].ID, pickReg(j.regs))	// 第j.idx个参数必须用某个固定的寄存器保存
				}
				// Set desired register of input 0 if this is a 2-operand instruction.
				if opcodeTable[v.Op].resultInArg0 {
					if opcodeTable[v.Op].commutative {	// 这个操作可以交换参数,不影响结果
						desired.addList(v.Args[1].ID, prefs)
					}
					desired.addList(v.Args[0].ID, prefs)	// v希望用prefs中的寄存器存储结果,但结果是放在第一个参数中,所以第一个参数要添加这些寄存器
				}
			}

			// For each predecessor of b, expand its list of live-at-end values.
			// invariant: live contains the values live at the start of b (excluding phi inputs)
			for i, e := range b.Preds {	// 更新b的前驱中的live values
				p := e.b
				// Compute additional distance for the edge.
				// Note: delta must be at least 1 to distinguish the control
				// value use from the first user in a successor block.
				delta := int32(normalDistance)
				if len(p.Succs) == 2 { // 通过静态分值预测计算度量值
					if p.Succs[0].b == b && p.Likely == BranchLikely ||
						p.Succs[1].b == b && p.Likely == BranchUnlikely {
						delta = likelyDistance
					}
					if p.Succs[0].b == b && p.Likely == BranchUnlikely ||
						p.Succs[1].b == b && p.Likely == BranchLikely {
						delta = unlikelyDistance
					}
				}

				// Update any desired registers at the end of p.
				s.desired[p.ID].merge(&desired)		// 前驱中的寄存器合并后继中的记录

				// Start t off with the previously known live values at the end of p.
				t.clear()
				for _, e := range s.live[p.ID] {	// 设置已知的p块中的live values到t中
					t.set(e.ID, e.dist, e.pos)
				}
				update := false

				// Add new live values from scanning this block.
				for _, e := range live.contents() {	// 遍历当前块中的live values
					d := e.val + delta	// 计算距离p块的距离
					if !t.contains(e.key) || d < t.get(e.key) {		// t中记录距离最小的后继块中的live values
						update = true
						t.set(e.key, d, e.aux)
					}
				}
				// Also add the correct arg from the saved phi values.
				// All phis are at distance delta (we consider them
				// simultaneously happening at the start of the block).
				for _, v := range phis {	// 遍历当前块中的所有phi
					id := v.Args[i].ID	// 第i个参数的id
					if s.values[id].needReg && (!t.contains(id) || delta < t.get(id)) {	// t中记录距离最小的后继块中的live values
						update = true
						t.set(id, delta, v.Pos)
					}
				}

				if !update {
					continue
				}
				// The live set has changed, update it.
				l := s.live[p.ID][:0]
				if cap(l) < t.size() {
					l = make([]liveInfo, 0, t.size())
				}
				for _, e := range t.contents() {	// t中的内容保存到l中
					l = append(l, liveInfo{e.key, e.val, e.aux})
				}
				s.live[p.ID] = l
				changed = true
			}
		}

		if !changed {
			break
		}
	}
	if f.pass.debug > regDebug {
		fmt.Println("live values at end of each block")
		for _, b := range f.Blocks {
			fmt.Printf("  %s:", b)
			for _, x := range s.live[b.ID] {
				fmt.Printf(" v%d", x.ID)
				for _, e := range s.desired[b.ID].entries {
					if e.ID != x.ID {
						continue
					}
					fmt.Printf("[")
					first := true
					for _, r := range e.regs {
						if r == noRegister {
							continue
						}
						if !first {
							fmt.Printf(",")
						}
						fmt.Print(&s.registers[r])
						first = false
					}
					fmt.Printf("]")
				}
			}
			if avoid := s.desired[b.ID].avoid; avoid != 0 {
				fmt.Printf(" avoid=%v", s.RegMaskString(avoid))
			}
			fmt.Println()
		}
	}
}

// A desiredState represents desired register assignments.
type desiredState struct {	// 表示一个块中的某些values想要被分配到的寄存器
	// Desired assignments will be small, so we just use a list
	// of valueID+registers entries.
	entries []desiredStateEntry
	// Registers that other values want to be in.  This value will
	// contain at least the union of the regs fields of entries, but
	// may contain additional entries for values that were once in
	// this data structure but are no longer.
	avoid regMask // 其他value可能用到的寄存器
}
type desiredStateEntry struct {
	// (pre-regalloc) value
	ID ID // 当前块中的某个valueID,表示这个value需要指定的寄存器,保存在regs中
	// Registers it would like to be in, in priority order.
	// Unused slots are filled with noRegister.
	regs [4]register
}

func (d *desiredState) clear() {
	d.entries = d.entries[:0]
	d.avoid = 0
}

// get returns a list of desired registers for value vid.
func (d *desiredState) get(vid ID) [4]register {
	for _, e := range d.entries {
		if e.ID == vid {
			return e.regs
		}
	}
	return [4]register{noRegister, noRegister, noRegister, noRegister}
}

// add records that we'd like value vid to be in register r.
func (d *desiredState) add(vid ID, r register) {
	d.avoid |= regMask(1) << r // 添加到d.avoid中
	for i := range d.entries { // 遍历所有的entries
		e := &d.entries[i]
		if e.ID != vid { // 找到分配给这个value的entry
			continue
		}
		if e.regs[0] == r {
			// Already known and highest priority
			return
		}
		for j := 1; j < len(e.regs); j++ {
			if e.regs[j] == r { // 找到第j个寄存器就是当前要被分配的寄存器
				// Move from lower priority to top priority
				copy(e.regs[1:], e.regs[:j]) // 将前j个寄存器向后移
				e.regs[0] = r                // 设置r为第一个,表示最高优先级
				return
			}
		}
		// 没有找到为该value分配的指定寄存器
		copy(e.regs[1:], e.regs[:]) // 所有寄存器后移一位
		e.regs[0] = r               // 设置r为第一个,表示最高优先级
		return
	}
	// 没有找到当前vid,再添加一个entry
	d.entries = append(d.entries, desiredStateEntry{vid, [4]register{r, noRegister, noRegister, noRegister}})
}
// 将regs添加到vid希望的寄存器中
func (d *desiredState) addList(vid ID, regs [4]register) {
	// regs is in priority order, so iterate in reverse order.
	for i := len(regs) - 1; i >= 0; i-- { // 倒序遍历regs
		r := regs[i]         // 获取register
		if r != noRegister { // 有想要分配的寄存器
			d.add(vid, r) // 将r添加到d中
		}
	}
}

// clobber erases any desired registers in the set m.
func (d *desiredState) clobber(m regMask) {
	for i := 0; i < len(d.entries); {	// 这是要破坏当前记录的当前块中的所有values中想要分配的寄存器
		e := &d.entries[i]
		j := 0
		for _, r := range e.regs {
			if r != noRegister && m>>r&1 == 0 {		// 表示当前这个想要分配的寄存器没有被影响
				e.regs[j] = r
				j++
			}
		}
		if j == 0 { // 当前entry没有想要的寄存器或者想要的寄存器都被破坏了,将这个entry弹出
			// No more desired registers for this value.
			d.entries[i] = d.entries[len(d.entries)-1]
			d.entries = d.entries[:len(d.entries)-1]
			continue
		}
		for ; j < len(e.regs); j++ { // 将剩下的空间赋值为noRegister
			e.regs[j] = noRegister
		}
		i++
	}
	d.avoid &^= m	// 将m中二进制为1的bit位置清0,因为是倒序遍历,所以可以认为之前的values可以分配m中的寄存器
}

// copy copies a desired state from another desiredState x.
func (d *desiredState) copy(x *desiredState) {
	d.entries = append(d.entries[:0], x.entries...)
	d.avoid = x.avoid
}

// remove removes the desired registers for vid and returns them.
func (d *desiredState) remove(vid ID) [4]register {
	for i := range d.entries {
		if d.entries[i].ID == vid {		// 遍历entries找到与目标vid相同的desiredStateEntry
			regs := d.entries[i].regs
			d.entries[i] = d.entries[len(d.entries)-1]
			d.entries = d.entries[:len(d.entries)-1]
			return regs
		}
	}
	return [4]register{noRegister, noRegister, noRegister, noRegister}
}

// merge merges another desired state x into d.
func (d *desiredState) merge(x *desiredState) {
	d.avoid |= x.avoid	// 后面的块要用到的寄存器也避免分配
	// There should only be a few desired registers, so
	// linear insert is ok.
	for _, e := range x.entries {
		d.addList(e.ID, e.regs)
	}
}

func min32(x, y int32) int32 {
	if x < y {
		return x
	}
	return y
}
func max32(x, y int32) int32 {
	if x > y {
		return x
	}
	return y
}

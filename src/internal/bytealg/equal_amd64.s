// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#include "go_asm.h"
#include "textflag.h"

// memequal(a, b unsafe.Pointer, size uintptr) bool
TEXT runtime·memequal(SB),NOSPLIT,$0-25
	MOVQ	a+0(FP), SI	//参数1存储到SI
	MOVQ	b+8(FP), DI	//参数2存储到DI
	CMPQ	SI, DI		//比较两个指针是否相同
	JEQ	eq
	MOVQ	size+16(FP), BX	//两块内存比较的长度存储到BX，参数3
	LEAQ	ret+24(FP), AX	//返回值的指针存储到AX
	JMP	memeqbody<>(SB)
eq:
	MOVB	$1, ret+24(FP)	//返回1
	RET

// memequal_varlen(a, b unsafe.Pointer) bool
TEXT runtime·memequal_varlen(SB),NOSPLIT,$0-17
	MOVQ	a+0(FP), SI
	MOVQ	b+8(FP), DI
	CMPQ	SI, DI
	JEQ	eq
	MOVQ	8(DX), BX    // compiler stores size at offset 8 in the closure
	LEAQ	ret+16(FP), AX
	JMP	memeqbody<>(SB)
eq:
	MOVB	$1, ret+16(FP)
	RET

// a in SI
// b in DI
// count in BX
// address of result byte in AX
TEXT memeqbody<>(SB),NOSPLIT,$0-0
	CMPQ	BX, $8	//比较的长度小于8走small逻辑
	JB	small
	CMPQ	BX, $64	//比较的长度小于64走bigloop逻辑
	JB	bigloop
	CMPB	internal∕cpu·X86+const_offsetX86HasAVX2(SB), $1
	JE	hugeloop_avx2

	// 64 bytes at a time using xmm registers
hugeloop:
	CMPQ	BX, $64
	JB	bigloop
	MOVOU	(SI), X0
	MOVOU	(DI), X1
	MOVOU	16(SI), X2
	MOVOU	16(DI), X3
	MOVOU	32(SI), X4
	MOVOU	32(DI), X5
	MOVOU	48(SI), X6
	MOVOU	48(DI), X7
	PCMPEQB	X1, X0
	PCMPEQB	X3, X2
	PCMPEQB	X5, X4
	PCMPEQB	X7, X6
	PAND	X2, X0
	PAND	X6, X4
	PAND	X4, X0
	PMOVMSKB X0, DX
	ADDQ	$64, SI
	ADDQ	$64, DI
	SUBQ	$64, BX
	CMPL	DX, $0xffff
	JEQ	hugeloop
	MOVB	$0, (AX)
	RET

	// 64 bytes at a time using ymm registers
hugeloop_avx2:
	CMPQ	BX, $64
	JB	bigloop_avx2
	VMOVDQU	(SI), Y0
	VMOVDQU	(DI), Y1
	VMOVDQU	32(SI), Y2
	VMOVDQU	32(DI), Y3
	VPCMPEQB	Y1, Y0, Y4
	VPCMPEQB	Y2, Y3, Y5
	VPAND	Y4, Y5, Y6
	VPMOVMSKB Y6, DX
	ADDQ	$64, SI
	ADDQ	$64, DI
	SUBQ	$64, BX
	CMPL	DX, $0xffffffff
	JEQ	hugeloop_avx2
	VZEROUPPER
	MOVB	$0, (AX)
	RET

bigloop_avx2:
	VZEROUPPER

	// 8 bytes at a time using 64-bit register
bigloop:
	CMPQ	BX, $8	//当BX中的值小于等于8后走leftover逻辑
	JBE	leftover
	MOVQ	(SI), CX	//分别从两块内存中取8个字节分别存储到CX与DX中
	MOVQ	(DI), DX
	ADDQ	$8, SI	//两块内存的指针分别加8
	ADDQ	$8, DI
	SUBQ	$8, BX	//BX减8
	CMPQ	CX, DX
	JEQ	bigloop
	MOVB	$0, (AX)
	RET

	// remaining 0-8 bytes
leftover:
	MOVQ	-8(SI)(BX*1), CX	//取最后8个字节
	MOVQ	-8(DI)(BX*1), DX
	CMPQ	CX, DX
	SETEQ	(AX)
	RET

small:
	CMPQ	BX, $0
	JEQ	equal

	LEAQ	0(BX*8), CX
	NEGQ	CX

	CMPB	SI, $0xf8
	JA	si_high

	// load at SI won't cross a page boundary.
	MOVQ	(SI), SI
	JMP	si_finish
si_high:
	// address ends in 11111xxx. Load up to bytes we want, move to correct position.
	MOVQ	-8(SI)(BX*1), SI
	SHRQ	CX, SI
si_finish:

	// same for DI.
	CMPB	DI, $0xf8
	JA	di_high
	MOVQ	(DI), DI
	JMP	di_finish
di_high:
	MOVQ	-8(DI)(BX*1), DI
	SHRQ	CX, DI
di_finish:

	SUBQ	SI, DI
	SHLQ	CX, DI
equal:
	SETEQ	(AX)
	RET


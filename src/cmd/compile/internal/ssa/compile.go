// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"bytes"
	"cmd/internal/objabi"
	"cmd/internal/src"
	"fmt"
	"hash/crc32"
	"log"
	"math/rand"
	"os"
	"regexp"
	"runtime"
	"sort"
	"strings"
	"time"
)

// Compile is the main entry point for this package.
// Compile modifies f so that on return:
//   · all Values in f map to 0 or 1 assembly instructions of the target architecture
//   · the order of f.Blocks is the order to emit the Blocks
//   · the order of b.Values is the order to emit the Values in each Block
//   · f has a non-nil regAlloc field
func Compile(f *Func) {
	// TODO: debugging - set flags to control verbosity of compiler,
	// which phases to dump IR before/after, etc.
	if f.Log() {
		f.Logf("compiling %s\n", f.Name)
	}

	var rnd *rand.Rand
	if checkEnabled {
		seed := int64(crc32.ChecksumIEEE(([]byte)(f.Name))) ^ int64(checkRandSeed)
		rnd = rand.New(rand.NewSource(seed))
	}

	// hook to print function & phase if panic happens
	phaseName := "init"
	defer func() {
		if phaseName != "" {
			err := recover()
			stack := make([]byte, 16384)
			n := runtime.Stack(stack, false)
			stack = stack[:n]
			f.Fatalf("panic during %s while compiling %s:\n\n%v\n\n%s\n", phaseName, f.Name, err, stack)
		}
	}()

	// Run all the passes
	if f.Log() {
		printFunc(f)
	}
	f.HTMLWriter.WritePhase("start", "start")
	if BuildDump != "" && BuildDump == f.Name {
		f.dumpFile("build")
	}
	if checkEnabled {
		checkFunc(f)
	}
	const logMemStats = false
	for _, p := range passes {
		if !f.Config.optimize && !p.required || p.disabled {
			continue
		}
		f.pass = &p
		phaseName = p.name
		if f.Log() {
			f.Logf("  pass %s begin\n", p.name)
		}
		// TODO: capture logging during this pass, add it to the HTML
		var mStart runtime.MemStats
		if logMemStats || p.mem {
			runtime.ReadMemStats(&mStart)
		}

		if checkEnabled && !f.scheduled {
			// Test that we don't depend on the value order, by randomizing
			// the order of values in each block. See issue 18169.
			for _, b := range f.Blocks {
				for i := 0; i < len(b.Values)-1; i++ {
					j := i + rnd.Intn(len(b.Values)-i)
					b.Values[i], b.Values[j] = b.Values[j], b.Values[i]
				}
			}
		}

		tStart := time.Now()
		p.fn(f) // 调用passes中的函数校验f
		tEnd := time.Now()

		// Need something less crude than "Log the whole intermediate result".
		if f.Log() || f.HTMLWriter != nil {
			time := tEnd.Sub(tStart).Nanoseconds()
			var stats string
			if logMemStats {
				var mEnd runtime.MemStats
				runtime.ReadMemStats(&mEnd)
				nBytes := mEnd.TotalAlloc - mStart.TotalAlloc
				nAllocs := mEnd.Mallocs - mStart.Mallocs
				stats = fmt.Sprintf("[%d ns %d allocs %d bytes]", time, nAllocs, nBytes)
			} else {
				stats = fmt.Sprintf("[%d ns]", time)
			}

			if f.Log() {
				f.Logf("  pass %s end %s\n", p.name, stats)
				printFunc(f)
			}
			f.HTMLWriter.WritePhase(phaseName, fmt.Sprintf("%s <span class=\"stats\">%s</span>", phaseName, stats))
		}
		if p.time || p.mem {
			// Surround timing information w/ enough context to allow comparisons.
			time := tEnd.Sub(tStart).Nanoseconds()
			if p.time {
				f.LogStat("TIME(ns)", time)
			}
			if p.mem {
				var mEnd runtime.MemStats
				runtime.ReadMemStats(&mEnd)
				nBytes := mEnd.TotalAlloc - mStart.TotalAlloc
				nAllocs := mEnd.Mallocs - mStart.Mallocs
				f.LogStat("TIME(ns):BYTES:ALLOCS", time, nBytes, nAllocs)
			}
		}
		if p.dump != nil && p.dump[f.Name] {
			// Dump function to appropriately named file
			f.dumpFile(phaseName)
		}
		if checkEnabled {
			checkFunc(f)
		}
	}

	if f.HTMLWriter != nil {
		// Ensure we write any pending phases to the html
		f.HTMLWriter.flushPhases()
	}

	if f.ruleMatches != nil {
		var keys []string
		for key := range f.ruleMatches {
			keys = append(keys, key)
		}
		sort.Strings(keys)
		buf := new(bytes.Buffer)
		fmt.Fprintf(buf, "%s: ", f.Name)
		for _, key := range keys {
			fmt.Fprintf(buf, "%s=%d ", key, f.ruleMatches[key])
		}
		fmt.Fprint(buf, "\n")
		fmt.Print(buf.String())
	}

	// Squash error printing defer
	phaseName = ""
}

// TODO: should be a config field
var dumpFileSeq int

// dumpFile creates a file from the phase name and function name
// Dumping is done to files to avoid buffering huge strings before
// output.
func (f *Func) dumpFile(phaseName string) {
	dumpFileSeq++
	fname := fmt.Sprintf("%s_%02d__%s.dump", f.Name, dumpFileSeq, phaseName)
	fname = strings.Replace(fname, " ", "_", -1)
	fname = strings.Replace(fname, "/", "_", -1)
	fname = strings.Replace(fname, ":", "_", -1)

	fi, err := os.Create(fname)
	if err != nil {
		f.Warnl(src.NoXPos, "Unable to create after-phase dump file %s", fname)
		return
	}

	p := stringFuncPrinter{w: fi}
	fprintFunc(p, f)
	fi.Close()
}

type pass struct {
	name     string
	fn       func(*Func)
	required bool            // 需要pass
	disabled bool            // 禁止pass
	time     bool            // report time to run pass
	mem      bool            // report mem stats to run pass
	stats    int             // pass reports own "stats" (e.g., branches removed)
	debug    int             // pass performs some debugging. =1 should be in error-testing-friendly Warnl format.
	test     int             // pass-specific ad-hoc option, perhaps useful in development
	dump     map[string]bool // dump if function name matches
}

func (p *pass) addDump(s string) {
	if p.dump == nil {
		p.dump = make(map[string]bool)
	}
	p.dump[s] = true
}

// Run consistency checker between each phase
var (
	checkEnabled  = false
	checkRandSeed = 0
)

// Debug output
var IntrinsicsDebug int
var IntrinsicsDisable bool

var BuildDebug int
var BuildTest int
var BuildStats int
var BuildDump string // name of function to dump after initial build of ssa

// PhaseOption sets the specified flag in the specified ssa phase,
// returning empty string if this was successful or a string explaining
// the error if it was not.
// A version of the phase name with "_" replaced by " " is also checked for a match.
// If the phase name begins a '~' then the rest of the underscores-replaced-with-blanks
// version is used as a regular expression to match the phase name(s).
//
// Special cases that have turned out to be useful:
//  ssa/check/on enables checking after each phase
//  ssa/all/time enables time reporting for all phases
//
// See gc/lex.go for dissection of the option string.
// Example uses:
//
// GO_GCFLAGS=-d=ssa/generic_cse/time,ssa/generic_cse/stats,ssa/generic_cse/debug=3 ./make.bash
//
// BOOT_GO_GCFLAGS=-d='ssa/~^.*scc$/off' GO_GCFLAGS='-d=ssa/~^.*scc$/off' ./make.bash
//
func PhaseOption(phase, flag string, val int, valString string) string {
	switch phase {
	case "", "help":
		lastcr := 0
		phasenames := "    check, all, build, intrinsics"
		for _, p := range passes {
			pn := strings.Replace(p.name, " ", "_", -1)
			if len(pn)+len(phasenames)-lastcr > 70 {
				phasenames += "\n    "
				lastcr = len(phasenames)
				phasenames += pn
			} else {
				phasenames += ", " + pn
			}
		}
		return `PhaseOptions usage:

    go tool compile -d=ssa/<phase>/<flag>[=<value>|<function_name>]

where:

- <phase> is one of:
` + phasenames + `

- <flag> is one of:
    on, off, debug, mem, time, test, stats, dump, seed

- <value> defaults to 1

- <function_name> is required for the "dump" flag, and specifies the
  name of function to dump after <phase>

Phase "all" supports flags "time", "mem", and "dump".
Phase "intrinsics" supports flags "on", "off", and "debug".

If the "dump" flag is specified, the output is written on a file named
<phase>__<function_name>_<seq>.dump; otherwise it is directed to stdout.

Examples:

    -d=ssa/check/on
enables checking after each phase

	-d=ssa/check/seed=1234
enables checking after each phase, using 1234 to seed the PRNG
used for value order randomization

    -d=ssa/all/time
enables time reporting for all phases

    -d=ssa/prove/debug=2
sets debugging level to 2 in the prove pass

Multiple flags can be passed at once, by separating them with
commas. For example:

    -d=ssa/check/on,ssa/all/time
`
	}

	if phase == "check" && flag == "on" {
		checkEnabled = val != 0
		debugPoset = checkEnabled // also turn on advanced self-checking in prove's datastructure
		return ""
	}
	if phase == "check" && flag == "off" {
		checkEnabled = val == 0
		debugPoset = checkEnabled
		return ""
	}
	if phase == "check" && flag == "seed" {
		checkEnabled = true
		checkRandSeed = val
		debugPoset = checkEnabled
		return ""
	}

	alltime := false
	allmem := false
	alldump := false
	if phase == "all" {
		if flag == "time" {
			alltime = val != 0
		} else if flag == "mem" {
			allmem = val != 0
		} else if flag == "dump" {
			alldump = val != 0
			if alldump {
				BuildDump = valString
			}
		} else {
			return fmt.Sprintf("Did not find a flag matching %s in -d=ssa/%s debug option", flag, phase)
		}
	}

	if phase == "intrinsics" {
		switch flag {
		case "on":
			IntrinsicsDisable = val == 0
		case "off":
			IntrinsicsDisable = val != 0
		case "debug":
			IntrinsicsDebug = val
		default:
			return fmt.Sprintf("Did not find a flag matching %s in -d=ssa/%s debug option", flag, phase)
		}
		return ""
	}
	if phase == "build" {
		switch flag {
		case "debug":
			BuildDebug = val
		case "test":
			BuildTest = val
		case "stats":
			BuildStats = val
		case "dump":
			BuildDump = valString
		default:
			return fmt.Sprintf("Did not find a flag matching %s in -d=ssa/%s debug option", flag, phase)
		}
		return ""
	}

	underphase := strings.Replace(phase, "_", " ", -1)
	var re *regexp.Regexp
	if phase[0] == '~' {
		r, ok := regexp.Compile(underphase[1:])
		if ok != nil {
			return fmt.Sprintf("Error %s in regexp for phase %s, flag %s", ok.Error(), phase, flag)
		}
		re = r
	}
	matchedOne := false
	for i, p := range passes {
		if phase == "all" {
			p.time = alltime
			p.mem = allmem
			if alldump {
				p.addDump(valString)
			}
			passes[i] = p
			matchedOne = true
		} else if p.name == phase || p.name == underphase || re != nil && re.MatchString(p.name) {
			switch flag {
			case "on":
				p.disabled = val == 0
			case "off":
				p.disabled = val != 0
			case "time":
				p.time = val != 0
			case "mem":
				p.mem = val != 0
			case "debug":
				p.debug = val
			case "stats":
				p.stats = val
			case "test":
				p.test = val
			case "dump":
				p.addDump(valString)
			default:
				return fmt.Sprintf("Did not find a flag matching %s in -d=ssa/%s debug option", flag, phase)
			}
			if p.disabled && p.required {
				return fmt.Sprintf("Cannot disable required SSA phase %s using -d=ssa/%s debug option", phase, phase)
			}
			passes[i] = p
			matchedOne = true
		}
	}
	if matchedOne {
		return ""
	}
	return fmt.Sprintf("Did not find a phase matching %s in -d=ssa/... debug option", phase)
}

// list of passes for the compiler
var passes = [...]pass{
	// TODO: combine phielim and copyelim into a single pass?
	{name: "number lines", fn: numberLines, required: true},
	{name: "early phielim", fn: phielim},   // 将所有的参数中仅有一个不是引用自身的phi替换为OpCopy
	{name: "early copyelim", fn: copyelim}, // 将拷贝操作直接用拷贝的参数进行替换
	{name: "early deadcode", fn: deadcode}, // remove generated dead code to avoid doing pointless work during opt
	// 对于类型为布尔的phi函数,可以从其前驱知道这个phi函数是true还是false,将对应的参数替换为布尔常量并进行块优化
	{name: "short circuit", fn: shortcircuit},
	// 对Op为OpArg的Value进行重写
	{name: "decompose args", fn: decomposeArgs, required: true},
	// 对于phi函数中类型为结构体或者数组的情况,将其替换为结构体中多个phi的情况以及数组中多个phi的情况
	{name: "decompose user", fn: decomposeUser, required: true},
	{name: "pre-opt deadcode", fn: deadcode},
	{name: "opt", fn: opt, required: true}, // NB: some generic rules know the name of the opt pass. TODO: split required rules and optimizing rules
	// 对于不需要参数的Op,提取该value并放到entry块中,并将其他块中具有相同的Op, AuxInt, Aux, Type的value替换为该value
	{name: "zero arg cse", fn: zcse, required: true},     // required to merge OpSB values
	{name: "opt deadcode", fn: deadcode, required: true}, // remove any blocks orphaned during opt
	// 筛选出Op,Aux,AuxInt,参数数量,类型,相同块中的phi以及相同的参数,这些都相同的value视为一组,这一组中用支配力最高的value分别替换掉被支配的value
	{name: "generic cse", fn: cse},
	/*
		if块后面的布尔类型的phi函数优化
		 Replaces
			if a { x = true } else { x = false } with x = a
			if a { x = false } else { x = true } with x = !a
			if a { x = true } else { x = value } with x = a || value
			if a { x = value } else { x = false } with x = a && value
	*/
	{name: "phiopt", fn: phiopt},
	{name: "gcse deadcode", fn: deadcode, required: true}, // clean out after cse and phiopt
	/*
		遍历所有的phi函数,如果这个phi函数的所有参数都不为nil,那么这个phi函数也不为nil
		对于 if ptr != nil {
					// A块
					// do something
				} 这样的代码,可知如果进了A块,那么ptr一定不为nil
		通过深度优先遍历的方式遍历支配树上的所有节点,对无用的nil检查删除
	*/
	{name: "nilcheckelim", fn: nilcheckelim},
	{name: "prove", fn: prove},
	/*
		1. 如果一个块c只有一个前驱块b且b是基本块,那么将b合并到c
		2. 如果一个块b只有一个前驱块p且b与p都是if块,那么尝试合并b与p的控制语句到b并将p设置为基本块(删掉一条p的后继边)
	*/
	{name: "early fuse", fn: fuseEarly},
	// 将复杂类型的phi拆分重写为简单类型的phi
	// 将复杂类型重写为简单的类型
	// 如果程序是32位,将64位的操作拆解为32位的等价操作
	// 将栈槽切分为小的栈槽
	{name: "decompose builtin", fn: decomposeBuiltIn, required: true},
	// 软件实现float类型
	{name: "softfloat", fn: softfloat, required: true},
	// 优化if块中的控制Value
	// 用于重写特定Value进行运算优化
	{name: "late opt", fn: opt, required: true},              // TODO: split required rules and optimizing rules
	{name: "dead auto elim", fn: elimDeadAutosGeneric},       // 消除对于之后没有使用的局部变量的存储操作
	{name: "generic deadcode", fn: deadcode, required: true}, // remove dead stores, which otherwise mess up store chain
	{name: "check bce", fn: checkbce},                        // 激活相应的调试选项时会打印所有的边界检查,一般为false
	// bb0            bb0
	//  | \          /   \
	//  | bb1  or  bb1   bb2    <- trivial if/else blocks
	//  | /          \   /
	// bb2            bb3
	// 如果if或者if-else语句中的分支块内容较少(指令少),尝试将所有块的values归纳到bb0块中
	{name: "branchelim", fn: branchelim},
	// 如果一个块c只有一个前驱块b且b是基本块,那么将b合并到c;清除掉无用的if块
	{name: "late fuse", fn: fuseLate},
	// 在一个块中如果有连续的存储或者清零操作(中间不含读取内存的操作),且本次操作的内存字节数小于下一次内存操作的字节数(表示本次操作会被下一次的操作覆盖),直接将本次的内存状态设置为上一次的内存状态的拷贝
	{name: "dse", fn: dse},
	{name: "writebarrier", fn: writebarrier, required: true}, // expand write barrier ops	// 添加写屏障相关的代码,跳过了,记得再看
	/*
		有些块没有定义mem value,为这样的块添加phi mem value并传递给之后的块(如果后继块本身也没有定义mem value的话)
		添加检查,如果栈顶指针超过了g.limit,重新调度g
	*/
	{name: "insert resched checks", fn: insertLoopReschedChecks,
		disabled: objabi.Preemptibleloops_enabled == 0}, // insert resched checks in loops.		objabi.Preemptibleloops_enabled默认为0,这个优化一般不会运行
	{name: "lower", fn: lower, required: true},                                   // convert to machine-dependent ops		很大的函数,将各种Op转为依赖于机器的Op
	{name: "addressing modes", fn: addressingModes, required: false},             // 将多次的地址计算结合为一个复杂的指令中
	{name: "lowered deadcode for cse", fn: deadcode},                             // deadcode immediately before CSE avoids CSE making dead values live again
	{name: "lowered cse", fn: cse},                                               // 筛选出Op,Aux,AuxInt,参数数量,类型,相同块中的phi以及相同的参数,这些都相同的value视为一组,这一组中用支配力最高的value分别替换掉被支配的value
	{name: "elim unread autos", fn: elimUnreadAutos},                             // 删掉没有取地址或者读操作的对局部栈存储的变量
	{name: "tighten tuple selectors", fn: tightenTupleSelectors, required: true}, // Select0 and Select1 ops	保证对tuple的操作都与tuple在同一个块中且相同的取值操作只进行一次
	{name: "lowered deadcode", fn: deadcode, required: true},
	{name: "checkLower", fn: checkLower, required: true}, // checks for unlowered opcodes and fails if we find one.
	{name: "late phielim", fn: phielim},                  // 将所有的参数中仅有一个不是引用自身的phi替换为OpCopy
	{name: "late copyelim", fn: copyelim},                // 将拷贝操作直接用拷贝的参数进行替换
	{name: "tighten", fn: tighten},                       // move values closer to their uses		移动一些values到它们最早被使用的块,这是为了减轻寄存器分配的压力
	{name: "late deadcode", fn: deadcode},
	/*
		 v1   v1  v2
		   \  |  /
		phi(v1, v1, v2)
		改为:
		  v1  v1    v2
		   \  |     /
		    b1     b2
		     \     /
		   phi(v1, v2)
		其中b1与b2都是新创建的基本块
	*/
	{name: "critical", fn: critical, required: true}, // remove critical edges
	// 在phi函数的前驱块放上一个对应的参数的拷贝,保证phi的参数都是在直接前驱块定义的
	{name: "phi tighten", fn: phiTighten},    // place rematerializable phi args near uses to reduce value lifetimes
	{name: "likelyadjust", fn: likelyadjust}, // 看不明白打算做什么
	/*
		将所有的块进行排序
		1.一旦进入了某个块那么程序必然会exit,整理出这些块放到exit切片中
		2.对于剩余的块,记录其入度,也就是前驱的数量保存到indegree切片中,并且记录入度为0与入度不为0的块分别保存到zerodegree与posdegree中
		3.从entry块开始处理,被处理块加入order切片,被处理块的后继入度分别减一,如果此时后继块入度为0,将该块从posdegree放到zerodegree中,之后的调度优先级顺序如下:
			1.通过被处理块的静态分支预测找到未被处理的后继块进行调度
			2.后继中未被调度且块类型不是BlockExit的拥有最小入度的块
			3.如果zerodegree中存在入度为0的块,弹出一项,若弹出的这一个块未被调度,那么这个块就是下一个被调度的块
			4.如果posdegree中存在入度大于0的块,弹出一项,若弹出的这一个块未被调度,那么这个块就是下一个被调度的块
			5.从exit中弹出一项,若未被调度,那么这个块就是下一个被调度的块
	*/
	{name: "layout", fn: layout, required: true},       // schedule blocks
	/*
	会将每个块中的每个value按如下优先级进行排序
		评定的score较大的在后面
		源码位置不相等时后出现的在后面
		对于不是phi的value,两个value参数少的在后面
		被使用次数少的在后面
		AuxInt大的在后面
		通过类型比较,大的在后面
		Id大的在后面
	进行排序的value必须满足的一点是:这个value不再被未被调度过的所有value所使用
	*/
	{name: "schedule", fn: schedule, required: true},   // schedule values	将所有块中的Value进行排序
	{name: "late nilcheck", fn: nilcheckelim2},         // 通过一些指针为nil就会主动报错的操作来消除对这些指针的nilcheck
	{name: "flagalloc", fn: flagalloc, required: true}, // allocate flags register		通过跟踪flag清除无用的flag类型的value
	{name: "regalloc", fn: regalloc, required: true},   // allocate int & float registers + stack slots
	//   loop:
	//     CMPQ ...
	//     JGE exit
	//     ...
	//     JMP loop
	//   exit:
	//
	// 变成
	//    JMP entry
	//  loop:
	//    ...
	//  entry:
	//    CMPQ ...
	//    JLT loop
	// 主要通过改变块的顺序实现
	{name: "loop rotate", fn: loopRotate},                // 将循环头部进行的跳转判断转换为在尾部进行判断并跳转的语句
	{name: "stackframe", fn: stackframe, required: true}, // 计算出当前函数的栈帧大小以及当前栈帧前多少字节中包含指针
	// 将为空(或者只有phi)的基本块合并到它的唯一后继中
	{name: "trim", fn: trim},                             // remove empty blocks
}

// Double-check phase ordering constraints.
// This code is intended to document the ordering requirements
// between different phases. It does not override the passes
// list above.
type constraint struct {
	a, b string // a must come before b
}

var passOrder = [...]constraint{
	// "insert resched checks" uses mem, better to clean out stores first.
	{"dse", "insert resched checks"},
	// insert resched checks adds new blocks containing generic instructions
	{"insert resched checks", "lower"},
	{"insert resched checks", "tighten"},

	// prove relies on common-subexpression elimination for maximum benefits.
	{"generic cse", "prove"},
	// deadcode after prove to eliminate all new dead blocks.
	{"prove", "generic deadcode"},
	// common-subexpression before dead-store elim, so that we recognize
	// when two address expressions are the same.
	{"generic cse", "dse"},
	// cse substantially improves nilcheckelim efficacy
	{"generic cse", "nilcheckelim"},
	// allow deadcode to clean up after nilcheckelim
	{"nilcheckelim", "generic deadcode"},
	// nilcheckelim generates sequences of plain basic blocks
	{"nilcheckelim", "late fuse"},
	// nilcheckelim relies on opt to rewrite user nil checks
	{"opt", "nilcheckelim"},
	// tighten will be most effective when as many values have been removed as possible
	{"generic deadcode", "tighten"},
	{"generic cse", "tighten"},
	// checkbce needs the values removed
	{"generic deadcode", "check bce"},
	// don't run optimization pass until we've decomposed builtin objects
	{"decompose builtin", "late opt"},
	// decompose builtin is the last pass that may introduce new float ops, so run softfloat after it
	{"decompose builtin", "softfloat"},
	// tuple selectors must be tightened to generators and de-duplicated before scheduling
	{"tighten tuple selectors", "schedule"},
	// remove critical edges before phi tighten, so that phi args get better placement
	{"critical", "phi tighten"},
	// don't layout blocks until critical edges have been removed
	{"critical", "layout"},
	// regalloc requires the removal of all critical edges
	{"critical", "regalloc"},
	// regalloc requires all the values in a block to be scheduled
	{"schedule", "regalloc"},
	// checkLower must run after lowering & subsequent dead code elim
	{"lower", "checkLower"},
	{"lowered deadcode", "checkLower"},
	// late nilcheck needs instructions to be scheduled.
	{"schedule", "late nilcheck"},
	// flagalloc needs instructions to be scheduled.
	{"schedule", "flagalloc"},
	// regalloc needs flags to be allocated first.
	{"flagalloc", "regalloc"},
	// loopRotate will confuse regalloc.
	{"regalloc", "loop rotate"},
	// stackframe needs to know about spilled registers.
	{"regalloc", "stackframe"},
	// trim needs regalloc to be done first.
	{"regalloc", "trim"},
}

func init() {
	for _, c := range passOrder {
		a, b := c.a, c.b
		i := -1
		j := -1
		for k, p := range passes {
			if p.name == a {
				i = k
			}
			if p.name == b {
				j = k
			}
		}
		if i < 0 {
			log.Panicf("pass %s not found", a)
		}
		if j < 0 {
			log.Panicf("pass %s not found", b)
		}
		if i >= j {
			log.Panicf("passes %s and %s out of order", a, b)
		}
	}
}

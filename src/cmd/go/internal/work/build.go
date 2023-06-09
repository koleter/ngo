// Copyright 2011 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package work

import (
	"errors"
	"fmt"
	"go/build"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"

	"cmd/go/internal/base"
	"cmd/go/internal/cfg"
	"cmd/go/internal/load"
	"cmd/go/internal/search"
)

var CmdBuild = &base.Command{
	UsageLine: "go build [-o output] [-i] [build flags] [packages]",
	Short:     "compile packages and dependencies",
	Long: `
Build compiles the packages named by the import paths,
along with their dependencies, but it does not install the results.

If the arguments to build are a list of .go files from a single directory,
build treats them as a list of source files specifying a single package.

When compiling packages, build ignores files that end in '_test.go'.

When compiling a single main package, build writes
the resulting executable to an output file named after
the first source file ('go build ed.go rx.go' writes 'ed' or 'ed.exe')
or the source code directory ('go build unix/sam' writes 'sam' or 'sam.exe').
The '.exe' suffix is added when writing a Windows executable.

When compiling multiple packages or a single non-main package,
build compiles the packages but discards the resulting object,
serving only as a check that the packages can be built.

The -o flag forces build to write the resulting executable or object
to the named output file or directory, instead of the default behavior described
in the last two paragraphs. If the named output is a directory that exists,
then any resulting executables will be written to that directory.

The -i flag installs the packages that are dependencies of the target.

The build flags are shared by the build, clean, get, install, list, run,
and test commands:

	-a
		force rebuilding of packages that are already up-to-date.
	-n
		print the commands but do not run them.
	-p n
		the number of programs, such as build commands or
		test binaries, that can be run in parallel.
		The default is the number of CPUs available.
	-race
		enable data race detection.
		Supported only on linux/amd64, freebsd/amd64, darwin/amd64, windows/amd64,
		linux/ppc64le and linux/arm64 (only for 48-bit VMA).
	-msan
		enable interoperation with memory sanitizer.
		Supported only on linux/amd64, linux/arm64
		and only with Clang/LLVM as the host C compiler.
		On linux/arm64, pie build mode will be used.
	-v
		print the names of packages as they are compiled.
	-work
		print the name of the temporary work directory and
		do not delete it when exiting.
	-x
		print the commands.

	-asmflags '[pattern=]arg list'
		arguments to pass on each go tool asm invocation.
	-buildmode mode
		build mode to use. See 'go help buildmode' for more.
	-compiler name
		name of compiler to use, as in runtime.Compiler (gccgo or gc).
	-gccgoflags '[pattern=]arg list'
		arguments to pass on each gccgo compiler/linker invocation.
	-gcflags '[pattern=]arg list'
		arguments to pass on each go tool compile invocation.
	-installsuffix suffix
		a suffix to use in the name of the package installation directory,
		in order to keep output separate from default builds.
		If using the -race flag, the install suffix is automatically set to race
		or, if set explicitly, has _race appended to it. Likewise for the -msan
		flag. Using a -buildmode option that requires non-default compile flags
		has a similar effect.
	-ldflags '[pattern=]arg list'
		arguments to pass on each go tool link invocation.
	-linkshared
		build code that will be linked against shared libraries previously
		created with -buildmode=shared.
	-mod mode
		module download mode to use: readonly, vendor, or mod.
		See 'go help modules' for more.
	-modcacherw
		leave newly-created directories in the module cache read-write
		instead of making them read-only.
	-modfile file
		in module aware mode, read (and possibly write) an alternate go.mod
		file instead of the one in the module root directory. A file named
		"go.mod" must still be present in order to determine the module root
		directory, but it is not accessed. When -modfile is specified, an
		alternate go.sum file is also used: its path is derived from the
		-modfile flag by trimming the ".mod" extension and appending ".sum".
	-pkgdir dir
		install and load all packages from dir instead of the usual locations.
		For example, when building with a non-standard configuration,
		use -pkgdir to keep generated packages in a separate location.
	-tags tag,list
		a comma-separated list of build tags to consider satisfied during the
		build. For more information about build tags, see the description of
		build constraints in the documentation for the go/build package.
		(Earlier versions of Go used a space-separated list, and that form
		is deprecated but still recognized.)
	-trimpath
		remove all file system paths from the resulting executable.
		Instead of absolute file system paths, the recorded file names
		will begin with either "go" (for the standard library),
		or a module path@version (when using modules),
		or a plain import path (when using GOPATH).
	-toolexec 'cmd args'
		a program to use to invoke toolchain programs like vet and asm.
		For example, instead of running asm, the go command will run
		'cmd args /path/to/asm <arguments for asm>'.

The -asmflags, -gccgoflags, -gcflags, and -ldflags flags accept a
space-separated list of arguments to pass to an underlying tool
during the build. To embed spaces in an element in the list, surround
it with either single or double quotes. The argument list may be
preceded by a package pattern and an equal sign, which restricts
the use of that argument list to the building of packages matching
that pattern (see 'go help packages' for a description of package
patterns). Without a pattern, the argument list applies only to the
packages named on the command line. The flags may be repeated
with different patterns in order to specify different arguments for
different sets of packages. If a package matches patterns given in
multiple flags, the latest match on the command line wins.
For example, 'go build -gcflags=-S fmt' prints the disassembly
only for package fmt, while 'go build -gcflags=all=-S fmt'
prints the disassembly for fmt and all its dependencies.

For more about specifying packages, see 'go help packages'.
For more about where packages and binaries are installed,
run 'go help gopath'.
For more about calling between Go and C/C++, run 'go help c'.

Note: Build adheres to certain conventions such as those described
by 'go help gopath'. Not all projects can follow these conventions,
however. Installations that have their own conventions or that use
a separate software build system may choose to use lower-level
invocations such as 'go tool compile' and 'go tool link' to avoid
some of the overheads and design decisions of the build tool.

See also: go install, go get, go clean.
	`,
}

const concurrentGCBackendCompilationEnabledByDefault = true

func init() {
	// break init cycle
	CmdBuild.Run = runBuild
	CmdInstall.Run = runInstall

	CmdBuild.Flag.BoolVar(&cfg.BuildI, "i", false, "")
	CmdBuild.Flag.StringVar(&cfg.BuildO, "o", "", "output file or directory")

	CmdInstall.Flag.BoolVar(&cfg.BuildI, "i", false, "")

	AddBuildFlags(CmdBuild, DefaultBuildFlags)
	AddBuildFlags(CmdInstall, DefaultBuildFlags)
}

// Note that flags consulted by other parts of the code
// (for example, buildV) are in cmd/go/internal/cfg.

var (
	forcedAsmflags   []string // internally-forced flags for cmd/asm
	forcedGcflags    []string // internally-forced flags for cmd/compile
	forcedLdflags    []string // internally-forced flags for cmd/link
	forcedGccgoflags []string // internally-forced flags for gccgo
)

var BuildToolchain toolchain = noToolchain{}
var ldBuildmode string

// buildCompiler implements flag.Var.
// It implements Set by updating both
// BuildToolchain and buildContext.Compiler.
type buildCompiler struct{}

func (c buildCompiler) Set(value string) error {
	switch value {
	case "gc":
		BuildToolchain = gcToolchain{}
	case "gccgo":
		BuildToolchain = gccgoToolchain{}
	default:
		return fmt.Errorf("unknown compiler %q", value)
	}
	cfg.BuildToolchainName = value
	cfg.BuildToolchainCompiler = BuildToolchain.compiler
	cfg.BuildToolchainLinker = BuildToolchain.linker
	cfg.BuildContext.Compiler = value
	return nil
}

func (c buildCompiler) String() string {
	return cfg.BuildContext.Compiler
}

func init() {
	switch build.Default.Compiler {
	case "gc", "gccgo":
		buildCompiler{}.Set(build.Default.Compiler)
	}
}

type BuildFlagMask int

const (
	DefaultBuildFlags BuildFlagMask = 0
	OmitModFlag       BuildFlagMask = 1 << iota
	OmitModCommonFlags
	OmitVFlag
)

// AddBuildFlags adds the flags common to the build, clean, get,
// install, list, run, and test commands.
func AddBuildFlags(cmd *base.Command, mask BuildFlagMask) {
	cmd.Flag.BoolVar(&cfg.BuildA, "a", false, "")
	cmd.Flag.BoolVar(&cfg.BuildN, "n", false, "")
	cmd.Flag.IntVar(&cfg.BuildP, "p", cfg.BuildP, "")
	if mask&OmitVFlag == 0 {
		cmd.Flag.BoolVar(&cfg.BuildV, "v", false, "")
	}
	cmd.Flag.BoolVar(&cfg.BuildX, "x", false, "")

	cmd.Flag.Var(&load.BuildAsmflags, "asmflags", "")
	cmd.Flag.Var(buildCompiler{}, "compiler", "")
	cmd.Flag.StringVar(&cfg.BuildBuildmode, "buildmode", "default", "")
	cmd.Flag.Var(&load.BuildGcflags, "gcflags", "")
	cmd.Flag.Var(&load.BuildGccgoflags, "gccgoflags", "")
	if mask&OmitModFlag == 0 {
		cmd.Flag.StringVar(&cfg.BuildMod, "mod", "", "")
	}
	if mask&OmitModCommonFlags == 0 {
		AddModCommonFlags(cmd)
	}
	cmd.Flag.StringVar(&cfg.BuildContext.InstallSuffix, "installsuffix", "", "")
	cmd.Flag.Var(&load.BuildLdflags, "ldflags", "")
	cmd.Flag.BoolVar(&cfg.BuildLinkshared, "linkshared", false, "")
	cmd.Flag.StringVar(&cfg.BuildPkgdir, "pkgdir", "", "")
	cmd.Flag.BoolVar(&cfg.BuildRace, "race", false, "")
	cmd.Flag.BoolVar(&cfg.BuildMSan, "msan", false, "")
	cmd.Flag.Var((*tagsFlag)(&cfg.BuildContext.BuildTags), "tags", "")
	cmd.Flag.Var((*base.StringsFlag)(&cfg.BuildToolexec), "toolexec", "")
	cmd.Flag.BoolVar(&cfg.BuildTrimpath, "trimpath", false, "")
	cmd.Flag.BoolVar(&cfg.BuildWork, "work", false, "")

	// Undocumented, unstable debugging flags.
	cmd.Flag.StringVar(&cfg.DebugActiongraph, "debug-actiongraph", "", "")
}

// AddModCommonFlags adds the module-related flags common to build commands
// and 'go mod' subcommands.
func AddModCommonFlags(cmd *base.Command) {
	cmd.Flag.BoolVar(&cfg.ModCacheRW, "modcacherw", false, "")
	cmd.Flag.StringVar(&cfg.ModFile, "modfile", "", "")
}

// tagsFlag is the implementation of the -tags flag.
type tagsFlag []string

func (v *tagsFlag) Set(s string) error {
	// For compatibility with Go 1.12 and earlier, allow "-tags='a b c'" or even just "-tags='a'".
	if strings.Contains(s, " ") || strings.Contains(s, "'") {
		return (*base.StringsFlag)(v).Set(s)
	}

	// Split on commas, ignore empty strings.
	*v = []string{}
	for _, s := range strings.Split(s, ",") {
		if s != "" {
			*v = append(*v, s)
		}
	}
	return nil
}

func (v *tagsFlag) String() string {
	return "<TagsFlag>"
}

// fileExtSplit expects a filename and returns the name
// and ext (without the dot). If the file has no
// extension, ext will be empty.
func fileExtSplit(file string) (name, ext string) {
	dotExt := filepath.Ext(file)
	name = file[:len(file)-len(dotExt)]
	if dotExt != "" {
		ext = dotExt[1:]
	}
	return
}

func pkgsMain(pkgs []*load.Package) (res []*load.Package) {
	for _, p := range pkgs {
		if p.Name == "main" {
			res = append(res, p)
		}
	}
	return res
}

func pkgsNotMain(pkgs []*load.Package) (res []*load.Package) {
	for _, p := range pkgs {
		if p.Name != "main" {
			res = append(res, p)
		}
	}
	return res
}

func oneMainPkg(pkgs []*load.Package) []*load.Package {
	if len(pkgs) != 1 || pkgs[0].Name != "main" {
		base.Fatalf("-buildmode=%s requires exactly one main package", cfg.BuildBuildmode)
	}
	return pkgs
}

var pkgsFilter = func(pkgs []*load.Package) []*load.Package { return pkgs }

var runtimeVersion = runtime.Version()

func runBuild(cmd *base.Command, args []string) {
	BuildInit() //对mod、instrument、buildMode进行初始化及检查，最后对输出编译包的路径进行检查。
	var b Builder
	b.Init() //对于编译缓存参数的初始化，对工作目录、GOOS-ARCH及tag进行检查。

	pkgs := load.PackagesForBuild(args) //检查并包装所有的package,这里返回的pkgs仅仅包含go build编译的那个main包，若有错误则不能编译

	explicitO := len(cfg.BuildO) > 0 //通过-o flag指定了输出路径

	if len(pkgs) == 1 && pkgs[0].Name == "main" && cfg.BuildO == "" { // 编译的是main包且没有指定-o参数,赋予默认输出文件名
		cfg.BuildO = pkgs[0].DefaultExecName() //默认执行文件名
		cfg.BuildO += cfg.ExeSuffix            //执行文件后缀
	}

	// sanity check some often mis-used options
	switch cfg.BuildContext.Compiler { //健全检查一些经常误用的选项
	case "gccgo":
		if load.BuildGcflags.Present() {
			fmt.Println("go build: when using gccgo toolchain, please pass compiler flags using -gccgoflags, not -gcflags")
		}
		if load.BuildLdflags.Present() {
			fmt.Println("go build: when using gccgo toolchain, please pass linker flags using -gccgoflags, not -ldflags")
		}
	case "gc":
		if load.BuildGccgoflags.Present() {
			fmt.Println("go build: when using gc toolchain, please pass compile flags using -gcflags, and linker flags using -ldflags")
		}
	}

	depMode := ModeBuild
	if cfg.BuildI { // -i flag
		depMode = ModeInstall
	}

	pkgs = omitTestOnly(pkgsFilter(load.Packages(args))) //忽略仅测试的package

	// Special case -o /dev/null by not writing at all.
	if cfg.BuildO == os.DevNull { //指针特殊输出路径的处理
		cfg.BuildO = ""
	}

	if cfg.BuildO != "" { //针对输出路径的处理,存在-o参数
		// If the -o name exists and is a directory, then
		// write all main packages to that directory.
		// Otherwise require only a single package be built.
		if fi, err := os.Stat(cfg.BuildO); err == nil && fi.IsDir() { //输出路径已存在且是文件夹
			if !explicitO { // 没有用-o明确指定输出的文件
				base.Fatalf("go build: build output %q already exists and is a directory", cfg.BuildO)
			}
			a := &Action{Mode: "go build"} //指定Action的Mode为build
			for _, p := range pkgs {
				if p.Name != "main" { //build的package需从main package开始
					continue
				}
				//目标packag的参数设置
				p.Target = filepath.Join(cfg.BuildO, p.DefaultExecName())
				p.Target += cfg.ExeSuffix
				p.Stale = true
				p.StaleReason = "build -o flag in use"
				a.Deps = append(a.Deps, b.AutoAction(ModeInstall, depMode, p)) //记录针对所有package的编译操作
			}
			if len(a.Deps) == 0 { //没有main则报错
				base.Fatalf("go build: no main packages to build")
			}
			b.Do(a) //根据action进行操作
			return
		}
		if len(pkgs) > 1 { //编译的包超过了一个
			base.Fatalf("go build: cannot write multiple packages to non-directory %s", cfg.BuildO)
		} else if len(pkgs) == 0 { //没有package
			base.Fatalf("no packages to build")
		}
		p := pkgs[0]
		p.Target = cfg.BuildO
		p.Stale = true // must build - not up to date
		p.StaleReason = "build -o flag in use"
		a := b.AutoAction(ModeInstall, depMode, p)
		b.Do(a)
		return
	}
	// 未通过-o指定输出文件
	a := &Action{Mode: "go build"}
	for _, p := range pkgs {
		a.Deps = append(a.Deps, b.AutoAction(ModeBuild, depMode, p))
	}
	if cfg.BuildBuildmode == "shared" {
		a = b.buildmodeShared(ModeBuild, depMode, args, pkgs, a)
	}
	b.Do(a)
}

var CmdInstall = &base.Command{
	UsageLine: "go install [-i] [build flags] [packages]",
	Short:     "compile and install packages and dependencies",
	Long: `
Install compiles and installs the packages named by the import paths.

Executables are installed in the directory named by the GOBIN environment
variable, which defaults to $GOPATH/bin or $HOME/go/bin if the GOPATH
environment variable is not set. Executables in $GOROOT
are installed in $GOROOT/bin or $GOTOOLDIR instead of $GOBIN.

When module-aware mode is disabled, other packages are installed in the
directory $GOPATH/pkg/$GOOS_$GOARCH. When module-aware mode is enabled,
other packages are built and cached but not installed.

The -i flag installs the dependencies of the named packages as well.

For more about the build flags, see 'go help build'.
For more about specifying packages, see 'go help packages'.

See also: go build, go get, go clean.
	`,
}

// libname returns the filename to use for the shared library when using
// -buildmode=shared. The rules we use are:
// Use arguments for special 'meta' packages:
//	std --> libstd.so
//	std cmd --> libstd,cmd.so
// A single non-meta argument with trailing "/..." is special cased:
//	foo/... --> libfoo.so
//	(A relative path like "./..."  expands the "." first)
// Use import paths for other cases, changing '/' to '-':
//	somelib --> libsubdir-somelib.so
//	./ or ../ --> libsubdir-somelib.so
//	gopkg.in/tomb.v2 -> libgopkg.in-tomb.v2.so
//	a/... b/... ---> liba/c,b/d.so - all matching import paths
// Name parts are joined with ','.
func libname(args []string, pkgs []*load.Package) (string, error) {
	var libname string
	appendName := func(arg string) {
		if libname == "" {
			libname = arg
		} else {
			libname += "," + arg
		}
	}
	var haveNonMeta bool
	for _, arg := range args {
		if search.IsMetaPackage(arg) {
			appendName(arg)
		} else {
			haveNonMeta = true
		}
	}
	if len(libname) == 0 { // non-meta packages only. use import paths
		if len(args) == 1 && strings.HasSuffix(args[0], "/...") {
			// Special case of "foo/..." as mentioned above.
			arg := strings.TrimSuffix(args[0], "/...")
			if build.IsLocalImport(arg) {
				cwd, _ := os.Getwd()
				bp, _ := cfg.BuildContext.ImportDir(filepath.Join(cwd, arg), build.FindOnly)
				if bp.ImportPath != "" && bp.ImportPath != "." {
					arg = bp.ImportPath
				}
			}
			appendName(strings.ReplaceAll(arg, "/", "-"))
		} else {
			for _, pkg := range pkgs {
				appendName(strings.ReplaceAll(pkg.ImportPath, "/", "-"))
			}
		}
	} else if haveNonMeta { // have both meta package and a non-meta one
		return "", errors.New("mixing of meta and non-meta packages is not allowed")
	}
	// TODO(mwhudson): Needs to change for platforms that use different naming
	// conventions...
	return "lib" + libname + ".so", nil
}

func runInstall(cmd *base.Command, args []string) {
	BuildInit()
	InstallPackages(args, load.PackagesForBuild(args))
}

// omitTestOnly returns pkgs with test-only packages removed.
func omitTestOnly(pkgs []*load.Package) []*load.Package {
	var list []*load.Package
	for _, p := range pkgs {
		if len(p.GoFiles)+len(p.CgoFiles) == 0 && !p.Internal.CmdlinePkgLiteral {
			// Package has no source files,
			// perhaps due to build tags or perhaps due to only having *_test.go files.
			// Also, it is only being processed as the result of a wildcard match
			// like ./..., not because it was listed as a literal path on the command line.
			// Ignore it.
			continue
		}
		list = append(list, p)
	}
	return list
}

func InstallPackages(patterns []string, pkgs []*load.Package) {
	if cfg.GOBIN != "" && !filepath.IsAbs(cfg.GOBIN) {
		base.Fatalf("cannot install, GOBIN must be an absolute path")
	}

	pkgs = omitTestOnly(pkgsFilter(pkgs))
	for _, p := range pkgs {
		if p.Target == "" {
			switch {
			case p.Standard && p.ImportPath == "unsafe":
				// unsafe is a built-in package, has no target
			case p.Name != "main" && p.Internal.Local && p.ConflictDir == "":
				// Non-executables outside GOPATH need not have a target:
				// we can use the cache to hold the built package archive for use in future builds.
				// The ones inside GOPATH should have a target (in GOPATH/pkg)
				// or else something is wrong and worth reporting (like a ConflictDir).
			case p.Name != "main" && p.Module != nil:
				// Non-executables have no target (except the cache) when building with modules.
			case p.Internal.GobinSubdir:
				base.Errorf("go %s: cannot install cross-compiled binaries when GOBIN is set", cfg.CmdName)
			case p.Internal.CmdlineFiles:
				base.Errorf("go %s: no install location for .go files listed on command line (GOBIN not set)", cfg.CmdName)
			case p.ConflictDir != "":
				base.Errorf("go %s: no install location for %s: hidden by %s", cfg.CmdName, p.Dir, p.ConflictDir)
			default:
				base.Errorf("go %s: no install location for directory %s outside GOPATH\n"+
					"\tFor more details see: 'go help gopath'", cfg.CmdName, p.Dir)
			}
		}
	}
	base.ExitIfErrors()

	var b Builder
	b.Init()
	depMode := ModeBuild
	if cfg.BuildI {
		depMode = ModeInstall
	}
	a := &Action{Mode: "go install"}
	var tools []*Action
	for _, p := range pkgs {
		// If p is a tool, delay the installation until the end of the build.
		// This avoids installing assemblers/compilers that are being executed
		// by other steps in the build.
		a1 := b.AutoAction(ModeInstall, depMode, p)
		if load.InstallTargetDir(p) == load.ToTool {
			a.Deps = append(a.Deps, a1.Deps...)
			a1.Deps = append(a1.Deps, a)
			tools = append(tools, a1)
			continue
		}
		a.Deps = append(a.Deps, a1)
	}
	if len(tools) > 0 {
		a = &Action{
			Mode: "go install (tools)",
			Deps: tools,
		}
	}

	if cfg.BuildBuildmode == "shared" {
		// Note: If buildmode=shared then only non-main packages
		// are present in the pkgs list, so all the special case code about
		// tools above did not apply, and a is just a simple Action
		// with a list of Deps, one per package named in pkgs,
		// the same as in runBuild.
		a = b.buildmodeShared(ModeInstall, ModeInstall, patterns, pkgs, a)
	}

	b.Do(a)
	base.ExitIfErrors()

	// Success. If this command is 'go install' with no arguments
	// and the current directory (the implicit argument) is a command,
	// remove any leftover command binary from a previous 'go build'.
	// The binary is installed; it's not needed here anymore.
	// And worse it might be a stale copy, which you don't want to find
	// instead of the installed one if $PATH contains dot.
	// One way to view this behavior is that it is as if 'go install' first
	// runs 'go build' and the moves the generated file to the install dir.
	// See issue 9645.
	if len(patterns) == 0 && len(pkgs) == 1 && pkgs[0].Name == "main" {
		// Compute file 'go build' would have created.
		// If it exists and is an executable file, remove it.
		targ := pkgs[0].DefaultExecName()
		targ += cfg.ExeSuffix
		if filepath.Join(pkgs[0].Dir, targ) != pkgs[0].Target { // maybe $GOBIN is the current directory
			fi, err := os.Stat(targ)
			if err == nil {
				m := fi.Mode()
				if m.IsRegular() {
					if m&0111 != 0 || cfg.Goos == "windows" { // windows never sets executable bit
						os.Remove(targ)
					}
				}
			}
		}
	}
}

// ExecCmd is the command to use to run user binaries.
// Normally it is empty, meaning run the binaries directly.
// If cross-compiling and running on a remote system or
// simulator, it is typically go_GOOS_GOARCH_exec, with
// the target GOOS and GOARCH substituted.
// The -exec flag overrides these defaults.
var ExecCmd []string

// FindExecCmd derives the value of ExecCmd to use.
// It returns that value and leaves ExecCmd set for direct use.
func FindExecCmd() []string {
	if ExecCmd != nil {
		return ExecCmd
	}
	ExecCmd = []string{} // avoid work the second time
	if cfg.Goos == runtime.GOOS && cfg.Goarch == runtime.GOARCH {
		return ExecCmd
	}
	path, err := exec.LookPath(fmt.Sprintf("go_%s_%s_exec", cfg.Goos, cfg.Goarch))
	if err == nil {
		ExecCmd = []string{path}
	}
	return ExecCmd
}

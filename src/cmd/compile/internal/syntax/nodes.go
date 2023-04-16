// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package syntax

// ----------------------------------------------------------------------------
// Nodes

type Node interface {
	// Pos() returns the position associated with the node as follows:
	// 1) The position of a node representing a terminal syntax production
	//    (Name, BasicLit, etc.) is the position of the respective production
	//    in the source.
	// 2) The position of a node representing a non-terminal production
	//    (IndexExpr, IfStmt, etc.) is the position of a token uniquely
	//    associated with that production; usually the left-most one
	//    ('[' for IndexExpr, 'if' for IfStmt, etc.)
	Pos() Pos
	aNode()
}

type node struct {
	// commented out for now since not yet used
	// doc  *Comment // nil means no comment(s) attached
	pos Pos
}

func (n *node) Pos() Pos { return n.pos }
func (*node) aNode()     {}

// ----------------------------------------------------------------------------
// Files

// package PkgName; DeclList[0], DeclList[1], ...
type File struct {
	Pragma   Pragma
	PkgName  *Name  // 记录本文件所定义的的go包
	DeclList []Decl // 本文件中的所有decl
	Lines    uint   // 记录本文件的行数
	node
}

// ----------------------------------------------------------------------------
// Declarations

type (
	Decl interface {
		Node
		aDecl()
	}

	//              Path
	// LocalPkgName Path
	ImportDecl struct {
		Group        *Group // nil means not part of a group
		Pragma       Pragma
		LocalPkgName *Name     // including "."; nil means no rename present	表示在本package中导入的package名，如果定义了别名，那就是别名
		Path         *BasicLit // 导入的包的实际名字
		decl
	}

	// NameList
	// NameList      = Values
	// NameList Type = Values			const nameList [Type] = Values
	ConstDecl struct {
		Group    *Group // nil means not part of a group	标记相同组的声明
		Pragma   Pragma
		NameList []*Name // a, b, c = 1,2,3, 这个NameList存储a,b,c为一个列表
		Type     Expr    // nil means no type
		Values   Expr    // nil means no values	Expr本身可能为一个列表,也可能为单个对象,存储一行声明中用逗号隔开的Value列表,也就是上面的1,2,3
		decl
	}

	// Name Type		Type Name [=] Type
	TypeDecl struct {
		Group  *Group // nil means not part of a group
		Pragma Pragma
		Name   *Name // type后面跟的符号名
		Alias  bool  // 是否通过type xxx = yyy 定义了别名，有等号该值为true
		Type   Expr  // 表示一个type声明中后面的Expr
		decl
	}

	// NameList Type
	// NameList Type = Values
	// NameList      = Values		var nameList [Type] = Values
	VarDecl struct {
		Group    *Group // nil means not part of a group
		Pragma   Pragma
		NameList []*Name // a, b, c = 1,2,3, 这个NameList存储a,b,c为一个Name列表
		Type     Expr    // nil means no type
		Values   Expr    // nil means no values	Expr本身可能为一个列表，也可能为单个对象，存储一行声明中用逗号隔开的Value列表
		decl
	}

	// func          Name Type { Body }
	// func          Name Type
	// func Receiver Name Type { Body }
	// func Receiver Name Type
	FuncDecl struct {
		Pragma Pragma
		Recv   *Field // nil means regular function, else is receiver
		Name   *Name  // 函数名
		Type   *FuncType
		Body   *BlockStmt // nil means no body (forward declaration)
		decl
	}
)

type decl struct{ node }

func (*decl) aDecl() {}

// All declarations belonging to the same group point to the same Group node.
type Group struct {
	dummy int // not empty so we are guaranteed different Group instances
}

// ----------------------------------------------------------------------------
// Expressions

type (
	Expr interface {
		Node
		aExpr()
	}

	// Placeholder for an expression that failed to parse
	// correctly and where we can't provide a better node.
	BadExpr struct {
		expr
	}

	// Value
	Name struct {
		Value string // token为Value的字符串字面量
		expr
	}

	// Value
	BasicLit struct {
		Value string  // 字面量的值
		Kind  LitKind // 字面量类型，数字？字符串？字符？浮点数？
		Bad   bool    // true means the literal Value has syntax errors
		expr
	}

	// Type { ElemList[0], ElemList[1], ... }  表示一个结构体字面量或者数组等字面量
	CompositeLit struct {
		Type     Expr   // nil means no literal type
		ElemList []Expr // 组合类型中的一个元素或者一个键值对，与类型相关
		NKeys    int    // number of elements with keys
		Rbrace   Pos
		expr
	}

	// Key: Value
	KeyValueExpr struct {
		Key, Value Expr
		expr
	}

	// func Type { Body }
	FuncLit struct {
		Type *FuncType // 记录函数的类型
		Body *BlockStmt
		expr
	}

	// (X)
	ParenExpr struct {
		X Expr
		expr
	}

	// X.Sel
	SelectorExpr struct {
		X   Expr
		Sel *Name
		expr
	}

	// X[Index]
	IndexExpr struct {
		X     Expr
		Index Expr
		expr
	}

	// X[Index[0] : Index[1] : Index[2]]
	SliceExpr struct {
		X     Expr
		Index [3]Expr //当Index[2]不为nil时，Index[1]不许为nil，如果类似于x[a:b:c]这种情况，Index[2]也不能为nil
		// Full indicates whether this is a simple or full slice expression.
		// In a valid AST, this is equivalent to Index[2] != nil.
		// TODO(mdempsky): This is only needed to report the "3-index
		// slice of string" error when Index[2] is missing.
		Full bool
		expr
	}

	// X.(Type)
	AssertExpr struct {
		X    Expr
		Type Expr
		expr
	}

	// X.(type)
	// Lhs := X.(type)
	TypeSwitchGuard struct {
		Lhs *Name // nil means no Lhs :=
		X   Expr  // X.(type)
		expr
	}

	Operation struct {
		Op   Operator // 实际的操作，Mul, Add, Sub, Not, Xor，And, Recv
		X, Y Expr     // Y == nil means unary expression
		expr
	}

	// Fun(ArgList[0], ArgList[1], ...)
	CallExpr struct {
		Fun     Expr   // 调用的函数Node
		ArgList []Expr // nil means no arguments
		HasDots bool   // last argument is followed by ...
		expr
	}

	// ElemList[0], ElemList[1], ...
	ListExpr struct {
		ElemList []Expr // expr数组
		expr
	}

	// [Len]Elem
	ArrayType struct {
		// TODO(gri) consider using Name{"..."} instead of nil (permits attaching of comments)
		Len  Expr // nil means Len is ...
		Elem Expr // 存储元素的类型
		expr
	}

	// []Elem
	SliceType struct {
		Elem Expr // slice中存储元素的类型
		expr
	}

	// ...Elem
	DotsType struct {
		Elem Expr //此处是一个Type
		expr
	}

	// struct { FieldList[0] TagList[0]; FieldList[1] TagList[1]; ... }
	StructType struct {
		FieldList []*Field
		TagList   []*BasicLit // i >= len(TagList) || TagList[i] == nil means no tag for field i
		expr
	}

	// Name Type
	//      Type
	Field struct {
		Name *Name // nil means anonymous field/parameter (structs/parameters), or embedded interface (interfaces)
		Type Expr  // field names declared in a list share the same Type (identical pointers)
		node
	}

	// interface { MethodList[0]; MethodList[1]; ... }
	InterfaceType struct {
		MethodList []*Field
		expr
	}

	FuncType struct {
		ParamList  []*Field //参数列表
		ResultList []*Field //返回参数列表
		expr
	}

	// map[Key]Value
	MapType struct {
		Key, Value Expr // Key, Value分别表示声明map类型时的键值类型
		expr
	}

	//   chan Elem
	// <-chan Elem
	// chan<- Elem
	ChanType struct {
		Dir  ChanDir // 0 means no direction
		Elem Expr    // 这里表示一个类型
		expr
	}
)

type expr struct {
	node
	// 以下为自增字段
	Extra interface{} // 用于记录一些自定义的内容
}

func (*expr) aExpr() {}

type ChanDir uint

const (
	_        ChanDir = iota
	SendOnly         // chan<- Type
	RecvOnly         // <-chan Type
)

// ----------------------------------------------------------------------------
// Statements

type (
	Stmt interface {
		Node
		aStmt()
	}

	SimpleStmt interface {
		Stmt
		aSimpleStmt()
	}

	EmptyStmt struct {
		simpleStmt
	}

	LabeledStmt struct {
		Label *Name // 记录Label的字面量
		Stmt  Stmt  // 记录Label所在的Statment
		stmt
	}
	// {}中的代码解析
	BlockStmt struct {
		List   []Stmt // stmt数组
		Rbrace Pos
		stmt
	}

	ExprStmt struct {
		X Expr
		simpleStmt
	}

	SendStmt struct {
		Chan, Value Expr // Chan <- Value
		simpleStmt
	}

	DeclStmt struct { //变量声明
		DeclList []Decl // 相当于将某个块声明按行拆分成声明列表，但是声明列表中可能同时为多个变量进行赋值
		stmt
	}
	// x := expr   当op为=或者:=时，lhs与rhs可能为ExprList
	AssignStmt struct {
		Op       Operator // 0 means no operation	maybe lhs op= rhs, lhs++ or lhs-- will be replaced by lhs+=ImplicitOne or lhs-=ImplicitOne
		Lhs, Rhs Expr     // Rhs == ImplicitOne means Lhs++ (Op == Add) or Lhs-- (Op == Sub)
		simpleStmt
	}

	BranchStmt struct {
		Tok   token // Break, Continue, Fallthrough, or Goto
		Label *Name // 记录break label或者continue label中的label的字面量
		// Target is the continuation of the control flow after executing
		// the branch; it is computed by the parser if CheckBranches is set.
		// Target is a *LabeledStmt for gotos, and a *SwitchStmt, *SelectStmt,
		// or *ForStmt for breaks and continues, depending on the context of
		// the branch. Target is not set for fallthroughs.
		Target Stmt
		stmt
	}

	CallStmt struct {
		Tok  token     // Go or Defer
		Call *CallExpr // Go or Defer之后跟的函数调用表达式
		stmt
	}

	ReturnStmt struct {
		Results Expr // nil means no explicit return values		不为nil表示返回表达式列表
		stmt
	}

	IfStmt struct {
		Init SimpleStmt
		Cond Expr
		Then *BlockStmt // Then表示Cond为true时执行的大括号中的代码块
		Else Stmt       // either nil, *IfStmt, or *BlockStmt    如果为*IfStmt表示之后跟着else if,*BlockStmt表示之后跟着else
		stmt
	}

	ForStmt struct {
		Init SimpleStmt // incl. *RangeClause
		Cond Expr
		Post SimpleStmt
		Body *BlockStmt
		stmt
	}

	SwitchStmt struct {
		Init   SimpleStmt
		Tag    Expr          // incl. *TypeSwitchGuard
		Body   []*CaseClause // 表示多个case块
		Rbrace Pos           // 记录}的位置
		stmt
	}

	SelectStmt struct {
		Body   []*CommClause // 记录select语句中的所有case块
		Rbrace Pos           // 记录}的位置
		stmt
	}
)

type (
	RangeClause struct {
		Lhs Expr // nil means no Lhs = or Lhs :=
		Def bool // means :=
		X   Expr // range X
		simpleStmt
	}

	CaseClause struct {
		Cases Expr   // nil means default clause   为case 4， 6， 8： 这种情况时Cases是一个Expr数组
		Body  []Stmt // case块中的statements
		Colon Pos    //记录当前case的:位于文件中的位置
		node
	}

	CommClause struct {
		Comm  SimpleStmt // send or receive stmt; nil means default clause
		Body  []Stmt     // case块中的statements
		Colon Pos        // 记录case块的:的位置
		node
	}
)

type stmt struct{ node }

func (stmt) aStmt() {}

type simpleStmt struct {
	stmt
}

func (simpleStmt) aSimpleStmt() {}

// ----------------------------------------------------------------------------
// Comments

// TODO(gri) Consider renaming to CommentPos, CommentPlacement, etc.
//           Kind = Above doesn't make much sense.
type CommentKind uint

const (
	Above CommentKind = iota
	Below
	Left
	Right
)

type Comment struct {
	Kind CommentKind
	Text string
	Next *Comment
}

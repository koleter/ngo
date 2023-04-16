package aop

type CutPoint struct {
	FuncName      string
	Args, Results []interface{}
}

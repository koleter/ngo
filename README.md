Based on the official go 1.15.6 version, compile according to the official go language



Added the following functions

## Basic types can be used as receivers for functions

```go
package main

import "fmt"

func (i int) cmp(i2 int) bool {
	return i > i2
}

func main() {
	fmt.Println("hello")
	var a = 3
	fmt.Println(a.cmp(4))
}
```

But you can't use the method of 3.cmp(4) to call with all your heart. To call this function, you need to use a variable instead of a constant. In addition, other packages cannot call the declaration in this package.



## Python-like slicing

Support the syntax of arr[i:j;k] and i, j, k are allowed to be negative values, indicating the penultimate item. Note that there is a semicolon instead of a colon between j and k, and k is the step of the slice. This way will create a new slice

```go
package main

import "fmt"

func main() {
	arr := []int{1, 2, 3, 4, 5, 6, 7, 8, 9}
	fmt.Println(arr[2:9])
	fmt.Println(arr[2:-2])
	fmt.Println(arr[1:-1;2])
	fmt.Println(arr[1:-1;-1])
	fmt.Println(arr[2:2;20])
}
```



This will output

```
[3 4 5 6 7 8 9]
[3 4 5 6 7]
[2 4 6 8]
[8 7 6 5 4 3 2]
[]
```



## Support AOP programming

Add the //go:aop line instruction, modifying a function with this instruction can make the function be executed before and after the call of some functions, before means that the function will be called before the matched function is called, after means that it will be called after the call, around Represents the call once before and after, which is equivalent to using before and after at the same time, followed by a colon, followed by a regular expression, and other functions matching the regular expression will be applied to this rule

The input parameter of the modified function is \*aop.CutPoint type, and the output parameter is \*aop.RetPoint type (currently the output parameter has no meaning, it can be any type, it is recommended to be this type)

The structure of aop.CutPoint is as follows

```go
type CutPoint struct {
	FuncName      string
	Args, Results []interface{}
}
```

FuncName represents the function name of the matched function (if the matched function has a receiver, the function name will have a prefix string representing the receiver type), Args and Results represent the input and output parameter lists of the matched function, Modifying these two lists will modify the input and output parameters of this function call (Results is an empty list before the function call)



You can execute the following code and view the output

```go
package main

import (
	"aop"
	"fmt"
)

// func test() {
// 	cutpoint := &aop.CutPoint{}
// 	fmt.Print(cutpoint)
// }

func main() {
	a, b := test1("arg1", "arg2")
	fmt.Println("test1函数的返回结果：", a+" test "+b)
	test2(1, 1)
	test3(3, 3)
}

//go:aop   after:^test.$
func aop1(cp *aop.CutPoint) *aop.RetPoint {
	if cp.FuncName == "test1" {
		fmt.Println("test1的原参数列表：", cp.Args)
		cp.Results[0] = "改掉的返回结果1"
		cp.Results[1] = "改掉的返回结果2"
	}
	fmt.Println("我aop1咋执行了呢, 不是该执行" + cp.FuncName + "吗")
	return nil
}

type Person struct{}

// func (p *Person) test333() {}

func test1(a, b string) (string, string) {
	fmt.Println("test1执行中。。。")
	defer func() {
		a += "添加的内容"
		fmt.Println("闭包函数为参数添加内容成功")
	}()
	return b, a
}

func test2(a, b int) (int, int) {
	fmt.Println("test2函数执行中。。。")
	return b, a
}

func test3(a, b int) (int, int) {
	fmt.Println("test3函数执行中。。。")
	return b, a
}
```

This only affects functions in the same package



<div style='height:300px'></div>



基于官方go 1.15.6版本,按照官方go语言进行编译即可



添加了以下功能

## 基础类型可以作为函数的receiver

```go
package main

import "fmt"

func (i int) cmp(i2 int) bool {
	return i > i2
}

func main() {
	fmt.Println("hello")
	var a = 3
	fmt.Println(a.cmp(4))
}
```

但是不能用3.cmp(4)这样的方式尽心调用，调用该函数需要用一个变量而不是常量，另外其他包不能调用这个包里面声明的



## 类似python的切片

支持arr[i:j;k]这种语法且i，j，k允许为负值，表示倒数第几项，注意j和k之间是分号不是冒号，k就是切片的step，这种方式会创建一个新的切片

```go
package main

import "fmt"

func main() {
	arr := []int{1, 2, 3, 4, 5, 6, 7, 8, 9}
	fmt.Println(arr[2:9])
	fmt.Println(arr[2:-2])
	fmt.Println(arr[1:-1;2])
	fmt.Println(arr[1:-1;-1])
	fmt.Println(arr[2:2;20])
}
```

上方代码输出为：

```
[3 4 5 6 7 8 9]
[3 4 5 6 7]
[2 4 6 8]
[8 7 6 5 4 3 2]
[]
```



## 支持AOP编程

新增//go:aop这个行指令，用该指令修饰一个函数可以令某些函数的调用前后执行该函数，before表示匹配到的函数调用前会调用该函数，after表示调用后会调用，around代表调用前后各一次，相当于同时使用了before和after，再后面跟一个冒号，之后是一个正则表达式，匹配该正则的其他函数会被应用这条规则

被修饰的函数的入参是\*aop.CutPoint类型，出参是\*aop.RetPoint类型(目前出参还没有任何意义，可以为任何类型，建议为该类型)

aop.CutPoint的结构如下所示

```go
type CutPoint struct {
	FuncName      string
	Args, Results []interface{}
}
```

FuncName代表匹配到的函数的函数名(如果匹配到的函数有receiver，那么函数名会有代表这个receiver类型的前缀字符串)，Args, Results分别代表了被匹配函数的入参和出参列表，修改这两个列表会修改这个函数调用时的入参和出参(函数调用前Results是一个空列表)



可以执行如下代码并查看输出

```go
package main

import (
	"aop"
	"fmt"
)

// func test() {
// 	cutpoint := &aop.CutPoint{}
// 	fmt.Print(cutpoint)
// }

func main() {
	a, b := test1("arg1", "arg2")
	fmt.Println("test1函数的返回结果：", a+" test "+b)
	test2(1, 1)
	test3(3, 3)
}

//go:aop   after:^test.$
func aop1(cp *aop.CutPoint) *aop.RetPoint {
	if cp.FuncName == "test1" {
		fmt.Println("test1的原参数列表：", cp.Args)
		cp.Results[0] = "改掉的返回结果1"
		cp.Results[1] = "改掉的返回结果2"
	}
	fmt.Println("我aop1咋执行了呢, 不是该执行" + cp.FuncName + "吗")
	return nil
}

type Person struct{}

// func (p *Person) test333() {}

func test1(a, b string) (string, string) {
	fmt.Println("test1执行中。。。")
	defer func() {
		a += "添加的内容"
		fmt.Println("闭包函数为参数添加内容成功")
	}()
	return b, a
}

func test2(a, b int) (int, int) {
	fmt.Println("test2函数执行中。。。")
	return b, a
}

func test3(a, b int) (int, int) {
	fmt.Println("test3函数执行中。。。")
	return b, a
}
```

目前aop只会影响相同包内的函数


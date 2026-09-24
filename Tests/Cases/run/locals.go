// run
// optimized-has: target datalayout
// optimized-has: target triple
// optimized-lacks: = alloca

package main

func mark(x int) int {
	println(x)
	return x
}

func update(x int) int {
	var zero int
	println(zero)
	x = x + 1
	y := mark(x)
	if 0 < x {
		y = y + 2
		x := x + y
		println(x)
		var y int
		println(y)
		y = 9
		println(y)
	}
	if x < 0 {
		y = 99
	}
	flag := 2 < 1
	if 0 < x {
		flag = 2 < 3
	}
	if flag {
		y = y + 4
	}
	return y
}

func early(x int) int {
	if x < 1 {
		var y int = 8
		return y
	}
	var y int = 3
	return y
}

func main() {
	println(update(3))
	z := mark(1) + mark(2)
	println(z)
	println(early(0))
	println(early(1))
}

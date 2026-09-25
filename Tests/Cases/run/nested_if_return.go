// run

package main

func f(x int, y int) int {
	if x < y {
		if y < 3 {
			return y
		}
	}
	return x
}

func main() {
	println(f(1, 2))
	println(f(1, 5))
	println(f(4, 2))
}

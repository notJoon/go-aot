// errorcheck

package main

func f(n int) int {
	return n
}

func main() {
	println(f(1 < 2)) // ERROR 12 "function arguments must be int"
}

// errorcheck

package main

func f(n int) int {
	return n
}

func main() {
	f(1 < 2) // ERROR 4 "function arguments must be int"
}

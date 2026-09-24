// errorcheck

package main

func f(println int) int {
	println(1) // ERROR "cannot call non-function 'println'"
	return 1
}

func main() {}

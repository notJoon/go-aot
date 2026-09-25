// errorcheck

package main

func f(println int) int {
	return 1
	if 0 < 1 {
		println(1) // ERROR "cannot call non-function 'println'"
	}
	return 2
}

func main() {}

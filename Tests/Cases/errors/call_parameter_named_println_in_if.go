// errorcheck

package main

func f(println int) int {
	if println < 1 {
		println(1) // ERROR "cannot call non-function 'println'"
	}
	return println
}

func main() {}

// errorcheck

package main

func f(g int) int {
	g(1) // ERROR "cannot call non-function 'g'"
	return 1
}

func main() {}

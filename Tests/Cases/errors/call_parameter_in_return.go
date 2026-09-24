// errorcheck

package main

func g(x int) int {
	return x
}

func f(g int) int {
	return g(g) // ERROR 9 "cannot call non-function 'g'"
}

func main() {}

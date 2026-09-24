// errorcheck

package main

func f(n int) int {
	return n
}

func main() {
	f() // ERROR "function 'f' expects 1 arguments"
}

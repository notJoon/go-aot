// errorcheck

package main

func f(n int) int {
	return n
}

func main() {
	println(f()) // ERROR 10 "function 'f' expects 1 arguments"
}

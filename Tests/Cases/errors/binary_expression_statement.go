// errorcheck

package main

func f(n int) int {
	return n
}

func main() {
	f(1) + 1 // ERROR "only function calls may be used as statements"
}

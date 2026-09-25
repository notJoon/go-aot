// errorcheck

package main

func f(x int) int {
	x := 1 // ERROR "duplicate declaration 'x'"
	return x
}

func main() {}

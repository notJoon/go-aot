// errorcheck

package main

func f() int {
	return 1
	var x int
	x := 2 // ERROR "duplicate declaration 'x'"
	return x
}

func main() {}

// errorcheck

package main

func f() int {
	return 1
	x = 2 // ERROR "unknown identifier 'x'"
	return 0
}

func main() {}

// errorcheck

package main

func f(x int, x int) int { // ERROR 15 "duplicate parameter 'x'"
	return x
}

func main() {}

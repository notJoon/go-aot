// errorcheck

package main

func f(x int) int {
	return x
}

func main() {
	println(x) // ERROR 10 "unknown identifier 'x'"
}

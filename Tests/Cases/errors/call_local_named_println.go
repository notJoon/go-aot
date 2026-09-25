// errorcheck

package main

func main() {
	println := 1
	println(2) // ERROR "cannot call non-function 'println'"
}

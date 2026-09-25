// errorcheck

package main

func f() int {
	return 1
}

func main() {
	f := 2
	x := f() // ERROR 7 "cannot call non-function 'f'"
}

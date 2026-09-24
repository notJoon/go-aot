// errorcheck

package main

func f() (int, int) {
	return 1, 2
}

func main() {
	var a bool
	a, b := f() // ERROR "assignment type does not match variable type"
}

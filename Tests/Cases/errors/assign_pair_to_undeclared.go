// errorcheck

package main

func f() (int, int) {
	return 1, 2
}

func main() {
	a, b = f() // ERROR "unknown identifier 'a'"
}

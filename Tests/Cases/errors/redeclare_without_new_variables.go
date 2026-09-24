// errorcheck

package main

func f() (int, int) {
	return 1, 2
}

func main() {
	a, b := f()
	a, b := f() // ERROR "no new variables on left side of :="
}

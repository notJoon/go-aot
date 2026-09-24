// errorcheck

package main

func f() (int, int) {
	return 1, 2
}

func main() {
	a, a := f() // ERROR 5 "'a' repeated on left side of :="
}

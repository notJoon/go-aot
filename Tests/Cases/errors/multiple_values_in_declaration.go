// errorcheck

package main

func f() (int, int) {
	return 1, 2
}

func main() {
	x := f() // ERROR 7 "multiple-value f() in single-value context"
}

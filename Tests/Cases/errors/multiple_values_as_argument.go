// errorcheck

package main

func f() (int, int) {
	return 1, 2
}

func main() {
	println(f()) // ERROR 10 "multiple-value f() in single-value context"
}

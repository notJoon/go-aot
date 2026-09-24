// errorcheck

package main

func g() (int, int) {
	return 1, 2
}

func f() (int, bool) {
	return g() // ERROR 9 "results of g() do not match the results of function 'f'"
}

func main() {}

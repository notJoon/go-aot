// errorcheck

package main

func f() (int, int) {
	return 1 // ERROR "not enough return values in function 'f'"
}

func main() {}

// errorcheck

package main

func f() int {
	return 1, 2 // ERROR 12 "too many return values in function 'f'"
}

func main() {}

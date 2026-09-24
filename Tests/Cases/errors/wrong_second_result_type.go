// errorcheck

package main

func f() (int, int) {
	return 1, true // ERROR 12 "return value must be int"
}

func main() {}

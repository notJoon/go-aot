// errorcheck

package main

func f() int {
	return 1 < 2 // ERROR 9 "return value must be int"
}

func main() {}

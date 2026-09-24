// errorcheck

package main

func f() bool {
	return 1 // ERROR 9 "return value must be bool"
}

func main() {}

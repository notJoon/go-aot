// errorcheck

package main

func f() int {
	return 1
	if 1 { // ERROR 5 "if condition must be bool"
	}
	return 2
}

func main() {}

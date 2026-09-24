// errorcheck

package main

func g() int {
	return 1
}

func main() {
	a, b := g() // ERROR 10 "assignment mismatch: 2 variables but g() returns 1 value"
}

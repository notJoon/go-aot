// errorcheck

package main

func f(b bool) bool {
	return b
}

func main() {
	f(1) // ERROR 4 "function arguments must be bool"
}

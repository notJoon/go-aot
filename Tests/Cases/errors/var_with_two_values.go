// errorcheck

package main

func main() {
	var x int = 1, 2 // ERROR 15 "multiple variable declarations and assignments are unsupported"
}

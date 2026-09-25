// errorcheck

package main

func main() {
	var x int
	x = 1 < 2 // ERROR 6 "assignment type does not match variable type"
}

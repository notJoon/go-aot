// errorcheck

package main

func main() {
	x := 1 < 2
	x = 1 // ERROR 6 "assignment type does not match variable type"
}

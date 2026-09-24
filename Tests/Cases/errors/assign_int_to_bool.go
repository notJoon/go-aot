// errorcheck

package main

func main() {
	b := true
	b = 1 // ERROR 6 "assignment type does not match variable type"
}

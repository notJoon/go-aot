// errorcheck

package main

func main() {
	if 1 && true {} // ERROR 5 "logical operands must be bool"
}

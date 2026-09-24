// errorcheck

package main

func main() {
	if true || 1 {} // ERROR 13 "logical operands must be bool"
}

// errorcheck

package main

func main() {
	var x int = 1 < 2 // ERROR 14 "initializer must be int"
}

// errorcheck

package main

func main() {
	x := 1
	x := 2 // ERROR "duplicate declaration 'x'"
}

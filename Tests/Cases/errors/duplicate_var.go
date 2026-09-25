// errorcheck

package main

func main() {
	var x int
	var x int // ERROR 6 "duplicate declaration 'x'"
}

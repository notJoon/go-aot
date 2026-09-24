// errorcheck

package main

func main() {
	var x int8 = 200 // ERROR 15 "constant 200 overflows int8"
}

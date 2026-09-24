// errorcheck

package main

func main() {
	var x uint8 = -1 // ERROR 16 "constant -1 overflows uint8"
}

// errorcheck

package main

func main() {
	println(0x1p-2) // ERROR 10 "hexadecimal floating-point literals are unsupported"
}

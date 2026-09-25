// errorcheck

package main

func main() {
	println(0x8000000000000000) // ERROR 10 "constant 9223372036854775808 overflows int"
}

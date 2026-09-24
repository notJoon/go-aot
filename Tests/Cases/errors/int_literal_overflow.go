// errorcheck

package main

func main() {
	println(9223372036854775808) // ERROR 10 "constant 9223372036854775808 overflows int"
}

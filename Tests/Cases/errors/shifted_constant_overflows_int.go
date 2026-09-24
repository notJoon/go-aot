// errorcheck

package main

func main() {
	println(1 << 70) // ERROR 10 "constant 1180591620717411303424 overflows int"
}

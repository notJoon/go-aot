// errorcheck

package main

func main() {
	println(1 << 1.5) // ERROR 15 "constant 1.5 truncated to shift count"
}

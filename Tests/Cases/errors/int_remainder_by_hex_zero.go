// errorcheck

package main

func main() {
	println(1 % 0x0) // ERROR 14 "division by zero"
}

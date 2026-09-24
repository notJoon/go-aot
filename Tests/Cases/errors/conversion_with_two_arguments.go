// errorcheck

package main

func main() {
	println(int8(1, 2)) // ERROR 10 "conversion to int8 expects one argument"
}

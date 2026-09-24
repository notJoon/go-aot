// errorcheck

package main

func main() {
	println(1.5 % 2) // ERROR 10 "operator % is not defined on untyped float"
}

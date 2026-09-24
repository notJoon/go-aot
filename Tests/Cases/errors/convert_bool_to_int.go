// errorcheck

package main

func main() {
	println(int(true)) // ERROR 14 "cannot convert bool to int"
}

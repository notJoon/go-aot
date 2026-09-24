// errorcheck

package main

func main() {
	println(bool(1)) // ERROR 15 "cannot convert untyped int to bool"
}

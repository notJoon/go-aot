// errorcheck

package main

func main() {
	println(1 << -1) // ERROR 15 "negative shift count"
}

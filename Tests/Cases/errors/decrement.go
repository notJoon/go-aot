// errorcheck

package main

func main() {
	x-- // ERROR 3 "increment and decrement statements are unsupported"
}

// errorcheck

package main

func main() {
	x += 1 // ERROR 4 "compound assignments are unsupported"
}

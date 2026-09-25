// errorcheck

package main

func main() {
	if 1 < 2 {
		x := 1
	}
	if 1 < 2 {
		println(x) // ERROR 11 "unknown identifier 'x'"
	}
}

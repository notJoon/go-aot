// errorcheck

package main

func main() {
	if 1 < 2 {
		x := 1
	}
	println(x) // ERROR 10 "unknown identifier 'x'"
}

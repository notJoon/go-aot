// errorcheck

package main

func main() {
	for i := 0; i < 1; a, b := f() { // ERROR 33 "for post statement cannot declare a variable"
	}
}

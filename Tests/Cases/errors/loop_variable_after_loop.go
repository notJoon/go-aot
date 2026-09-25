// errorcheck

package main

func main() {
	for i := 0; i < 1; i = i + 1 {
	}
	println(i) // ERROR 10 "unknown identifier 'i'"
}

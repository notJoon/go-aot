// errorcheck

package main

func main() {
	var a int8
	var b int16
	println(a + b) // ERROR 14 "mismatched types int8 and int16"
}

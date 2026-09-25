// errorcheck

package main

// Columns count UTF-8 bytes, so "가" moves the error three columns, not one.
func main() {
	println("가"); println(missing) // ERROR 26 "unknown identifier 'missing'"
}

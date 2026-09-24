// errorcheck

package main

func main() {
	println(1e400) // ERROR 10 "constant overflows float64"
}

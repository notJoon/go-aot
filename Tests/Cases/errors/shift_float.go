// errorcheck

package main

func main() {
	f := 1.5
	println(f << 1) // ERROR 10 "operator << is not defined on float64"
}

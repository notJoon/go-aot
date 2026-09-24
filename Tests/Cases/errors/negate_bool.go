// errorcheck

package main

func main() {
	println(-true) // ERROR 11 "operator - is not defined on bool"
}

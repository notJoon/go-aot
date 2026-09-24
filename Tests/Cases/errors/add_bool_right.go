// errorcheck

package main

func main() {
	println(1 + true) // ERROR 14 "operator + is not defined on bool"
}

// errorcheck

package main

func f() {}

func main() {
	println(f()) // ERROR 10 "function 'f' does not return a value"
}

// errorcheck

package main

func main() {
	println(true < false) // ERROR 10 "operator < is not defined on bool"
}

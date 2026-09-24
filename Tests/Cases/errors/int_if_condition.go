// errorcheck

package main

func main() {
	if 1 { println(2) } // ERROR 5 "if condition must be bool"
}

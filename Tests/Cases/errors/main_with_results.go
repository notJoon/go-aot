// errorcheck

package main

func main() (int, int) { // ERROR "main must have no parameters or return value"
	return 1, 2
}

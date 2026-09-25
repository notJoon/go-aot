// errorcheck

package main

func main() {
	1 = 2 // ERROR "assignment target must be an identifier"
}

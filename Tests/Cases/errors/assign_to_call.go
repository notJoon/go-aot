// errorcheck

package main

func main() {
	f() = 1 // ERROR "assignment target must be an identifier"
}

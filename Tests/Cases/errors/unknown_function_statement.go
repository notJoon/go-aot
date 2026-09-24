// errorcheck

package main

func main() {
	missing() // ERROR "unknown function 'missing'"
}

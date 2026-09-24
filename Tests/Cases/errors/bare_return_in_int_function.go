// errorcheck

package main

func f() int {
	return // ERROR "function 'f' must return a value"
}

func main() {}

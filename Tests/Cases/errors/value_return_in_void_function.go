// errorcheck

package main

func f() {
	return 1 // ERROR 9 "function 'f' returns no value"
}

func main() {}

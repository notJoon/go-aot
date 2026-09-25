// errorcheck

package main

func f() int {
	return 1
	println(missing) // ERROR 10 "unknown identifier 'missing'"
}

func main() {}

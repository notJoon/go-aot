// errorcheck

package main

func f() int {
	return 1
	if 0 < 1 {
		println(missing) // ERROR 11 "unknown identifier 'missing'"
	}
	return 2
}

func main() {}

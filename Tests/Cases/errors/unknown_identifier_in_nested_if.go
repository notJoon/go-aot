// errorcheck

package main

func f(x int) int {
	if x < 1 {
		if x < 2 {
			return missing // ERROR 11 "unknown identifier 'missing'"
		}
	}
	return x
}

func main() {}

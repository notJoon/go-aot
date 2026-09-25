// errorcheck

package main

func f(g int) int {
	if g < 1 {
		return g(1) // ERROR 10 "cannot call non-function 'g'"
	}
	return g
}

func main() {}

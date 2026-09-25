// errorcheck

package main

func f() int { // ERROR "function 'f' must end with return"
	return 1
	println(2)
}

func main() {}

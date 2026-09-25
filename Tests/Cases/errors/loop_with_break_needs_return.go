// errorcheck

package main

func f() int { // ERROR "function 'f' must end with return"
	for {
		return 1
		break
	}
}

func main() {}

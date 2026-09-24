// errorcheck

package main

func f() (int, int) {
	return 1, 2
}

func main() {
	_, _ := f() // ERROR "no new variables on left side of :="
}

// errorcheck

package main

func f() int {
	return 1
	for {
		break
		println(1 + true) // ERROR 15 "operator + is not defined on bool"
	}
}

func main() {}

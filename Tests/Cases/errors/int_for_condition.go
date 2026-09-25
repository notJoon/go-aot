// errorcheck

package main

func main() {
	for 1 { // ERROR 6 "for condition must be bool"
		println(2)
	}
}

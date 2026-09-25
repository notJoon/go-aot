// errorcheck

package main

func main() {
	for {
		break L // ERROR 9 "labeled break is unsupported"
	}
}

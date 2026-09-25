// errorcheck

package main

func main() {
	for {
		break
		var x int
		x := 1 // ERROR "duplicate declaration 'x'"
	}
}

// run

package main

func choose(n int) int {
	if n < 1 {
		return 4
	} else {
		return 5
	}
}

func main() {
	println(choose(0))
	println(choose(1))
}

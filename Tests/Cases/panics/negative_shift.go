// panic: runtime error: negative shift amount

package main

func main() {
	println(1)
	s := -1
	println(1 << s)
}

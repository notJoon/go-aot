// panic: runtime error: negative shift amount

package main

func main() {
	println(1)
	var s int8 = -1
	println(uint8(1) >> s)
}

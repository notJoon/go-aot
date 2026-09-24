// run
// ir-lacks: dead marker

package main

func main() {
	for ; ; println("dead marker") {
		break
	}
	println(1)
}

package main

func f() int {
	for {
		return 1
	}
	println("dead marker")
	return 2
}

func main() {
	println(f())
}

package main

func f() int {
	for {
		return 1
	}
}

func g() int {
	for {
	}
}

func main() {
	println(f())
}

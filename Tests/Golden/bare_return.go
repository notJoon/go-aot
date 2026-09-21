package main

func printPositive(n int) {
	if n < 1 {
		return
	}
	println(n)
}

func main() {
	printPositive(0)
	printPositive(2)
}

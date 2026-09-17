package main

func main() {
	for {
		if 0 < 1 {
			break
			var afterBreak int = 1
			afterBreak = 2
			println(afterBreak)
			println("dead marker")
		} else {
			continue
			var afterContinue int = 3
			afterContinue = 4
			println(afterContinue)
			println("dead marker")
		}
		println("dead marker")
	}
	println(7)
}

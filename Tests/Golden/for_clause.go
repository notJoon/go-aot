package main

func main() {
	for i := 0; i < 4; i = i + 1 {
		if i < 2 {
			continue
		}
		println(i)
	}
}

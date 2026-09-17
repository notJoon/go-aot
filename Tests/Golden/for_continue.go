package main

func main() {
	i := 0
	for i < 4 {
		i = i + 1
		if i < 3 {
			continue
		}
		println(i)
	}
}

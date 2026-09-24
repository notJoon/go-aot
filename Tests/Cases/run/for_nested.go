// run

package main

func main() {
	for i := 0; i < 2; i = i + 1 {
		for j := 0; j < 3; j = j + 1 {
			if j < 1 {
				continue
			}
			if 1 < j {
				break
			}
			println(i)
			println(j)
		}
		println(8)
	}
}

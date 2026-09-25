// run

package main

func 계산(값 int) int {
	결과 := 값 * 2
	return 결과
}

func nåde(π float64) (float64, bool) {
	return π, π > 3
}

func main() {
	println(계산(21))
	크기, ok := nåde(3.5)
	println(크기)
	println(ok)
}

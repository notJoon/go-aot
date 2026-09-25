// run

package main

// Each literal must round to the nearest float64, ties to even, including subnormals. A value one
// float64 away would print differently, since println prints the shortest digits that round trip.
func main() {
	println(0.1)
	println(0.3)
	println(1e-5)
	println(123456789.0)
	println(1.7976931348623157e308)
	println(5e-324)
	println(2.5e-324)
	println(2.4e-324)
	println(2.2250738585072011e-308)
	println(9007199254740993.0)
	println(9007199254740995.0)
}

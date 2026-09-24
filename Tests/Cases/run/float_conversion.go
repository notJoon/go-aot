// run
// gc-arch: arm64

package main

func main() {
    big := 300.0
    println(uint8(big))
    println(int8(-big))
    huge := 1e30
    println(int64(huge))
    println(int64(-huge))
    println(uint64(huge))
    println(uint64(-big))
    println(int32(huge))
    var zero float64
    nan := zero / zero
    println(int64(nan))
    println(uint32(nan))
}

package main

func nextInt8(x int8) int8 {
    return x + 1
}

func nextInt16(x int16) int16 {
    return x + 1
}

func nextInt32(x int32) int32 {
    return x + 1
}

func nextInt64(x int64) int64 {
    return x + 1
}

func nextInt(x int) int {
    return x + 1
}

func nextUint8(x uint8) uint8 {
    return x + 1
}

func nextUint16(x uint16) uint16 {
    return x + 1
}

func nextUint32(x uint32) uint32 {
    return x + 1
}

func nextUint64(x uint64) uint64 {
    return x + 1
}

func nextUint(x uint) uint {
    return x + 1
}

func half(x float64) float64 {
    return x / 2
}

func main() {
    println(nextInt8(127))
    println(nextInt16(32767))
    println(nextInt32(2147483647))
    println(nextInt64(9223372036854775807))
    println(nextInt(9223372036854775807))
    println(nextUint8(255))
    println(nextUint16(65535))
    println(nextUint32(4294967295))
    println(nextUint64(18446744073709551615))
    println(nextUint(18446744073709551615))
    println(half(3))

    var a int8 = 100
    println(a * 3)
    println(-a - 29)
    var b uint8 = 200
    println(b / 3)
    println(b % 7)
    println(b > 100)
    var zero uint64
    println(zero - 1)
    println(zero - 1 > 1)
    println((zero - 1) / 2)
    var c uint16 = 65535
    println(c * c)
    var d int32 = -2147483648
    println(d / -1)
    println(d % -1)

    println(^a)
    println(^b)
    println(b & 0x0f | 0x30 ^ 0x01)
    println(b &^ 0xc0)
    var one uint8 = 1
    var n int = 7
    println(one << n)
    n = 8
    println(one << n)
    println(a >> 100)
    a = -128
    println(a >> 1)
    println(a >> 100)
    var count uint = 3
    println(-17 >> count)
    println(1 << 62)

    big := 300
    println(int8(big))
    println(uint8(-big))
    println(int64(int32(-5)))
    println(uint64(uint32(4294967295)))
    println(uint32(zero - 1))
    println(float64(big) / 7)
    f := 3.9
    println(int(f))
    println(int(-f))
    println(uint8(f))

    println(1.5 + 2.25)
    println(0.1 + 0.2)
    println(1.0 / 3)
    println(123456789.0)
    println(1e100)
    println(1e-5)
    println(-2.5)
    var nothing float64
    println(nothing)
    println(-nothing)
    println(1 / nothing)
    println(-1 / nothing)
    nan := nothing / nothing
    println(nan)
    println(nan == nan)
    println(nan != nan)
    println(nan < 1)
    println(0.5 < f)
    println(f >= 3.9)
    println(true)
    println(1 < 2 && 3 > 4)
}

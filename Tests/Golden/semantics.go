package main

func mark(n int) int {
    println(n)
    return n
}

func combine(a int, b int, c int) int {
    return a + b + c
}

func even(n int) int {
    if n < 1 {
        return 1
    }
    return odd(n - 1)
}

func odd(n int) int {
    if n < 1 {
        return 0
    }
    return even(n - 1)
}

func main() {
    println(combine(mark(1), mark(2), mark(3)))
    println(even(10) + odd(10))
    println(mark(4) - mark(5) + mark(6))
    if mark(7) + mark(8) < mark(9) + mark(10) {
        println(11)
    }
}

package main

func show(b bool) {
    if b {
        println(1)
    } else {
        println(0)
    }
}

func yes(n int) bool {
    println(n)
    return true
}

func no(n int) bool {
    println(n)
    return false
}

func main() {
    println(1 + 2 * 3)
    println((1 + 2) * 3)
    println(10 - 4 - 3)
    println(100 / 10 / 5)
    println(7 % 4 * 3)
    println(-7 / 2)
    println(-7 % 2)
    println(7 % -2)
    println(- -5)
    lowest := -9223372036854775807 - 1
    m := -1
    println(lowest / m)
    println(lowest % m)
    show(1 + 1 == 2)
    show(1 < 2 == true)
    show(2 <= 2)
    show(3 > 4)
    show(4 >= 5)
    show(1 != 2)
    show(true != false)
    show(!(1 < 2))
    show(!false == true)
    show(no(1) && yes(2))
    show(yes(3) || no(4))
    show(yes(5) && no(6))
    show(no(7) || yes(8))
    show(no(9) || yes(10) && no(11))
    show(yes(12) || no(13) && yes(14))
}

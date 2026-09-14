package main

func choose(n int) int {
    if n < 3 {
        if n < 1 {
            return 10
            println("dead inner")
            if 0 < 1 { println("dead branch") }
        }
        println(20)
        if n < 2 { return 21 }
        println(22)
    }
    println(30)
    return 31
    println("dead outer")
    return 32
}

func main() {
    if 1 < 0 {}
    println(choose(0))
    println(choose(1))
    println(choose(2))
    println(choose(3))
}

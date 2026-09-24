// run

package main

func one(n int) int {
    println(n)
    return n
}

func show(n int) {
    println(n)
}

func main() {
    one(1)
    show(2)
    one(one(3))
    for i := 4; i < 6; i = i + 1 {
        one(i)
    }
    for i := 6; i < 8; one(i) {
        i = i + 1
    }
}

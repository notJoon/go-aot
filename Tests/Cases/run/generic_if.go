// run

package main

func choose(n int) int {
    if n < 2 {
        return 7
    }
    return n + 1
}

func main() {
    println(choose(1) + choose(2))
}

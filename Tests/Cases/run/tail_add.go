// run

package main

func bump(n int) int {
    return n + 1
}

func sum(n int) int {
    if n < 2 {
        return bump(n)
    }
    return bump(n) + sum(n - 1)
}

func main() {
    println(sum(5))
}

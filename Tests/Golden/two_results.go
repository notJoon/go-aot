package main

func split(n int) (int, bool) {
    return n - 1, n > 0
}

func main() {
    rest, positive := split(3)
    println(rest)
    println(positive)
}

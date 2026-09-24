// run

package main

func less(a int, b int) bool {
    return a < b
}

func not(b bool) bool {
    if b {
        return false
    }
    return true
}

func main() {
    var zero bool
    if not(zero) {
        println(1)
    }
    ok := less(1, 2)
    if ok {
        println(2)
    }
    if not(true) {
        println(3)
    } else {
        println(4)
    }
    var flag bool = false
    flag = less(2, 1)
    if not(flag) {
        println(5)
    }
    false := 6
    println(false)
}

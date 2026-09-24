// run

package main

func divmod(a int, b int) (int, int) {
    return a / b, a % b
}

func lookup(key int) (float64, bool) {
    if key == 1 {
        return 1.5, true
    }
    return 0, false
}

func swap(a int8, b uint16) (uint16, int8) {
    return b, a
}

func trace(n int) int {
    println(n)
    return n
}

func order() (int, int, int) {
    return trace(1), trace(2), trace(3)
}

func forward(a int, b int) (int, int) {
    return divmod(b, a)
}

func main() {
    q, r := divmod(17, 5)
    println(q)
    println(r)
    value, ok := lookup(1)
    println(value)
    println(ok)
    value, ok = lookup(2)
    println(value)
    println(ok)
    _, missing := lookup(3)
    println(missing)
    q, rest := divmod(-7, 2)
    println(q)
    println(rest)
    x, y := swap(-1, 65535)
    println(x)
    println(y)
    a, _, c := order()
    println(a + c)
    order()
    if q < 0 {
        q, inner := divmod(9, 4)
        println(q + inner)
    }
    println(q)
    f, g := forward(3, 20)
    println(f * 10 + g)
}

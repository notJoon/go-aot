// errorcheck

package main

func f() (x int) {} // ERROR 13 "named results are unsupported"

func main() {}

// errorcheck

package main

func main() {
	if !1 {} // ERROR 6 "operator ! is not defined on untyped int"
}

// errorcheck

package main

func main() {
	for {
		continue L // ERROR 12 "labeled continue is unsupported"
	}
}

# GoAot

`GoAot.lex` tokenizes Go source. `GoAot.parse` currently accepts a package clause followed by
zero or more empty, parameterless functions such as `func main() {}`.

Build with `lake build`; run unit checks with `mise run test` and parser golden checks with
`mise run test:integration`.

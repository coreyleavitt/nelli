## RFC-0016 K8b (INT-56): the pragma names the walk meets on stdlib routines
## that are no pragma word of the compiler: system's and the stdlib's pragma
## aliases (`rtl`, `inl`, `benign`, ...) and macro pragmas (`async`,
## `multisync`, `since`, ...). Each is admitted as a routine (or type) row of
## the pragma axis (`pragmaaxes`), and a user program can carry the name only
## as a custom pragma of its own. The pragma axis suites import this module so
## the fragments (`s0016_k8b_snippets`) can name them.

template benign*() {.pragma.}
template rtl*() {.pragma.}
template rtlFunc*() {.pragma.}
template inl*() {.pragma.}
template compilerRtl*() {.pragma.}
template noWeirdTarget*() {.pragma.}
template noNimJs*() {.pragma.}
template nimhcr*() {.pragma.}
template hcrInline*() {.pragma.}
template multisync*() {.pragma.}
template since*() {.pragma.}
template async*() {.pragma.}
template parseRaises*() {.pragma.}
template parseFormatRaises*() {.pragma.}
template auditDelete*() {.pragma.}
template evalonce*() {.pragma.}
template myShallow*() {.pragma.}
template epollPacked*() {.pragma.}
template outParamsAt*() {.pragma.}
template importIconv*() {.pragma.}
template lcrypto*() {.pragma.}
template boehmGC*() {.pragma.}
template gcMark*() {.pragma.}
template errorNoReturn*() {.pragma.}
template nimbaseH*() {.pragma.}
template operator*() {.pragma.}
template tlsEmulation*() {.pragma.}
template exportJs*() {.pragma.}

# `dynlib` and `nosinks` are rejected on a type: a custom pragma of the name,
# NOT exported (an importer's routine `dynlib` stays the builtin), and the
# types the type rows read, declared here at top level.
template dynlib() {.pragma.}
template nosinks() {.pragma.}
type
  K8bDynO* {.dynlib.} = object
    x*: int
  K8bNoSinksP* = proc (x: int): int {.nimcall, nosinks.}

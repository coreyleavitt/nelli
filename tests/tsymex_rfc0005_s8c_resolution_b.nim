## RFC-0005 (soundness channels) slice S8c -- silent substitution by
## NAME-resolved builtins (§2.2's class). The DSL parser recognised operators
## (`+ - * < == ...`), `contains`/`in`, `len`, `inc`/`dec`, `+=`, the `items`
## iterator and the rest of its builtin vocabulary by the callee's NAME. A
## user overload of one of those names -- `+` on a `distinct int`, `==` on an
## object, a non-generic `contains`/`len`/`items` that beats the stdlib
## generic, a `converter` -- was modelled as the builtin, so the engine
## claimed `sxSat`/`sxUnsat` about semantics the program does not have, with
## nothing recorded.
##
## S8c resolves the callee by SYMBOL: a builtin model applies only when the
## call's resolved symbol is declared in the compiler's own `lib/` tree. A
## user routine is walked like any other user call (the precise answer, not a
## taint); a user `converter` is walked too, and a user `method` (dynamic
## dispatch) is a recorded callee decline. The second-order shape -- a
## stdlib generic whose instantiated body reaches a user routine -- is pinned
## below as closed by the element fragment.
## Walker 149 -> 150.
##
## Part b of 6 of what was one suite (`tsymex_rfc0005_s8c_resolution`, 25 tests
## in one file: the corpus's 240 s wall-clock watchdog on the Windows legs
## killed it). Shared overloads and SUTs: `s8c_resolution_defs.nim`.
include ./s8c_resolution_defs

suite "RFC-0005 S8c -- a user overload is walked, not modelled as the builtin (part b)":

  test "user non-generic `contains` beats sets.contains: unreachable (was a false sxSat)":
    let r = pinFind(s8cContains, tLabel("s8c_contains"))
    dump(r.errors)
    check r.status == sxUnsat

  test "user non-generic `len` beats system.len: unreachable (was a false sxSat)":
    let r = pinFind(s8cLen, tLabel("s8c_len"))
    dump(r.errors)
    check r.status == sxUnsat

  test "user non-generic `items` beats system.items: reachable (was a false sxUnsat)":
    let r = pinFind(s8cItems, tLabel("s8c_items"))
    dump(r.errors)
    check r.status != sxUnsat
    check r.status == sxSat

  test "a user `converter` is walked (was declined as an unsupported expression)":
    let r = pinFind(s8cConverter, tLabel("s8c_converter"))
    dump(r.errors)
    check r.status == sxSat

  test "user non-generic `add` beats system.add: reachable (was a false sxUnsat)":
    let r = pinFind(s8cAdd, tLabel("s8c_add"))
    dump(r.errors)
    check r.status == sxSat

  test "user string-receiver `find`: unreachable (was a false sxSat)":
    let r = pinFind(s8cFind, tLabel("s8c_find"))
    dump(r.errors)
    check r.status == sxUnsat

  test "a user proc named `symexAssume` is not the marker: reachable (was a false sxUnsat)":
    let r = pinFind(s8cForeignAssume, tLabel("s8c_foreign_assume"))
    dump(r.errors)
    check r.status == sxSat
    check r.witness[0] == 2

suite "RFC-0005 S8c -- walker version pin":

  test "walker version floor >= 150 (S8c: callee resolution by symbol)":
    check parseInt(symexWalkerVersion) >= 150

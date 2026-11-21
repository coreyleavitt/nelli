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
## Part a of 6 of what was one suite (`tsymex_rfc0005_s8c_resolution`, 25 tests
## in one file: the corpus's 240 s wall-clock watchdog on the Windows legs
## killed it). Shared overloads and SUTs: `s8c_resolution_defs.nim`.
include ./s8c_resolution_defs

suite "RFC-0005 S8c -- a user overload is walked, not modelled as the builtin (part a)":

  test "user `+` on a distinct int: reachable through the fee (was a false sxUnsat)":
    let r = pinFind(s8cPlus, tLabel("s8c_plus"))
    dump(r.errors)
    check r.status == sxSat

  test "user `<` on a distinct int: unreachable (was a false sxSat)":
    let r = pinFind(s8cLess, tLabel("s8c_less"))
    dump(r.errors)
    check r.status == sxUnsat

  test "user prefix `-` on a distinct int: reachable (was a false sxUnsat)":
    let r = pinFind(s8cNeg, tLabel("s8c_neg"))
    dump(r.errors)
    check r.status == sxSat

  test "user `+=` on a distinct int: unreachable (was a false sxSat)":
    let r = pinFind(s8cAugAssign, tLabel("s8c_augassign"))
    dump(r.errors)
    check r.status == sxUnsat

  test "user `inc` on a distinct int: unreachable (pin: already walked pre-S8c)":
    let r = pinFind(s8cInc, tLabel("s8c_inc"))
    dump(r.errors)
    check r.status == sxUnsat

  test "user `==` on an object: reachable (was a false sxUnsat)":
    let r = pinFind(s8cEq, tLabel("s8c_eq"))
    dump(r.errors)
    check r.status == sxSat

  test "`!=` resolves through the user `==` too":
    let r = pinFind(s8cNe, tLabel("s8c_ne"))
    dump(r.errors)
    check r.status == sxSat

suite "RFC-0005 S8c -- walker version pin":

  test "walker version floor >= 150 (S8c: callee resolution by symbol)":
    check parseInt(symexWalkerVersion) >= 150

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
## Part c of 6 of what was one suite (`tsymex_rfc0005_s8c_resolution`, 25 tests
## in one file: the corpus's 240 s wall-clock watchdog on the Windows legs
## killed it). Shared overloads and SUTs: `s8c_resolution_defs.nim`.
include ./s8c_resolution_defs

suite "RFC-0005 S8c -- strutils.replace is the all-occurrences model":
  test "replace is not first-occurrence (was a false sxSat)":
    let r = pinFind(s8cReplaceFirst, tLabel("s8c_replace_first"))
    dump(r.errors)
    check r.status != sxSat

  test "replace reaches the all-occurrences value":
    let r = pinFind(s8cReplaceAll, tLabel("s8c_replace_all"))
    dump(r.errors)
    check r.status == sxSat
    check r.witness[0] == "foofoo"

  test "an empty sub returns s unchanged: clean sxUnsat (was a false sxSat)":
    let r = pinFind(s8cReplaceEmptySub, tLabel("s8c_replace_empty_sub"))
    dump(r.errors)
    check r.status == sxUnsat
    check r.errors.len == 0

  test "the char overload replaces every occurrence (never a false sxSat)":
    let r = pinFind(s8cReplaceChar, tLabel("s8c_replace_char"))
    dump(r.errors)
    check r.status != sxSat

suite "RFC-0005 S8c -- controls: the builtin models still apply to builtins":

  test "builtin `+` on int keeps its model (clean sxUnsat)":
    let r = pinFind(s8cBuiltinPlus, tLabel("s8c_builtin_plus"))
    dump(r.errors)
    check r.status == sxUnsat

  test "strutils.contains keeps its model (clean sxUnsat)":
    let r = pinFind(s8cBuiltinStrContains, tLabel("s8c_builtin_strcontains"))
    dump(r.errors)
    check r.status == sxUnsat

suite "RFC-0005 S8c -- walker version pin":

  test "walker version floor >= 150 (S8c: callee resolution by symbol)":
    check parseInt(symexWalkerVersion) >= 150

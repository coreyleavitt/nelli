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
## Part d of 6 of what was one suite (`tsymex_rfc0005_s8c_resolution`, 25 tests
## in one file: the corpus's 240 s wall-clock watchdog on the Windows legs
## killed it). Shared overloads and SUTs: `s8c_resolution_defs.nim`.
include ./s8c_resolution_defs

suite "RFC-0005 S8c -- a stdlib generic over a user routine: closed by the element fragment":
  ## The SECOND-order shape: the resolved callee IS the stdlib routine, but
  ## its instantiated body reaches a USER routine (`system.==` over a tuple /
  ## object / seq compares elements with the user's `==`; `sets.contains`
  ## hashes and compares keys with the user's `hash`/`==`). Every builtin
  ## model that depends on element semantics admits only element types whose
  ## `==` cannot be user-overloaded (int64 / string / float -- a same-
  ## signature overload is an ambiguity error); every other element type is
  ## already declined, RECORDED, by the fragment. These pins hold that line:
  ## widening a fragment (say, `HashSet[distinct int]`) without resolving the
  ## element ops turns one of them into a false verdict.
  ##
  ## RFC-0016 S8cp-r (PRC-34, walker 394) walks the compiler's instance of
  ## system's `==` on a record with a non-atom field: its `fields` loop is
  ## unrolled with each field's `==` the one Nim resolved through `mixin`,
  ## a user's included. The object and tuple rows decide; each is pinned
  ## both ways against the native run (a target only the user `==` reaches,
  ## and one it refutes).

  test "system.== over an object with a user-`==` field: the user `==` decides":
    let r = pinFind(s8cFieldEq, tLabel("s8c_field_eq"))
    dump(r.errors)
    check r.status == sxSat
    check r.trusted

suite "RFC-0005 S8c -- walker version pin":

  test "walker version floor >= 150 (S8c: callee resolution by symbol)":
    check parseInt(symexWalkerVersion) >= 150

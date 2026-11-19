## RFC-0016 INT-87 (precision): the walker declines a `cstring` parameter
## (`feUnsupportedParamType`), where a `string` one is modelled. K9d-6 gave
## `pinFind` a `cstring` domain (the string domain minus the values with a NUL)
## for the day the walker takes one; until then every `cstring` call returns
## `sxUnknown` and is pinned by nothing. Recorded by K9d-12, which the plan
## asked to file it if the decline was still present on its base.
##
## The bar: a `cstring` parameter is an input (nil, or the bytes up to the
## first NUL), so each verdict below is definite and pinned natively.
## Unregistered while red (`tests/0016-allowlist/ids.txt`).
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

proc firstByte(s: cstring) =
  if s != nil and s[0] == 'a': symexTarget("hit")

proc nilOnly(s: cstring) =
  if s == nil: symexTarget("hit")

proc lenNever(s: cstring) =
  if s != nil and s.len < 0: symexTarget("hit")

suite "INT-87: a cstring parameter is an input":
  test "natively: each reachable target is reached":
    var a = "a"
    check nativeRun(firstByte(cstring(a))).hitsTarget(tLabel("hit"))
    check nativeRun(nilOnly(nil)).hitsTarget(tLabel("hit"))

  test "the walker reaches a byte of a cstring parameter":
    let r = pinFind(firstByte, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "and a nil one":
    let r = pinFind(nilOnly, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "and refutes a negative length":
    let r = pinFind(lenNever, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 444

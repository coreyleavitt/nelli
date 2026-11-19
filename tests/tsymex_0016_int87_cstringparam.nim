## RFC-0016 INT-87 (precision): the walker declined a `cstring` parameter
## (`feUnsupportedParamType`), where a `string` one is modelled. K9d-6 gave
## `pinFind` a `cstring` domain (nil, then the string domain minus the values
## with a NUL), so every verdict below is pinned natively. Recorded by K9d-12.
##
## A `cstring` is held by value: whether it is nil, and its bytes up to the
## first NUL (a string with no NUL, empty when nil). Natively (Nim 2.2.10, c
## and cpp alike): `len(nil) == 0`, `$nil == ""`; `==` compares content and
## nil equals only nil; `c[len(c)]` is the terminator '\0'; a high byte is a
## byte. `<`, `<=` and `cmp` are no content order: Nim converts both sides to
## `pointer` and compares the addresses (`zz` sorts before `ab` when its
## buffer is lower), so they decline by name, as every other address of a
## `cstring` does. A write through a `cstring`, a `cstring(s)` of a string
## the SUT holds, and a content read while the SUT may write memory the
## caller's buffer could be (a `var` or pointer-holding parameter, a global)
## decline by name: the bytes are held by value, which no write reaches.
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

proc firstByte(s: cstring) =
  if s != nil and s[0] == 'a': symexTarget("hit")

proc nilOnly(s: cstring) =
  if s == nil: symexTarget("hit")

proc isNilOnly(s: cstring) =
  if s.isNil: symexTarget("hit")

proc lenNever(s: cstring) =
  if s != nil and s.len < 0: symexTarget("hit")

proc nilLen(s: cstring) =
  if s == nil and s.len != 0: symexTarget("hit")

proc nilDollar(s: cstring) =
  if s == nil and $s == "": symexTarget("hit")

proc dollarAbc(s: cstring) =
  if $s == "abc": symexTarget("hit")

proc terminator(s: cstring) =
  if s != nil and s[s.len] != '\0': symexTarget("hit")

proc noNul(s: cstring) =
  if s != nil and s.len > 0 and s[0] == '\0': symexTarget("hit")

proc twoBytes(s: cstring) =
  if s != nil and s.len == 2 and s[1] == 'b' and s[2] == '\0':
    symexTarget("hit")

proc highByte(s: cstring) =
  if s != nil and ord(s[0]) == 255: symexTarget("hit")

proc highOf(s: cstring) =
  if s != nil and s.high == 2 and s[0] == 'q': symexTarget("hit")

proc eqContent(a, b: cstring) =
  if a == b and a != nil and a.len == 1: symexTarget("hit")

proc eqNilNonNil(a, b: cstring) =
  if a == nil and b != nil and a == b: symexTarget("hit")

proc neqNilEmpty(a, b: cstring) =
  if a == nil and b != nil and b.len == 0 and a != b: symexTarget("hit")

proc eqLit(s: cstring) =
  if s == "hi": symexTarget("hit")

proc eqLitBoth(s: cstring) =
  if s == "cs-lit" and s == "other": symexTarget("hit")

proc nilIndex(s: cstring) =
  if s == nil and s[0] == 'a': symexTarget("hit")

proc pastEnd(s: cstring) =
  if s != nil and s.len == 0 and s[1] == 'a': symexTarget("hit")

proc writeThrough(s: cstring) =
  if s != nil and s.len > 0:
    var t = s
    t[0] = 'x'
    if s[0] == 'x': symexTarget("hit")

proc addrOrder(a, b: cstring) =
  if a != nil and b != nil and a < b: symexTarget("hit")

proc fromString(s: string) =
  let c = cstring(s)
  if c[0] == 'a': symexTarget("hit")

proc aliasVar(c: cstring; s: var string) =
  if s.len > 0:
    s[0] = 'x'
    if c != nil and c[0] == 'x': symexTarget("hit")

proc aliasVarNil(c: cstring; s: var string) =
  s = "q"
  if c == nil: symexTarget("hit")

proc passOn(c: cstring): int = c.len

proc callee(s: cstring) =
  if s != nil and passOn(s) == 3: symexTarget("hit")

proc declinedByName[T](r: SymexResult[T]; what: string): bool =
  ## an unknown verdict whose errors name the cstring and `what`
  if r.status != sxUnknown: return false
  for e in r.errors:
    if "cstring" in e.msg and what in e.msg: return true

suite "INT-87: a cstring parameter is an input":
  test "natively: each reachable target is reached":
    var a = "a"
    check nativeRun(firstByte(cstring(a))).hitsTarget(tLabel("hit"))
    check nativeRun(nilOnly(nil)).hitsTarget(tLabel("hit"))
    var xx = "x"
    check nativeRun(aliasVar(cstring(xx), xx)).hitsTarget(tLabel("hit"))
    var p, q = "z"
    check nativeRun(eqContent(cstring(p), cstring(q))).hitsTarget(tLabel("hit"))

  test "the walker reaches a byte of a cstring parameter":
    let r = pinFind(firstByte, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "and a nil one, through `== nil` and `isNil`":
    for st in [pinFind(nilOnly, tLabel("hit")).status,
               pinFind(isNilOnly, tLabel("hit")).status]:
      check st == sxSat

  test "and refutes a negative length":
    let r = pinFind(lenNever, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "nil has length 0 and renders as the empty string":
    check pinFind(nilLen, tLabel("hit")).status == sxUnsat
    check pinFind(nilDollar, tLabel("hit")).status == sxSat
    check pinFind(dollarAbc, tLabel("hit")).status == sxSat

  test "the byte at the length is the terminator, and none before it":
    let t = pinFind(terminator, tLabel("hit"))
    checkpoint show(t.errors)
    check t.status == sxUnsat
    let z = pinFind(noNul, tLabel("hit"))
    checkpoint show(z.errors)
    check z.status == sxUnsat
    check pinFind(twoBytes, tLabel("hit")).status == sxSat
    let h = pinFind(highOf, tLabel("hit"))
    checkpoint show(h.errors)
    check h.status == sxSat

  test "a high byte is a byte":
    check pinFind(highByte, tLabel("hit")).status == sxSat

  test "== compares content, and nil equals only nil":
    check pinFind(eqContent, tLabel("hit")).status == sxSat
    check pinFind(eqNilNonNil, tLabel("hit")).status == sxUnsat
    check pinFind(neqNilEmpty, tLabel("hit")).status == sxSat
    check pinFind(eqLit, tLabel("hit")).status == sxSat
    check pinFind(eqLitBoth, tLabel("hit")).status == sxUnsat

  test "a cstring passed to a callee is the same value":
    check pinFind(callee, tLabel("hit")).status == sxSat

  test "an index of nil is a nil dereference, never a byte":
    check pinFind(nilIndex, tLabel("hit")).status != sxSat
    check pinFind(nilIndex, tNilAccess()).status == sxRaised

  test "an index past the terminator is undefined, never a byte":
    let r = pinFind(pastEnd, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status != sxSat
    check r.errors.named(ubArrayOutOfBounds)

  test "a write through a cstring declines by name":
    let r = pinFind(writeThrough, tLabel("hit"))
    checkpoint show(r.errors)
    check declinedByName(r, "write")

  test "< compares addresses, and declines by name":
    let r = pinFind(addrOrder, tLabel("hit"))
    checkpoint show(r.errors)
    check declinedByName(r, "address")

  test "a cstring of a string the SUT holds declines by name":
    let r = pinFind(fromString, tLabel("hit"))
    checkpoint show(r.errors)
    check declinedByName(r, "cstring(")

  test "a content read beside a writable parameter declines by name":
    let r = pinFind(aliasVar, tLabel("hit"))
    checkpoint show(r.errors)
    check declinedByName(r, "alias")
    # a nil test reads no content: the pointer is passed by value
    check pinFind(aliasVarNil, tLabel("hit")).status == sxSat

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 448

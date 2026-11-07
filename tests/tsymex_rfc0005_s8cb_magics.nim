## RFC-0005 S8cb, item 5 -- the system magics a walk can reach and no parser arm
## modelled, part 1: the integer family. The unsigned operators `+% -% *% /% %%
## <% <=%` and `ashr`, `ord(bool)`, `chr`, `high`/`low` of a value and unary `+`
## declined or failed the compile. Every expected value is checked against
## native Nim in the first test.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs:
    if e.severity != sevHint: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

template c(name: untyped, want: SymexStatusKind, body: untyped) {.dirty.} =
  proc name(x: int, y: int) =
    body
  test astToStr(name):
    let r = symexFind(name, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == want

type
  E = enum ea, eb, ec
  Sub = range[3 .. 9]

suite "RFC-0005 S8cb magics: the walker floor":
  test "symexWalkerVersion is at least 243":
    check parseInt(symexWalkerVersion) >= 243

suite "RFC-0005 S8cb magics: native Nim":
  test "the expected values":
    var a = high(int); var b = 1
    check a +% b == low(int)
    a = low(int)
    check a -% b == high(int)
    a = high(int); b = 2
    check a *% b == -2
    a = -2
    check a /% b == high(int)
    a = -1; b = 10
    check a %% b == 5
    a = -1; b = 1
    check not (a <% b) and b <% a and not (a <=% b) and b <=% a
    var i8 = 127'i8; var j8 = 1'i8
    check i8 +% j8 == -128'i8
    i8 = -1'i8; j8 = 2'i8
    check i8 /% j8 == 127'i8
    check ashr(-8, 1) == -4 and ashr(-1, 1) == -1 and ashr(8, 1) == 4
    i8 = -8'i8
    check ashr(i8, 1) == -4'i8
    var t = true; var f = false
    check ord(t) == 1 and ord(f) == 0
    var n = 97
    check chr(n) == 'a'
    n = 300
    expect RangeDefect: discard chr(n)
    n = -1
    expect RangeDefect: discard chr(n)
    var i32 = 5'i32; var ch = 'a'; var en = eb; var sb: Sub = 4
    check high(a) == high(int) and low(a) == low(int)
    check high(i32) == high(int32) and low(i8) == -128'i8
    check high(ch) == '\255' and low(ch) == '\0'
    check high(en) == ec and low(en) == ea
    check high(sb) == 9 and low(sb) == 3
    check +a == a

suite "RFC-0005 S8cb magics: unsigned operators":
  c(addw, sxSat): (if x == 1 and x +% y == 3 and y == 2: symexTarget("t"))
  c(addwrap, sxSat): (if x == high(int) and y == 1 and x +% y == low(int): symexTarget("t"))
  c(addwrapu, sxUnsat): (if x == high(int) and y == 1 and x +% y != low(int): symexTarget("t"))
  c(subwrap, sxSat): (if x == low(int) and y == 1 and x -% y == high(int): symexTarget("t"))
  c(subwrapu, sxUnsat): (if x == low(int) and y == 1 and x -% y != high(int): symexTarget("t"))
  c(mulwrap, sxSat): (if x == high(int) and y == 2 and x *% y == -2: symexTarget("t"))
  c(mulwrapu, sxUnsat): (if x == high(int) and y == 2 and x *% y != -2: symexTarget("t"))
  c(divu, sxSat): (if x == -2 and y == 2 and x /% y == high(int): symexTarget("t"))
  c(divuu, sxUnsat): (if x == -2 and y == 2 and x /% y != high(int): symexTarget("t"))
  c(modu, sxSat): (if x == -1 and y == 10 and x %% y == 5: symexTarget("t"))
  c(moduu, sxUnsat): (if x == -1 and y == 10 and x %% y != 5: symexTarget("t"))
  c(ltu, sxSat): (if x == -1 and y == 1 and y <% x: symexTarget("t"))
  c(ltuu, sxUnsat): (if x == -1 and y == 1 and x <% y: symexTarget("t"))
  c(leu, sxSat): (if x == -1 and y == 1 and y <=% x: symexTarget("t"))
  c(leuu, sxUnsat): (if x == -1 and y == 1 and x <=% y: symexTarget("t"))
  c(addlit, sxUnsat): (if x == high(int) and x +% 1 != low(int): symexTarget("t"))
  c(add8, sxSat):
    let a = int8(x and 127)
    if a == 127'i8 and a +% 1'i8 == -128'i8: symexTarget("t")
  c(add8u, sxUnsat):
    let a = int8(x and 127)
    if a == 127'i8 and a +% 1'i8 != -128'i8: symexTarget("t")
  c(div8, sxSat):
    let a = int8(x and 3) - 4'i8
    if a == -1'i8 and a /% 2'i8 == 127'i8: symexTarget("t")
  ## RFC-0016 W1-d1b (rule a): an unsigned `/%` or `%%` by zero is undefined
  ## behaviour (`ubUnsignedDivZero`, a halt), not a caught `DivByZeroDefect`;
  ## the label behind the `except` is no longer reached, and the verdict is
  ## `sxUnknown` naming the halt.
  c(divzero, sxUnknown):
    try:
      if y == 0:
        discard x /% y
    except DivByZeroDefect:
      symexTarget("t")
  c(modzero, sxUnknown):
    try:
      if y == 0:
        discard x %% y
    except DivByZeroDefect:
      symexTarget("t")
  test "the unsigned zero divisors name the halt (ubUnsignedDivZero)":
    for r in [symexFind(divzero, tLabel("t")), symexFind(modzero, tLabel("t"))]:
      var halted = false
      for e in r.errors:
        if e.kind == ubUnsignedDivZero: halted = true
      check halted
      check not r.trusted
  c(callform, sxUnsat): (if x == -1 and y == 1 and `<%`(x, y): symexTarget("t"))

suite "RFC-0005 S8cb magics: ashr, ord, chr, unary plus":
  c(ashrneg, sxSat): (if x == -8 and ashr(x, 1) == -4: symexTarget("t"))
  c(ashrnegu, sxUnsat): (if x == -8 and ashr(x, 1) != -4: symexTarget("t"))
  c(ashrpos, sxUnsat): (if x == 8 and ashr(x, 1) != 4: symexTarget("t"))
  c(ashr8, sxUnsat):
    let a = int8(x and 7) - 8'i8
    if a == -8'i8 and ashr(a, 1) != -4'i8: symexTarget("t")
  c(ordtrue, sxSat): (if ord(x > 0) == 1 and x == 1: symexTarget("t"))
  c(ordtrueu, sxUnsat): (if ord(x > 0) == 1 and x == 0: symexTarget("t"))
  c(ordfalseu, sxUnsat): (if ord(x > 0) == 0 and x == 1: symexTarget("t"))
  c(chrok, sxSat): (if chr(x) == 'a' and x == 97: symexTarget("t"))
  c(chroku, sxUnsat): (if x == 98 and chr(x) == 'a': symexTarget("t"))
  c(chrhigh, sxSat):
    try:
      if x == 300: discard chr(x)
    except RangeDefect:
      symexTarget("t")
  c(chrlow, sxSat):
    try:
      if x == -1: discard chr(x)
    except RangeDefect:
      symexTarget("t")
  c(chrinrangeu, sxUnsat):
    try:
      if x == 200: discard chr(x)
    except RangeDefect:
      symexTarget("t")
  c(uplus, sxSat): (if +x == 2 and x == 2: symexTarget("t"))
  c(uplusu, sxUnsat): (if +x == 2 and x == 3: symexTarget("t"))

suite "RFC-0005 S8cb magics: high and low of a value":
  c(highint, sxSat): (if high(x) == x and x > 0: symexTarget("t"))
  c(highintu, sxUnsat): (if high(x) != 9223372036854775807: symexTarget("t"))
  c(lowintu, sxUnsat): (if x == 0 and low(x) != low(int): symexTarget("t"))
  c(high32u, sxUnsat):
    let a = int32(x and 7)
    if high(a) != 2147483647'i32: symexTarget("t")
  c(low8u, sxUnsat):
    let a = int8(x and 7)
    if low(a) != -128'i8: symexTarget("t")
  c(highcharu, sxUnsat):
    let a = if x > 0: 'a' else: 'b'
    if high(a) != '\255': symexTarget("t")
  c(highenum, sxSat):
    let a = if x > 0: ea else: eb
    if high(a) == ec and low(a) == ea: symexTarget("t")
  c(highenumu, sxUnsat):
    let a = if x > 0: ea else: eb
    if high(a) != ec: symexTarget("t")
  c(highrangeu, sxUnsat):
    let a: Sub = if x > 0: 3 else: 4
    if high(a) != 9 or low(a) != 3: symexTarget("t")

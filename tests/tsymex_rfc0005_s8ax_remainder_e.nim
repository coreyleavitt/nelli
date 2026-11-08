## RFC-0005 (soundness channels) slice S8ax -- S8as's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 7 of 9 of this suite, with
## `tsymex_rfc0005_s8ax_remainder`, `tsymex_rfc0005_s8ax_remainder2`,
## `tsymex_rfc0005_s8ax_remainder3`, `tsymex_rfc0005_s8ax_remainder_b`,
## `tsymex_rfc0005_s8ax_remainder_c`, `tsymex_rfc0005_s8ax_remainder_d`,
## `tsymex_rfc0005_s8ax_remainder_f`, `tsymex_rfc0005_s8ax_remainder_g`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 132 s).

import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "s8ax_remainder_e")

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template clean(fn: typed, lbl: string, want: SymexStatusKind) =
  ## The verdict, with nothing recorded at all.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0

type S8axRR = ref object
  a: int

# ---- (6) a closure applied away from the frame that built it ----------------
#
# DECLINED before S8ax (`ceCaptureByRefUnmodelled`, every case below): a
# closure's by-reference captures were read as they stood at construction
# and its writes were dropped wherever it ran outside its own frame. Nim
# keeps them in a heap env the frame and the closure share; the walk keeps
# each in an env cell threaded through every call as a global is.
# Expected values probed on c and cpp.

proc s8axCounter(start: int): proc(): int =
  var c = start
  result = proc(): int =
    c += 1
    c

proc s8axApply(f: proc(): int): int = f()

proc s8axApplyRaise(f: proc(): int): int =
  discard f()
  raise newException(ValueError, "boom")

proc s8axApplyIf(f: proc(): int; c: bool): int =
  if c: f() else: 0

proc s8axReadVar(a: var int; f: proc(): int): int =
  discard f()
  a

proc sutCloEscaped(v: int) =
  symexAssume(v > -100 and v < 100)
  let f = s8axCounter(v)
  discard f()
  let b = f()
  if b == v + 2: symexTarget("ok")
  if b != v + 2: symexTarget("bad")

proc sutCloTwoEnvs(v: int) =
  symexAssume(v > -100 and v < 100)
  let f = s8axCounter(v)
  let h = s8axCounter(v)
  discard f()
  let b = h()
  if b == v + 1: symexTarget("ok")
  if b != v + 1: symexTarget("bad")

proc sutCloPassed(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  x = 50
  let r = s8axApply(f)
  if r == 51 and x == 51: symexTarget("ok")
  if r != 51 or x != 51: symexTarget("bad")

proc sutCloMixed(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  discard f()
  discard s8axApply(f)
  discard f()
  let r = s8axApply(f) + x
  if r == 2 * v + 8: symexTarget("ok")
  if r != 2 * v + 8: symexTarget("bad")

proc sutCloRaise(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  try:
    discard s8axApplyRaise(f)
  except ValueError:
    if x == v + 1: symexTarget("ok")
    if x != v + 1: symexTarget("bad")

proc sutCloBranch(v: int) =
  symexAssume(v > -100 and v < 100)
  let f = s8axCounter(v)
  discard s8axApplyIf(f, v > 0)
  let b = f()
  if v > 0 and b == v + 2: symexTarget("ok")
  if (v > 0 and b != v + 2) or (v <= 0 and b != v + 1): symexTarget("bad")

proc sutCloLoop(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  var i = 0
  while i < 3:
    discard s8axApply(f)
    inc i
  if x == v + 3: symexTarget("ok")
  if x != v + 3: symexTarget("bad")

proc sutCloByAddr(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  let r = s8axReadVar(x, f)
  if r == v + 1: symexTarget("ok")

suite "RFC-0005 S8ax (6): a closure applied away from its frame":
  test "a closure returned from its frame keeps its env":
    clean(sutCloEscaped, "ok", sxSat)
    clean(sutCloEscaped, "bad", sxUnsat)
    clean(sutCloTwoEnvs, "ok", sxSat)
    clean(sutCloTwoEnvs, "bad", sxUnsat)
  test "a closure a callee applies writes the frame's variable":
    clean(sutCloPassed, "ok", sxSat)
    clean(sutCloPassed, "bad", sxUnsat)
    clean(sutCloMixed, "ok", sxSat)
    clean(sutCloMixed, "bad", sxUnsat)
    clean(sutCloLoop, "ok", sxSat)
    clean(sutCloLoop, "bad", sxUnsat)
  test "the write survives a raise and a branch":
    clean(sutCloRaise, "ok", sxSat)
    clean(sutCloRaise, "bad", sxUnsat)
    clean(sutCloBranch, "ok", sxSat)
    clean(sutCloBranch, "bad", sxUnsat)
  test "a capture passed by address while the closure runs declines":
    pinDecline(sutCloByAddr, declKey, ceCaptureByRefUnmodelled, tLabel("ok"), "passed by address")

type S8axPair = object
  a, b: int

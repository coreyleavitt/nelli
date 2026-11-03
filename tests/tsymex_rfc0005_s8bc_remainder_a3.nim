## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder, part a: getOrDefault, inlined-iterator parameter conversions, seq[char] / seq[enum]
## witnesses, non-operator {.borrow.} routines (items 1, 8, 9, 2).
## RFC-0005 S8bl (item 5): split out of `tsymex_rfc0005_s8bc_remainder`,
## whose compile alone took 77 s on the Windows leg (budget: 60 s a file).
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8bc_remainder_a`, `tsymex_rfc0005_s8bc_remainder_a2`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 69 s).

import std/[unittest, strutils, sequtils, tables, sets, hashes]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

template replays(call: untyped; label: string) =
  ## The witness is typed (the parameter was not demoted) and replays.
  when compiles(call):
    check reproduces(call, label)
  else:
    checkpoint "the witness of `" & astToStr(call) & "` is not typed"
    check false

# ---- (2) a non-operator {.borrow.} routine ----------------------------------
#
# RFC-0005 S8bc: a borrowed routine has no body (its `getImpl` body is the
# base routine's symbol); `f(a)` is the base routine on `T(a)`, rewrapped
# when `f` returns the distinct. It was walked as a user routine whose body,
# that bare symbol, declined (`feUnsupportedStmtKind`).

type
  BSq = distinct seq[int]
  BM = distinct int
  BName = distinct string
  BBox = object
    w: int
  BDBox = distinct BBox

proc len(d: BSq): int {.borrow.}
proc abs(m: BM): BM {.borrow.}
proc `$`(m: BM): string {.borrow.}
proc len(n: BName): int {.borrow.}
# Full arity: Nim 2.2.10 crashes compiling `proc inc(m: var BM) {.borrow.}`.
proc inc(m: var BM, y: int) {.borrow.}
proc add(d: var BSq, x: int) {.borrow.}
proc area(b: BBox): int = b.w * b.w
proc area(d: BDBox): int {.borrow.}

proc brLen(d: BSq) =
  if d.len == 2: symexTarget("br_len")
  if d.len < 0: symexTarget("br_len_dead")

proc brAbs(m: BM) =
  if int(m) > -100 and int(m) < 100:
    if int(abs(m)) == 5 and int(m) < 0: symexTarget("br_abs")
    if int(abs(m)) < 0: symexTarget("br_abs_dead")

proc brStr(m: BM) =
  if $m == "42": symexTarget("br_str")

proc brStrLen(n: BName) =
  if n.len == 3: symexTarget("br_strlen")

proc brInc(x: int) =
  if x > 100 or x < -100: return
  var m = BM(x)
  inc(m, 2)
  if int(m) == 7: symexTarget("br_inc")
  if int(m) == x: symexTarget("br_inc_dead")

proc brAdd(x: int) =
  var d = BSq(@[1])
  d.add x
  if d.len == 2 and seq[int](d)[1] == 9: symexTarget("br_add")
  if d.len != 2: symexTarget("br_add_dead")

proc brUser(d: BDBox) =
  if BBox(d).w < 100 and BBox(d).w > -100:
    if area(d) == 49: symexTarget("br_user")
    if area(d) < 0: symexTarget("br_user_dead")

suite "S8bc (2): a non-operator {.borrow.} routine":
  test "len of a distinct seq":
    let r = symexFind(brLen, tLabel("br_len"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(brLen(r.witness[0]), "br_len")
    let d = symexFind(brLen, tLabel("br_len_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "abs of a distinct int, rewrapped":
    let r = symexFind(brAbs, tLabel("br_abs"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(brAbs(r.witness[0]), "br_abs")
    let d = symexFind(brAbs, tLabel("br_abs_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "$ of a distinct int":
    let r = symexFind(brStr, tLabel("br_str"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(brStr(r.witness[0]), "br_str")

  test "len of a distinct string":
    let r = symexFind(brStrLen, tLabel("br_strlen"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(brStrLen(r.witness[0]), "br_strlen")

  test "a var-parameter borrow (inc)":
    let r = symexFind(brInc, tLabel("br_inc"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check r.witness[0] == 5
    let d = symexFind(brInc, tLabel("br_inc_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a var-parameter borrow on a distinct seq (add)":
    let r = symexFind(brAdd, tLabel("br_add"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check r.witness[0] == 9
    let d = symexFind(brAdd, tLabel("br_add_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a borrow of a user routine":
    let r = symexFind(brUser, tLabel("br_user"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(brUser, tLabel("br_user_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat


suite "S8bc: walker version floor":
  test "walker version floor >= 203":
    check parseInt(symexWalkerVersion) >= 203

## RFC-0005 slice S8cn -- a `lent` `for` loop, and a `let` over a container, with
## a write during the variable's life.
##
## The walk binds a loop variable or a `let` to the value read where it stands.
## Natively `items` over a seq or an openArray, and a Table's `values`, yield the
## element's own memory, so a write to the container in the body is seen through
## the variable. `let c = s` shares under `--mm:refc` always and under orc or arc
## when cursor inference proves it, which turns on the whole routine:
## `tsymex_rfc0005_s8cn_lentnative` pins that, on each memory manager. Both are
## declined when the body (a callee, a pointer, a global alias included) may
## write; the exact model is for RFC-0016. The forms Nim copies on every setting
## stay decided: scalar elements through `pairs`, an array's `items`, a Table's
## `pairs`. Every label runs natively.
##
## RFC-0005 S8cm: part 1 of 6 of this suite, with `tsymex_rfc0005_s8cn_lent_b`,
## `tsymex_rfc0005_s8cn_lent_c`, `tsymex_rfc0005_s8cn_lent_d`,
## `tsymex_rfc0005_s8cn_lent_e`, `tsymex_rfc0005_s8cn_lent_f`. Split so that
## each part compiles and runs in under 60 s on the Windows legs (the whole
## file took 95 s).
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

const ns = [-5, -1, 0, 1, 3, 4, 7, 12, 49, 51]

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template declined(fn: typed; lbl: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxUnknown
    check "memory" in show(r.errors)

template nativeSees(fn: typed; live, dead: static string) =
  block:
    var l = false
    var d = false
    for n in ns:
      if n == 99: continue
      let h = hits(fn(n))
      if live in h: l = true
      if dead in h: d = true
    check l
    check not d

template guardN(): untyped {.dirty.} =
  if n > 1000 or n < -1000 or n == 99: return

var gs: seq[int]
var gp: ptr seq[int]

proc wr(v: var seq[int]) = v[0] = 99
proc wg() = gs[0] = 99
proc wgDeep() = wg()
proc wp() = gp[][0] = 99

# ---- seq, `items`: the element's memory ---------------------------------------

proc iDirect(n: int) =
  guardN()
  var s = @[n]
  for x in s:
    s[0] = 99
    if x == 99: symexTarget("id_new")
    if x == n: symexTarget("id_old")
proc iVarCallee(n: int) =
  guardN()
  var s = @[n]
  for x in s:
    wr(s)
    if x == 99: symexTarget("iv_new")
    if x == n: symexTarget("iv_old")
proc iGlobalName(n: int) =
  guardN()
  gs = @[n]
  for x in gs:
    gs[0] = 99
    if x == 99: symexTarget("in_new")
    if x == n: symexTarget("in_old")
proc iGlobalCallee(n: int) =
  guardN()
  gs = @[n]
  for x in gs:
    wgDeep()
    if x == 99: symexTarget("ig_new")
    if x == n: symexTarget("ig_old")
proc iPtrLocal(n: int) =
  guardN()
  var s = @[n]
  let p = addr s
  for x in s:
    p[][0] = 99
    if x == 99: symexTarget("ip_new")
    if x == n: symexTarget("ip_old")
proc iPtrGlobal(n: int) =
  guardN()
  gs = @[n]
  gp = addr gs
  for x in gs:
    wp()
    if x == 99: symexTarget("ipg_new")
    if x == n: symexTarget("ipg_old")
proc iElemPtr(n: int) =
  guardN()
  var s = @[n]
  let p = addr s[0]
  for x in s:
    p[] = 99
    if x == 99: symexTarget("ie_new")
    if x == n: symexTarget("ie_old")
proc iFormal(a: var seq[int]; n: int) =
  for x in a:
    a[0] = 99
    if x == 99: symexTarget("if_new")
    if x == n: symexTarget("if_old")
proc iFormalCall(n: int) =
  guardN()
  var s = @[n]
  iFormal(s, n)
proc oaLoop(a: openArray[int]; n: int) =
  for x in a:
    gs[0] = 99
    if x == 99: symexTarget("oa_new")
    if x == n: symexTarget("oa_old")
proc iOpenArray(n: int) =
  guardN()
  gs = @[n]
  oaLoop(gs, n)
proc twoInBody(a, b: var int) =
  a = 99
  if b == 99: symexTarget("tb_new")
  else: symexTarget("tb_old")
proc iTwoInBody(n: int) =
  guardN()
  var s = @[n]
  twoInBody(s[0], s[0])

suite "S8cn: seq `items` with a write in the body":
  test "native: the element's memory":
    nativeSees(iDirect, "id_new", "id_old")
    nativeSees(iVarCallee, "iv_new", "iv_old")
    nativeSees(iGlobalName, "in_new", "in_old")
    nativeSees(iGlobalCallee, "ig_new", "ig_old")
    nativeSees(iPtrLocal, "ip_new", "ip_old")
    nativeSees(iPtrGlobal, "ipg_new", "ipg_old")
    nativeSees(iElemPtr, "ie_new", "ie_old")
    nativeSees(iFormalCall, "if_new", "if_old")
    nativeSees(iOpenArray, "oa_new", "oa_old")
  test "declines":
    declined(iDirect, "id_new"); declined(iDirect, "id_old")
    declined(iVarCallee, "iv_new"); declined(iVarCallee, "iv_old")
    declined(iGlobalName, "in_new"); declined(iGlobalName, "in_old")
    declined(iGlobalCallee, "ig_new"); declined(iGlobalCallee, "ig_old")
    declined(iPtrLocal, "ip_new"); declined(iPtrLocal, "ip_old")
    declined(iPtrGlobal, "ipg_new"); declined(iPtrGlobal, "ipg_old")
    declined(iElemPtr, "ie_new"); declined(iElemPtr, "ie_old")
    declined(iFormalCall, "if_new"); declined(iFormalCall, "if_old")
    declined(iOpenArray, "oa_new"); declined(iOpenArray, "oa_old")
  test "a target in the body of a declined call declines":
    nativeSees(iTwoInBody, "tb_new", "tb_old")
    check symexFind(iTwoInBody, tLabel("tb_new")).status == sxUnknown
    check symexFind(iTwoInBody, tLabel("tb_old")).status == sxUnknown

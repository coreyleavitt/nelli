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
## RFC-0005 S8cm: part 5 of 6 of this suite, with `tsymex_rfc0005_s8cn_lent`,
## `tsymex_rfc0005_s8cn_lent_b`, `tsymex_rfc0005_s8cn_lent_c`,
## `tsymex_rfc0005_s8cn_lent_d`, `tsymex_rfc0005_s8cn_lent_f`. Split so that
## each part compiles and runs in under 60 s on the Windows legs (the whole
## file took 95 s).
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

template declined(fn: typed; lbl: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxUnknown
    check "memory" in show(r.errors)

template guardN(): untyped {.dirty.} =
  if n > 1000 or n < -1000 or n == 99: return

var gs: seq[int]
var gt: Table[string, int]
var gstr: string
type Obj2 = object
  a: int
  b: seq[int]

proc wr(v: var seq[int]) = v[0] = 99
proc wg() = gs[0] = 99
proc wt() = gt["a"] = 99

# ---- `let` over a container: the setting's choice ------------------------------

proc lGlobalCallee(n: int) =
  guardN()
  gs = @[n]
  let c = gs
  wg()
  if c[0] == 99: symexTarget("lg_a")
  if c[0] == n: symexTarget("lg_b")
proc lGlobalName(n: int) =
  guardN()
  gs = @[n]
  let c = gs
  gs[0] = 99
  if c[0] == 99: symexTarget("ln_a")
  if c[0] == n: symexTarget("ln_b")
proc lLocal(n: int) =
  guardN()
  var s = @[n]
  let c = s
  s[0] = 99
  if c[0] == 99: symexTarget("ll_a")
  if c[0] == n: symexTarget("ll_b")
proc lVarCallee(n: int) =
  guardN()
  var s = @[n]
  let c = s
  wr(s)
  if c[0] == 99: symexTarget("lv_a")
  if c[0] == n: symexTarget("lv_b")
proc lPtr(n: int) =
  guardN()
  var s = @[n]
  let p = addr s
  let c = s
  p[][0] = 99
  if c[0] == 99: symexTarget("lp_a")
  if c[0] == n: symexTarget("lp_b")
proc lTable(n: int) =
  guardN()
  gt = {"a": n}.toTable
  let c = gt
  wt()
  if c["a"] == 99: symexTarget("lt_a")
  if c["a"] == n: symexTarget("lt_b")
proc lField(n: int) =
  guardN()
  var o = Obj2(a: 1, b: @[n])
  let c = o.b
  o.b[0] = 99
  if c[0] == 99: symexTarget("lf_a")
  if c[0] == n: symexTarget("lf_b")
proc lString(n: int) =
  guardN()
  gstr = "ab"
  let c = gstr
  gstr[0] = 'z'
  if c[0] == 'z' and n == 0: symexTarget("ls_a")
  if c[0] == 'a' and n == 0: symexTarget("ls_b")
proc lObject(n: int) =
  guardN()
  var o = Obj2(a: 1, b: @[n])
  let c = o
  o.b[0] = 99
  if c.b[0] == 99: symexTarget("lo_a")
  if c.b[0] == n: symexTarget("lo_b")

suite "S8cn: `let` over a container with a write in its life":
  test "declines":
    declined(lGlobalCallee, "lg_a"); declined(lGlobalCallee, "lg_b")
    declined(lGlobalName, "ln_a"); declined(lGlobalName, "ln_b")
    declined(lLocal, "ll_a"); declined(lLocal, "ll_b")
    declined(lVarCallee, "lv_a"); declined(lVarCallee, "lv_b")
    declined(lPtr, "lp_a"); declined(lPtr, "lp_b")
    declined(lTable, "lt_a"); declined(lTable, "lt_b")
    declined(lField, "lf_a"); declined(lField, "lf_b")
    declined(lString, "ls_a"); declined(lString, "ls_b")
    declined(lObject, "lo_a"); declined(lObject, "lo_b")

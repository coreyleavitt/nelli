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
from ./s8cu_helpers import named, pinDecline
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/admission

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

template declined(fn: typed; lbl: static string, kinds: set[SymexErrorKind]) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxUnknown
    for k in kinds: check r.errors.named(k)
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
    declined(lGlobalCallee, "lg_a", {feUnsupportedOp}); declined(lGlobalCallee, "lg_b", {feUnsupportedOp})
    declined(lGlobalName, "ln_a", {feUnsupportedOp}); declined(lGlobalName, "ln_b", {feUnsupportedOp})
    declined(lLocal, "ll_a", {feUnsupportedOp}); declined(lLocal, "ll_b", {feUnsupportedOp})
    declined(lVarCallee, "lv_a", {feUnsupportedOp}); declined(lVarCallee, "lv_b", {feUnsupportedOp})
    declined(lPtr, "lp_a", {feUnsupportedOp}); declined(lPtr, "lp_b", {feUnsupportedOp})
    # `{"a": n}.toTable` used to decline as well, with feUnsupportedStmtKind
    # on its `for key, val in items(pairs)` (two loop variables over a tuple
    # element). INT-75 reads that destructuring as the flat form, so the walk
    # now runs through `toTable` and the one decline left is the accurate one:
    # whether `let c = gt` shares the Table or copies it depends on the memory
    # manager (`tsymex_rfc0005_s8cn_lentnative`), and `wt` writes it by name.
    # The excluded kind keeps the ratchet: the loop decline may not return.
    pinDecline(lTable, cellKey(faCallShape, "letShared/globalTableWrittenByCallee"),
      feUnsupportedOp, tLabel("lt_a"), needle = "written by `wt`, which reaches it by name",
      excluding = {feUnsupportedStmtKind})
    pinDecline(lTable, cellKey(faCallShape, "letShared/globalTableWrittenByCallee"),
      feUnsupportedOp, tLabel("lt_b"), needle = "written by `wt`, which reaches it by name",
      excluding = {feUnsupportedStmtKind})
    declined(lField, "lf_a", {feUnsupportedOp}); declined(lField, "lf_b", {feUnsupportedOp})
    declined(lString, "ls_a", {feUnsupportedOp}); declined(lString, "ls_b", {feUnsupportedOp})
    declined(lObject, "lo_a", {feUnsupportedOp}); declined(lObject, "lo_b", {feUnsupportedOp})

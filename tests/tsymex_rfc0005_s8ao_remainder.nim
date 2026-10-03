## RFC-0005 (soundness channels) slice S8ao -- S8aj's "Different mechanisms,
## reported and not fixed here" remainder.
##
## This slice closes:
##   (1) `add` on a dotted seq field (`o.s.add v`) was N49 `feUnsupportedOp`
##       while `s.add v` on a local seq and `o.s = @[v]` were already
##       modelled. `add` through a field path is now modelled: it reuses the
##       SAME field-write primitive the plain assignment `<fieldPath> = v`
##       already uses for the lvalue shape (S8p's value-field rebuild for a
##       value tuple/object step -- a base `o.s.add v` and a nested
##       `a.b.s.add v` both take it -- the R6 ref-object field-deref-write
##       for a `ref`/`ptr` step). `del`/`insert`/`incl`/`excl`/`[]=` on a
##       dotted field are UNCHANGED (still N49 -- S8aj's remainder named
##       `add` only), and so is `add` on a dotted STRING field (the scope
##       was the seq case).
##   (2) `zeroValueForType` still returns `nil` for `itUninterp` -- proven
##       the only sound answer, not widened. Every `itUninterp` reaching it
##       is one of three `classifyType` placeholder prefixes
##       (`__ownership:*`, `__closure`, `__unsupported:<X>`), and none has a
##       fabricable sound zero (see the proc's own doc comment,
##       `dsl_parser.nim`, for the per-prefix argument). The decline is
##       pinned here for all three, reached through an uninitialized local
##       var -- the one call site this `nil` visibly degrades.
##
## RFC-0005 S8ap (S8ao's remainder) moved several of these pins forward:
## `del`/`insert`/`incl`/`excl`/`[]=` and `add` on a dotted STRING field take
## the field-path rebuild too, a ref object's seq field is a heap cell (so
## `p.s.add v` is modelled), and the uninitialised `itUninterp` local
## declines with its placeholder's own kind instead of
## `feUnsupportedStmtKind`. The tests below say which slice each expectation
## dates from; `tests/tsymex_rfc0005_s8ap_remainder.nim` pins S8ap itself.
import std/[unittest, strutils, sequtils, atomics]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

# ---- (1) `add` through a field path -----------------------------------------

type
  SQ = object
    s: seq[int]
    n: int
  Inner = object
    s: seq[int]
    n: int
  Outer = object
    b: Inner
  NM = object
    name: string
  RNode = ref object
    s: seq[int]
    n: int

proc zDotAdd(v: int) =
  ## The base case: `o.s.add v` on a value object's seq field.
  var o: SQ
  o.s.add v
  if o.s.len == 1 and o.s[0] == 7 and o.n == 0: symexTarget("dotadd")
  if o.s.len != 1 or o.n != 0: symexTarget("dotadd_dead")

proc zNestedDotAdd(v: int) =
  ## A nested field path: `a.b.s.add v`.
  var a: Outer
  a.b.s.add v
  if a.b.s.len == 1 and a.b.s[0] == 9 and a.b.n == 0: symexTarget("nestadd")
  if a.b.s.len != 1 or a.b.n != 0: symexTarget("nestadd_dead")

proc zTwoAdds(v, w: int) =
  ## Two `.add` calls in sequence read the already-appended field, not a
  ## stale copy (proves the rebuild reads the CURRENT value each time, not
  ## the local's value at proc entry).
  var o: SQ
  o.s.add v
  o.s.add w
  if o.s.len == 2 and o.s[0] == 2 and o.s[1] == 3: symexTarget("twoadd")
  if o.s.len != 2: symexTarget("twoadd_dead")

proc zDelStillDeclines(v: int) =
  ## `del`/`insert`/`incl`/`excl`/`[]=` on a dotted field were UNCHANGED by
  ## S8ao (it named `add` only); RFC-0005 S8ap models them.
  var o: SQ
  o.s.add v
  o.s.del(0)
  if o.s.len == 0: symexTarget("delstill")

proc zStrDotAddStillDeclines(c: int) =
  ## `add` on a dotted STRING field was UNCHANGED by S8ao -- the scope was
  ## the seq case. RFC-0005 S8ap routes it through `iekStrConcat`.
  var o: NM
  o.name.add(char(c))
  if o.name.len == 1: symexTarget("strdotadd")

proc zRefDotAdd(p: RNode, v: int) =
  ## A ref/ptr object's field. At S8ao a ref-object field of a COMPOUND sort
  ## (seq) had no field-split heap representation -- `p.s = @[...]` alone
  ## raised `seUnsupportedCompoundSortLeaf` -- and this pinned only that
  ## `.add` shared THAT fate instead of N49's `feUnsupportedOp`. RFC-0005
  ## S8ap gave the field a leaf-split heap cell, so it is now modelled.
  p.s = @[]
  p.s.add v
  if p.s.len == 1: symexTarget("refadd")

suite "S8ao (1): add through a field path":

  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "a base dotted seq field (o.s.add v)":
    ## RED at the base: N49 `feUnsupportedOp`, "dotted-field lvalue
    ## mutation `add` unsupported".
    let r = run(zDotAdd, "dotadd", sxSat)
    if r.status == sxSat: check r.witness[0] == 7
    discard run(zDotAdd, "dotadd_dead", sxUnsat)

  test "a nested dotted seq field (a.b.s.add v)":
    let r = run(zNestedDotAdd, "nestadd", sxSat)
    if r.status == sxSat: check r.witness[0] == 9
    discard run(zNestedDotAdd, "nestadd_dead", sxUnsat)

  test "two adds read the freshly-rebuilt field, not a stale copy":
    let r = run(zTwoAdds, "twoadd", sxSat)
    if r.status == sxSat: check r.witness[0] == 2 and r.witness[1] == 3
    discard run(zTwoAdds, "twoadd_dead", sxUnsat)

  test "del on a dotted field: modelled since RFC-0005 S8ap (S8ao left it N49)":
    let r = run(zDelStillDeclines, "delstill", sxSat)
    check not r.errors.anyIt("N49" in it.msg)

  test "add on a dotted STRING field: modelled since RFC-0005 S8ap (S8ao left it N49)":
    let r = run(zStrDotAddStillDeclines, "strdotadd", sxSat)
    check not r.errors.anyIt("N49" in it.msg)

  test "a ref object's seq field: add now shares fate with plain assignment":
    ## Different mechanism, not fixed here (see the RFC's S8ao notes): a
    ## ref-object field of a COMPOUND sort (seq) has no field-split heap
    ## representation at all -- `p.s = @[...]` alone already raises
    ## `seUnsupportedCompoundSortLeaf` ("no single-leaf Z3 sort
    ## representation"), independent of this slice (R3+ territory, per the
    ## engine's own message). Before S8ao, `p.s.add v` hit N49's
    ## `feUnsupportedOp` FIRST, one site earlier, hiding this. The field-path
    ## routing this slice adds means `.add` now reaches the SAME classified
    ## decline a plain `p.s = @[...]` already hits for the identical lvalue
    ## -- proving the routing is real (it shares the real primitive, not a
    ## parallel one) -- rather than being blocked by its own narrower N49
    ## catch-all. This pins that it is no longer N49 specifically.
    ## RFC-0005 S8ap: the field is a leaf-split heap cell now, so the
    ## append is modelled outright.
    let r = symexFind(zRefDotAdd, tLabel("refadd"))
    checkpoint $r.status & " " & show(r.errors)
    check not r.errors.anyIt(it.kind == feUnsupportedOp and "N49" in it.msg)
    check r.status == sxSat
    check not r.errors.hasKind(seUnsupportedCompoundSortLeaf)

  test "symexWalkerVersion >= 181":
    check parseInt(symexWalkerVersion) >= 181

# ---- (2) itUninterp has no zero -- proven, not widened ----------------------

type
  # RFC-0005 S8bn classifies a generic object instance (`G[int]`); a generic
  # CASE object is still unrecognised, so it stands in for the placeholder.
  Weird[T] = object
    case k: bool
    of true: x: T
    of false: discard

proc zClosureVar(x: int) =
  ## `__closure`: a proc-typed local with no initializer.
  var f: proc(y: int): int
  if x == 1: symexTarget("closurevar")

proc zAtomicVar(x: int) =
  ## `__ownership:Atomic`.
  var a: Atomic[int]
  if x == 1: symexTarget("atomicvar")

proc zUnsupportedGenericVar(x: int) =
  ## `__unsupported:<X>`: a user generic `classifyType`'s structural arms
  ## never recognise.
  var w: Weird[int]
  if x == 1: symexTarget("weirdvar")

suite "S8ao (2): itUninterp has no zero":

  template declines(fn: typed, lbl: string, kind: SymexErrorKind): untyped =
    ## RFC-0005 S8ap: the decline carries the placeholder's own kind (was
    ## `feUnsupportedStmtKind` "zero-init not modeled" for all three).
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check not r.errors.hasKind(weInternalWalkerFault)
      check r.errors.hasKind(kind)

  test "a closure-typed local (__closure) declines, never crashes":
    declines(zClosureVar, "closurevar", ceUnsupportedHof)

  test "an Atomic-typed local (__ownership:Atomic) declines, never crashes":
    declines(zAtomicVar, "atomicvar", heUnsupportedOwnership)

  test "an unrecognised generic local (__unsupported:*) declines, never crashes":
    declines(zUnsupportedGenericVar, "weirdvar", feUnsupportedParamType)

  test "symexWalkerVersion >= 181 (item 2)":
    check parseInt(symexWalkerVersion) >= 181

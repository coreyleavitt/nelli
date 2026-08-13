## Phase 16 — RFC Cluster 3 slice M4: string `.add` / `&=` modeled as
## in-place concat-assign.
##
## Both mutating string-append forms — `s &= x` (augmented-assign) and
## `s.add(x)` (string method) — are now modeled via the EXISTING `iekStrConcat`
## IR (the same ctor the binary `s & x` expression arm already builds), by
## rebinding the receiver's env slot to the concatenation result:
## `s := s & x`. This is a type-classify branch (string LHS/receiver routes to
## `mkStrOp`), NOT an addition to `binopForInfix` (which still has no `"&"`
## case, and must not gain one — string concat is a structurally different IR
## family from the numeric binop enum).
##
## `s &= x` was SND-1's Class-B silent-no-op case: `binopForInfix` has no
## `"&"` case, so pre-M4 this landed as a bare `mkUnsupported` — a false
## `sxSat` pre-SND-1 (naive stale-value comparison), `sxUnknown` post-SND-1
## (honest taint-and-degrade). M4 closes this properly: a real, correctly-
## constrained verdict. `s.add(x)` on a string receiver (S11) degraded
## cleanly to `sxUnknown`; M4 now models the string-arg form. `s.add('c')`
## (a char arg) is explicitly OUT OF SCOPE — char is modeled as `itInt`
## (uint8) with no char→1-char-string conversion IR — and keeps the S11
## clean degrade (see `tsymex_phase15_S11_mutation.nim`'s `addChar` guard).
##
## Bumps `symexWalkerVersion` 49→50 (verdict-surface change for `&=`/`.add`
## SUTs). `renderAsChoicesVersion` stays "5" — the witness is still a plain
## string, same shape the binary `&` expression form already produces.
import std/[unittest, strutils]
import nelli/symex

# --- `&=` happy path: SND-1's exact repro, now correctly modeled -----------
proc ampEqHappy() =
  var t = "a"
  t &= "x"
  if t == "ax":
    symexTarget("hit")

# --- `&=` UNSAT soundness: proves the concat is actually modeled, not a
# free-symbol / no-op stand-in (which would wrongly allow "ay" too) --------
proc ampEqUnsat() =
  var t = "a"
  t &= "x"
  if t == "ay":
    symexTarget("hit")

# --- `.add` parity: happy path -----------------------------------------------
proc addHappy() =
  var t = "a"
  t.add("x")
  if t == "ax":
    symexTarget("hit")

# --- `.add` parity: UNSAT soundness -----------------------------------------
proc addUnsat() =
  var t = "a"
  t.add("x")
  if t == "ay":
    symexTarget("hit")

# --- `&=` with the SND-1-shaped SYMBOLIC parameter (not a local literal) ----
# `t` is the free SUT parameter itself (mirrors SND-1's `concatMutate`).
# Target reachable only for t == "a" — proves the concat threads a symbolic
# LHS receiver, not just literals.
proc ampEqSymbolicParam(t: var string) =
  t &= "x"
  if t == "ax":
    symexTarget("hit")

# --- `&=` with a SYMBOLIC RHS operand (SUT string param appended to a local
# literal receiver) — proves the concat threads a symbolic operand on the
# RHS, not just literal RHS args. Target reachable only for s == "bc". ------
proc ampEqSymbolicRhs(s: string) =
  var t = "a"
  t &= s
  if t == "abc":
    symexTarget("hit")

# --- `.add` with a SYMBOLIC RHS operand: same proof for the method form ----
proc addSymbolicRhs(s: string) =
  var t = "a"
  t.add(s)
  if t == "abc":
    symexTarget("hit")

# --- Regression: numeric augmented-assign unaffected ------------------------
proc numericPlusEqUnchanged(n: int) =
  var x = n
  x += 1
  if x == 6:
    symexTarget("hit")

proc numericTimesEqUnchanged() =
  var x = 3
  x *= 4
  if x == 12:
    symexTarget("hit")

# --- Regression: binary `s & x` expression form unaffected ------------------
proc binaryConcatUnchanged(s: string) =
  if (s & "y") == "xy":
    symexTarget("hit")

# --- Regression: `seq[T].add` unaffected (must NOT reroute through the new
# string-receiver concat branch) --------------------------------------------
proc seqAddUnchanged(v: var seq[int]) =
  v.add(9)
  if v.len == 1 and v[0] == 9:
    symexTarget("hit")

suite "symex Phase 16 M4 — string `.add`/`&=` via iekStrConcat in-place assign":

  test "&= happy path (SND-1 repro): \"a\" &= \"x\" == \"ax\" is real sxSat":
    let r = symexFind(ampEqHappy, tLabel("hit"))
    check r.status == sxSat

  test "&= UNSAT: \"a\" &= \"x\" != \"ay\" (proves the concat is modeled, not a no-op)":
    let r = symexFind(ampEqUnsat, tLabel("hit"))
    check r.status == sxUnsat

  test ".add parity: \"a\".add(\"x\") == \"ax\" is real sxSat":
    let r = symexFind(addHappy, tLabel("hit"))
    check r.status == sxSat

  test ".add UNSAT: \"a\".add(\"x\") != \"ay\"":
    let r = symexFind(addUnsat, tLabel("hit"))
    check r.status == sxUnsat

  test "&= SND-1 no-longer-tainted: symbolic-param LHS yields a definite sxSat (never sxUnknown), witness round-trips":
    let r = symexFind(ampEqSymbolicParam, tLabel("hit"))
    check r.status == sxSat
    check r.status != sxUnknown
    check r.witness[0] == "a"
    check r.witness[0] & "x" == "ax"   ## round-trip vs real Nim `&`

  test "&= symbolic RHS operand: witness s == \"bc\", round-trips against real Nim":
    let r = symexFind(ampEqSymbolicRhs, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "bc"
    check "a" & r.witness[0] == "abc"

  test ".add symbolic RHS operand: witness s == \"bc\", round-trips against real Nim":
    let r = symexFind(addSymbolicRhs, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "bc"
    var expected = "a"
    expected.add(r.witness[0])
    check expected == "abc"

  test "regression: numeric `+=` unaffected":
    let r = symexFind(numericPlusEqUnchanged, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 5

  test "regression: numeric `*=` unaffected":
    let r = symexFind(numericTimesEqUnchanged, tLabel("hit"))
    check r.status == sxSat

  test "regression: binary `s & x` expression form unaffected":
    let r = symexFind(binaryConcatUnchanged, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "x"

  test "regression: seq[T].add unaffected (not rerouted through string concat)":
    let r = symexFind(seqAddUnchanged, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len == 0

  test "walker version floor: symexWalkerVersion >= 50 (M4 &=/.add modeled)":
    check parseInt(symexWalkerVersion) >= 50

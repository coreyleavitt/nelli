## RFC-0005 (soundness channels) slice S8s -- S8p's precision remainder.
##
## Four places the walker gave up on (or faulted over) code whose behaviour
## is fully determined, and one cpp compile failure. S8p reported them.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## debug build) by the oracle test of each suite, which runs the SUT itself.
##   (1) a `seq[uint8]` element compared against a literal
##       (was `weInternalWalkerFault`, "field 'bv8' ... kind = svBV64");
##   (2) the zero value of a multi-variant whose ordinal 0 falls in an
##       `else` arm (was `feUnsupportedOpHavoc`);
##   (3) a callee returning an `array` (was `feUnsupportedOpHavoc`);
##   (4) a write to a variant arm field and a positional tuple-element
##       write (was `feUnsupportedStmtKind`);
##   (5) the walker version floor.
## The cpp compile failure of `tsymex_r6_n43_parity` (a deleted
## `std::atomic::operator=`) is pinned by that suite compiling on cpp.
##
## RFC-0005 S8cm: part 2 of 8 of this suite, with
## `tsymex_rfc0005_s8s_precision`, `tsymex_rfc0005_s8s_precision_h`,
## `tsymex_rfc0005_s8s_precision_c`, `tsymex_rfc0005_s8s_precision_d`,
## `tsymex_rfc0005_s8s_precision_e`, `tsymex_rfc0005_s8s_precision_f`,
## `tsymex_rfc0005_s8s_precision_g`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 134 s).
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

# ---- (2) a multi-variant whose ordinal 0 is in an else arm ------------------------
#
# Real Nim zero-initialises `result`: both discriminators s3A (ordinal 0, which
# each axis's `else` arm covers) and every field 0, the else arms' too. Before
# S8s the untouched result was `feUnsupportedOpHavoc`.

type
  S8sK = enum s3A, s3B, s3C
  S8sMVE = object
    case k: S8sK
    of s3B: b: int
    else: e: int
    case j: S8sK
    of s3C: c: int
    else: f: int
  S8sVE = object
    ## A single `case` whose ordinal 0 is in its `else` arm.
    case vk: S8sK
    of s3C: vc: int
    else: ve: int

proc mveMaybe(x: int): S8sMVE =
  if x > 0: result = S8sMVE(k: s3B, b: x, j: s3C, c: 1)

proc mveBare(x: int): S8sMVE =
  if x > 0: return
  result = S8sMVE(k: s3B, b: 2, j: s3C, c: 2)

proc callMVE(x: int) =
  let v = mveMaybe(x)
  if x <= 0 and v.k == s3A and v.e == 0 and v.j == s3A and v.f == 0:
    symexTarget("s8s_mve")
  if x <= 0 and (v.k != s3A or v.j != s3A): symexTarget("s8s_mve_dead")
  # The else arms' fields are bound too: `retBindEq` guarded each arm's
  # fields by `disc == <arm key>`, and an else arm's key is -1.
  if x <= 0 and (v.e != 0 or v.f != 0): symexTarget("s8s_mve_edead")
  if x > 0 and v.b == 5: symexTarget("s8s_mve_b")

proc callMVEBare(x: int) =
  let v = mveBare(x)
  if x > 0 and v.k == s3A and v.f == 0: symexTarget("s8s_mvebare")
  if x > 0 and v.k != s3A: symexTarget("s8s_mvebare_dead")

suite "S8s (2) a multi-variant whose ordinal 0 is in an else arm":
  test "an untouched result is its zero value (was feUnsupportedOpHavoc)":
    let r = symexFind(callMVE, tLabel("s8s_mve"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.errors.len == 0
    let d = symexFind(callMVE, tLabel("s8s_mve_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat
    let e = symexFind(callMVE, tLabel("s8s_mve_edead"))
    checkpoint($e.status & " " & show(e.errors))
    check e.status == sxUnsat
    let b = symexFind(callMVE, tLabel("s8s_mve_b"))
    checkpoint($b.status & " " & show(b.errors))
    check b.status == sxSat
    if b.status == sxSat:
      check b.witness[0] == 5

  test "a bare return is its zero value":
    let r = symexFind(callMVEBare, tLabel("s8s_mvebare"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    let d = symexFind(callMVEBare, tLabel("s8s_mvebare_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

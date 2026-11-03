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
## RFC-0005 S8cm: part 7 of 7 of this suite, with
## `tsymex_rfc0005_s8s_precision`, `tsymex_rfc0005_s8s_precision_b`,
## `tsymex_rfc0005_s8s_precision_c`, `tsymex_rfc0005_s8s_precision_d`,
## `tsymex_rfc0005_s8s_precision_e`, `tsymex_rfc0005_s8s_precision_f`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 134 s).

import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc tupPosNested(x: int) =
  var q = (a: (b: 1, c: 2), d: 3)
  q[0][1] = x
  q.a[0] += 1
  if q.a.b == 2 and q.a.c == 9 and q.d == 3: symexTarget("s8s_tpn")
  if q.d != 3: symexTarget("s8s_tpn_dead")

suite "S8s (4) variant arm field writes and positional tuple writes":
  test "nested positional and named tuple writes":
    let r = symexFind(tupPosNested, tLabel("s8s_tpn"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 9
    let d = symexFind(tupPosNested, tLabel("s8s_tpn_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

# ---- (5) walker version floor -----------------------------------------------------

suite "S8s (5) walker version":
  test "walker version is at least 167":
    check parseInt(symexWalkerVersion) >= 167

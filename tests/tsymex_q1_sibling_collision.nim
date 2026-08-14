## Issue #154 guard — cross-proc collision on byte-identical while-loop ASTs.
##
## During A1 corpus authoring (`tsymex_phase15_A1_loopguard.nim`), cell (e)'s
## UNSAT companion was observed flipping `sxUnsat` -> `sxSat` when a sibling
## proc in the same module carried a byte-identical scan loop (same `':'`
## delimiter), suggesting recognizer/registration state keyed on AST shape
## without proc identity. The follow-up investigation could NOT reproduce the
## flip under exact reconstruction: not at HEAD, not at the A1 corpus commit
## (65f5e5d) with the identical dependency lock and container image, on
## either backend, for any of the candidate shapes (sibling declared-only,
## sibling queried first, full corpus file with reverted delimiters, cell
## queried in isolation). A structural audit found no candidate state either:
## `tryRecognizeScanIdiom` is pure and ctx-local, the parser holds no
## compile-time mutable state, and each runtime query builds a fresh
## Z3Context with all threadvar sinks reset. The observation is attributed
## to transient authoring-session build state, and #154 is closed as
## not-reproducible.
##
## This file makes the collision surface a PERMANENT pin so any future
## regression of that class fails loudly instead of surfacing as a silent
## wrong verdict in an unrelated corpus file. Both candidate shapes are
## pinned:
##   * a sibling with the byte-identical loop that is DECLARED but never
##     referenced (the minimized shape from the #154 report), and
##   * a sibling with the byte-identical loop that is itself queried via
##     `symexFind` BEFORE the target (the shape the A1 corpus actually
##     exercises — compile-time parse order and runtime query order both
##     mirror the original observation).
## The target's UNSAT companion (`i > s.len` after the canonical scan) is
## provable ONLY via the recognized closed form's clamp, so ANY cross-proc
## interference that suppresses or corrupts recognition flips this verdict.
import std/[unittest]
import nelli/symex

# Byte-identical to the target's loop (same `':'` delimiter, same bare
# `inc i` body) — never referenced anywhere. Declaration alone must not
# perturb another proc's query.
proc scanSiblingDeclaredOnly(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  if i == 3:
    symexTarget("hit")

# Byte-identical loop again, but this sibling IS queried (first), so its
# parse and its Z3 query both precede the target's.
proc scanSiblingQueried(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  if i == 3:
    symexTarget("hit")

proc scanTarget(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  if i > s.len:
    symexTarget("impossible")

suite "symex Q1 — byte-identical sibling loops must not perturb a query (#154)":
  test "queried sibling baseline: its own target is reachable, sxSat":
    let r = symexFind(scanSiblingQueried, tLabel("hit"))
    check r.status == sxSat

  test "target after both siblings: UNSAT companion still proves, sxUnsat":
    let r = symexFind(scanTarget, tLabel("impossible"))
    check r.status == sxUnsat

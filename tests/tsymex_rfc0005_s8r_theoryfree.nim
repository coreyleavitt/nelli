## RFC-0005 (soundness channels) slice S8r -- the symex-mingw corpus shard 2
## runner loss.
##
## `corpus (shard 2)` lost its Windows runner at every sha since S8k. The
## suite was `tsymex_163rev_intoffset_range`: its range-checked label
## searches (added by S8k) ask for a RangeDefect witness longer than 1000
## bytes. `checkCapped` caps the query at `maxSeqLen`; after the capped
## UNSAT, step 1b re-checks it with `smt.string_solver = none` set as a
## solver parameter. Z3 4.13.4's default (combined) solver ignores that
## parameter and keeps the sequence theory, so step 1b ran the uncapped
## string search itself, which does not poll `rlimit`. Measured on Linux
## against the 4.13.4 shared library: past 10 GB in 510 s (killed). Z3
## 5.1, the Linux image's build, honours the parameter, so every Linux
## gate stayed green.
##
## RED only against Z3 4.13.4 (the Windows leg's build; locally
## `LD_LIBRARY_PATH` at the 4.13.4 shared library): (1) reads `zsUnsat`,
## and (2) does not terminate. Z3 5.1 passes both before and after.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

# ---- (1) the theory-free solver has no sequence theory ----------------------
#
# `str.len(x) < 0` is refuted only by the sequence theory's length axiom.
# With the theory off, `str.len` is uninterpreted and the query is SAT.

suite "S8r: the theory-free check has no sequence theory":

  test "str.len(x) < 0 is SAT with seqTheory = false":
    let ctx = newContext()
    let x = mkStringVar(ctx, "x")
    let lenX = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_length(ctx.raw, x.raw))
    let s = querySolver(ctx, [lenX < mkInt(ctx, 0)], 100_000'u,
                        seqTheory = false)
    check s.check() == zsSat

  test "companion: the same query is UNSAT with the sequence theory":
    let ctx = newContext()
    let x = mkStringVar(ctx, "x")
    let lenX = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_length(ctx.raw, x.raw))
    let s = querySolver(ctx, [lenX < mkInt(ctx, 0)], 100_000'u)
    check s.check() == zsUnsat

# ---- (2) the capped search over a >1000-byte witness terminates ------------
#
# The shape of `tsymex_163rev_intoffset_range`'s first range-checked
# search. Nim raises RangeDefect on `return i` past 1000, so the defect is
# real, but its witness is longer than `maxSeqLen`: the honest verdict is
# the recorded cap decline (`sxUnknown`), never `sxUnsat`.

proc findColonRanged(s: string, offset: int): range[0..1000] =
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return i
    i = i + 1
  return i

proc callerRanged(s: string) =
  let p = findColonRanged(s, 0)
  if p > 1000:
    symexTarget("s8r_impossible")

suite "S8r: a capped string search past maxSeqLen terminates":

  test "the >1000-byte RangeDefect witness is a recorded maxSeqLen decline":
    let r = symexFind(callerRanged, tLabel("s8r_impossible"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    var capped = false
    for e in r.errors:
      check e.severity != sevError or e.kind == beSolverUndef
      if e.kind == beSolverUndef and "maxSeqLen" in e.msg: capped = true
    check capped

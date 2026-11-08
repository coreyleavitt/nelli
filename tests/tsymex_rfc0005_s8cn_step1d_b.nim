## RFC-0005 (soundness channels) slice S8cn, item 1 -- step 1d can turn a
## decline into `sxUnsat`, so it is held to adversarial pins.
##
## Step 1d (batch 8) answers UNSAT when the query with no sequence theory, plus
## the facts, has no model breaking a cap: every real model keeps to the caps,
## and step 1 refuted those. It stands on two things, each pinned here against
## native runs:
##   - `not all` is the negation of EVERY cap (a query that bounds one string
##     and leaves another past the cap must not answer);
##   - every fact is valid in Nim's byte-faithful string model (a fact that cut
##     a real model would refute the query's own past-the-cap model). The audit
##     is in the RFC's "As landed (S8cn)"; each family is checked here under
##     `invalidFacts`, over strings that hold `\x00` and `\xff`.
## Each query below reaches step 1d (the step table says so), on both Z3s. The
## pins were green when written: the two mutations named in the RFC's note turn
## them red (a false `sxUnsat`).
##
## RFC-0005 S8cm: part 2 of 6 of this suite, with `tsymex_rfc0005_s8cn_step1d`,
## `tsymex_rfc0005_s8cn_step1d_c`, `tsymex_rfc0005_s8cn_step1d_d`,
## `tsymex_rfc0005_s8cn_step1d_e`, `tsymex_rfc0005_s8cn_step1d_f`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 118 s).
import std/[re, tables]
include s8ai_helpers

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8cn_step1d needs -d:symexQueryStats (its .nim.cfg)".}

const smallCap = SymexSettings(budget: ResourceBudget(maxSeqLen: 8))

from ./s8cu_helpers import nativeHits

proc stepStatus(name: string): string =
  ## The last answer step `name` gave in the walk just run, or "".
  for s in symexStepStats:
    if s.step == name: result = s.status

template walk(sut: typed; lbl: static string): untyped =
  block:
    symexStepStats = @[]
    let r = symexFind(sut, tLabel(lbl), smallCap)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    var names: seq[string]
    for s in symexStepStats: names.add s.step & "/" & s.status & "=" & $s.units
    checkpoint names.join(" ")
    r

# ---- A query refuted only inside the cap -------------------------------------
#
# `abcde` ... `efghi` overlaps in one byte: the shortest such string is
# `abcdefghi`, 9 bytes. No length fact sees that (each `len(t) <= len(s)` gives
# 5), so the theory-free query keeps a model under the cap of 8 and step 1c's
# capped half does not answer; only the theory refutes it within the cap.

proc overlap(s: string): bool =
  s.startsWith("abcde") and s.endsWith("efghi")

proc boundAtCap(s: string) =
  if s.len <= 8 and overlap(s): symexTarget("at_cap_dead")

proc boundPastCap(s: string) =
  if s.len <= 9 and overlap(s): symexTarget("past_cap_live")

proc noBound(s: string) =
  if overlap(s): symexTarget("no_bound_live")

proc oneBranch(s: string; c: bool) =
  # One query: the bound holds on one disjunct.
  if ((c and s.len <= 8) or not c) and overlap(s):
    symexTarget("one_branch_live")

proc onePath(s: string; c: bool) =
  # Two paths: UNSAT with the bound, live without.
  if c:
    if s.len > 8: return
  if overlap(s): symexTarget("one_path_live")

proc onePathBoth(s: string; c: bool) =
  # Bounded on both paths: dead on each.
  if c:
    if s.len > 8: return
  else:
    if s.len > 7: return
  if overlap(s): symexTarget("one_path_dead")

proc theoryBound(s: string) =
  # `s.len <= 9`, which only the regex's complement states: no fact reads it.
  if not s.match(re"(?s).{10}") and overlap(s):
    symexTarget("theory_bound_live")

proc oneLeaf(s, t: string) =
  # `s` keeps to the cap and `t` does not: `not all` must reach `t`'s cap.
  if s.len <= 8 and t.len <= 9 and overlap(t): symexTarget("one_leaf_live")

proc oneLeafS(s, t: string) =
  # The cap's other order (a cap list is in the query's term order).
  if t.len <= 9 and s.len <= 8 and s.len >= 1 and overlap(t):
    symexTarget("one_leaf_s_live")

suite "S8cn (1): where step 1d must not answer":

  test "the native runs":
    # Every string of length <= 8 holding the prefix and the suffix would have
    # to overlap them in two bytes or more: none does.
    var found = 0
    for overlapBy in 0 .. 5:
      let w = "abcde" & "efghi"[overlapBy .. ^1]
      if w.len <= 8 and overlap(w): inc found
    check found == 0
    const alpha = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'x']
    var fills = @[""]
    for a in alpha:
      fills.add $a
      for b in alpha:
        fills.add $a & $b
        for c in alpha: fills.add $a & $b & $c
    symexCaptureBegin()
    for f in fills: boundAtCap("abcde" & f)
    check "at_cap_dead" notin symexCaptureEnd()
    const w = "abcdefghi"
    check "past_cap_live" in nativeHits(boundPastCap(w))
    check "no_bound_live" in nativeHits(noBound(w))
    check "one_branch_live" in nativeHits(oneBranch(w, false))
    check "one_branch_live" notin nativeHits(oneBranch(w, true))
    check "one_path_live" in nativeHits(onePath(w, false))
    check "one_path_live" notin nativeHits(onePath(w, true))
    check "one_path_dead" notin nativeHits(onePathBoth(w, false))
    check "one_path_dead" notin nativeHits(onePathBoth(w, true))
    check "theory_bound_live" in nativeHits(theoryBound(w))
    check "one_leaf_live" in nativeHits(oneLeaf("q", w))
    check "one_leaf_s_live" in nativeHits(oneLeafS("q", w))

  # A live label past the cap: never `sxUnsat`. `sxSat` only with a witness
  # that replays, and the step table shows the query reached step 1d and got
  # no UNSAT there.
  template live(sut: typed; lbl: static string; replay: untyped) =
    block:
      let r = walk(sut, lbl)
      check r.status != sxUnsat
      check stepStatus("1d") notin ["", "zsUnsat"]
      if r.status == sxSat:
        let witness {.inject.} = r.witness
        check lbl in nativeHits(replay)

  test "a length bound one past the cap":
    live(boundPastCap, "past_cap_live", boundPastCap(witness[0]))

  test "no bound at all":
    live(noBound, "no_bound_live", noBound(witness[0]))

  test "a bound on one disjunct":
    live(oneBranch, "one_branch_live", oneBranch(witness[0], witness[1]))

  test "a bound on one path":
    live(onePath, "one_path_live", onePath(witness[0], witness[1]))

  test "a bound only the sequence theory gives":
    live(theoryBound, "theory_bound_live", theoryBound(witness[0]))

  test "one leaf bounded, another past the cap":
    live(oneLeaf, "one_leaf_live", oneLeaf(witness[0], witness[1]))
    live(oneLeafS, "one_leaf_s_live", oneLeafS(witness[0], witness[1]))

suite "S8cn (1): where step 1d does answer":

  test "the query's bounds imply every cap":
    let d = walk(boundAtCap, "at_cap_dead")
    check d.status == sxUnsat
    check stepStatus("1d") == "zsUnsat"

  test "both paths bounded":
    let d = walk(onePathBoth, "one_path_dead")
    check d.status == sxUnsat
    check stepStatus("1d") == "zsUnsat"

suite "S8cn (1): every family of facts, under `invalidFacts`":

  template allValid(src: string; domain: seq[Z3Bool] = @[]) =
    block:
      let ctx = newContext()
      let roots = q(ctx, src)
      let res = invalidFacts(ctx, roots, domain)
      checkpoint src
      checkpoint res.bad.join("\n")
      check res.n > 0
      check res.bad.len == 0

  test "ranges: length, index, last index, piece, code, value":
    allValid("""(assert (>= (str.len s) 0))
      (assert (>= (str.indexof s t i) 0))
      (assert (>= (seq.last_indexof s t) 0))
      (assert (= (str.at s i) "a"))
      (assert (= (str.substr s i n) "a"))
      (assert (>= (str.to_code x) 0))
      (assert (>= (str.to_int x) 0))""")

  test "a byte leaf's code":
    let ctx = newContext()
    let roots = q(ctx, """(assert (str.in_re s (re.* (re.range "\u{0}" "\u{ff}"))))
      (assert (>= (str.to_code (str.at s i)) 0))""")
    let domain = @[roots[0]]
    let res = invalidFacts(ctx, roots, domain)
    checkpoint res.bad.join("\n")
    check res.n > 0
    check res.bad.len == 0

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
## RFC-0005 S8cm: part 1 of 6 of this suite, with
## `tsymex_rfc0005_s8cn_step1d_b`, `tsymex_rfc0005_s8cn_step1d_c`,
## `tsymex_rfc0005_s8cn_step1d_d`, `tsymex_rfc0005_s8cn_step1d_e`,
## `tsymex_rfc0005_s8cn_step1d_f`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 118 s).
import std/[re, tables]
include s8ai_helpers

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8cn_step1d needs -d:symexQueryStats (its .nim.cfg)".}

const smallCap = SymexSettings(budget: ResourceBudget(maxSeqLen: 8))

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

# ---- S8bx's `grow_pad_dead`, the query step 1d was added for -----------------

proc growPad(s: string, n: int) =
  if n < 0 or n > 12 or s.len > 8: return
  var t = s
  t.setLen(n)
  if n > s.len and t[n - 1] != '\0': symexTarget("grow_pad_dead")
  if n == s.len + 3 and s.len >= 1 and t[n - 1] == '\0' and t[0] == 'q':
    symexTarget("grow_pad_live")

proc growStale(s: string, m, n: int) =
  ## The same claim on a string shrunk first: its buffer holds stale bytes.
  if n < 0 or n > 12 or m < 0 or m > 12 or s.len > 8: return
  var t = s
  t.setLen(m)
  t.setLen(n)
  if n > m and t[n - 1] != '\0': symexTarget("grow_stale_dead")

suite "S8cn (1): grow_pad_dead natively":

  test "exhaustive over the bounded inputs":
    # Every string of length <= 2; lengths 3..8 over the four bytes a grown or
    # copied byte could be confused with (the code path reads no byte's value,
    # only its length and capacity); every `n` in -1..13.
    var inputs = @[""]
    for a in 0 .. 255:
      inputs.add $chr(a)
      for b in 0 .. 255: inputs.add $chr(a) & $chr(b)
    const four = ['\0', '\1', 'q', '\xff']
    var frontier = @[""]
    for len in 1 .. 8:
      var next: seq[string]
      for w in frontier:
        for c in four: next.add w & c
      if len >= 3: inputs.add next
      frontier = next
    symexCaptureBegin()
    for s in inputs:
      for n in -1 .. 13:
        if n >= 0: growPad(s, n)
    let hits = symexCaptureEnd()
    check "grow_pad_dead" notin hits
    check "grow_pad_live" in hits

  test "shrunk first: stale bytes in the buffer stay unread":
    symexCaptureBegin()
    for s in ["", "q", "qq", "\xff\xff\xff\xff\xff\xff\xff\xff"]:
      for m in 0 .. 12:
        for n in 0 .. 12:
          growStale(s, m, n)
    let hits = symexCaptureEnd()
    check "grow_stale_dead" notin hits

  test "the walker agrees":
    # The default cap: `t` runs to 12 bytes, past the small cap of the suites
    # below, so a real model breaks that one and step 1d rightly says so.
    symexStepStats = @[]
    let d = symexFind(growPad, tLabel("grow_pad_dead"))
    checkpoint show(d.errors)
    check d.status == sxUnsat
    let l = symexFind(growPad, tLabel("grow_pad_live"))
    check l.status == sxSat
    let g = symexFind(growStale, tLabel("grow_stale_dead"))
    checkpoint show(g.errors)
    check g.status == sxUnsat
    let tooSmall = walk(growPad, "grow_pad_dead")
    check tooSmall.status == sxUnknown
    check stepStatus("1d") == "zsSat"

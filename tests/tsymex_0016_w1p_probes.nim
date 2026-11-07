## RFC-0016 W1-p -- the three probe agreements that had no pin: SND-07's
## `ua3_diff`, SND-12's `gc_shared`, INT-21's `ai_caught`. Each SUT is the
## probe's own source, run natively beside the walker's verdict.
##
## Sources: SND-07 `p_cp.nim` and INT-21 `p_ck.nim` (the pre-tag probes);
## SND-12 `origin/worker-sls2:worker-reports/s8cn-blocker/
## s8cn_release_blocker_probe.nim` (`sGlCur`, `pv2`).
import std/[unittest, os, sets]
import nelli
import nelli/symex
import ./s8cu_helpers

if getEnv("NELLI_PIN_DIR").len == 0:  # keep a sweep-wide dir; else a private one
  putEnv("NELLI_PIN_DIR", getTempDir() / ("w1p_pins_" & $getCurrentProcessId()))

# --- SND-07: uncheckedAssign, the other arm's bytes differ --------------------

type
  K = enum kA, kB, kC
  V = object
    case k: K
    of kA, kB: x: int
    of kC: y: int

proc ua3(v: int) =
  var o = V(k: kA, x: v)
  {.cast(uncheckedAssign).}:
    o.k = kC
  if o.y == v: symexTarget("ua3_same")
  if o.y != v: symexTarget("ua3_diff")

proc ua3Diff(v: int) =
  var o = V(k: kA, x: v)
  {.cast(uncheckedAssign).}:
    o.k = kC
  if o.y != v: symexTarget("hit")

# --- SND-12: a `let` cursor over a shared global -------------------------------

var gseq: seq[int]
proc pv2(s: seq[int]): int =
  let c = s
  gseq[0] = 5
  c[0]

proc sGlCur(n: int) =
  if n > 1000 or n < -1000 or n == 5: return
  gseq = @[n]
  let r = pv2(gseq)
  if r == n: symexTarget("gc_copy")
  if r == 5: symexTarget("gc_shared")

proc sGlShared(n: int) =
  if n > 1000 or n < -1000 or n == 5: return
  gseq = @[n]
  if pv2(gseq) == 5: symexTarget("hit")

# --- INT-21: `mitems` over int16 with assertions off ---------------------------

{.push assertions: off.}
proc grow16(s: var seq[int16]) =
  for x in s.mitems:
    x = x + 1
{.pop.}

proc aIter(v: int16) =
  var s = @[v]
  try:
    grow16(s)
    if s[0] == 8: symexTarget("ai_hit")
  except AssertionDefect:
    symexTarget("ai_caught")

proc aIterCaught(v: int16) =
  var s = @[v]
  try:
    grow16(s)
  except AssertionDefect:
    symexTarget("hit")

suite "RFC-0016 W1-p: the probe agreements":
  test "SND-07 ua3: the native run, then the walker's decline":
    # Natively the new arm holds the old bytes, so `diff` is never reached for
    # any input and `same` always is.
    for v in [low(int), -1, 0, 1, 7, high(int)]:
      let r = nativeRun(ua3(v))
      check "ua3_same" in r.hits
      check "ua3_diff" notin r.hits
      check r.raised.len == 0
    pinDecline(ua3Diff, cellKey(axConstruct, "uncheckedAssign/diff"),
               feUncheckedDiscBytes)
    let r = symexFind(ua3Diff, tLabel("hit"), pinSettingsConst)
    check r.status == sxUnknown

  test "SND-12 gc_shared: a let cursor over a shared global is not a copy":
    # Natively the cursor aliases the global, so the write shows through.
    for n in [-1000, -1, 0, 4, 6, 1000]:
      let r = nativeRun(sGlCur(n))
      checkpoint "n=" & $n & " hits=" & $r.hits
      check "gc_shared" in r.hits
      check "gc_copy" notin r.hits
    # The walker cannot decide it (the `let` cursor decline) and must not
    # claim the copy: sxUnknown, never sxUnsat.
    pinDecline(sGlShared, cellKey(axReadOnly, "letCursor/sharedGlobal"),
               feUnsupportedOp)
    let r = symexFind(sGlShared, tLabel("hit"), pinSettingsConst)
    check r.status == sxUnknown

  test "INT-21 ai_caught: int16 overflow at 32767 raises natively":
    let hi = nativeRun(aIter(32767'i16))
    checkpoint "aIter(32767) raised=" & hi.raised
    check hi.raised == "OverflowDefect"
    check "ai_hit" notin hi.hits and "ai_caught" notin hi.hits
    for v in [0'i16, 7'i16, -1'i16, 32766'i16]:
      let r = nativeRun(aIter(v))
      check r.raised.len == 0
      check "ai_caught" notin r.hits
    let rs = symexFind(aIter, tRaisedExn("OverflowDefect"), pinSettingsConst)
    checkpoint $rs.status & " " & show(rs.errors)
    var msg = ""
    try:
      discard pinExact(aIter, cellKey(axConstruct, "mitems/int16/assertionsOff"),
                       target = tRaisedExn("OverflowDefect"),
                       domain = sampled([low(int16), -1'i16, 0, 7, 32766, 32767]))
    except PinFailure as e:
      msg = e.msg
    checkpoint msg
    check msg.len == 0

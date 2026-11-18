## RFC-0016 INT-37 (0005 review R2-09, R6-09): two unverified probes, run.
##
## R2-09. The PCRE reader's size bound adds nothing for a possessive
## quantifier on an item that is not a group (`groupRepSize` adds the
## OP_ONCE .. OP_KET wrapper only for groups and assertions). PCRE 8.45 has a
## possessive opcode for every repeat of a character, a character type, a
## class and a back-reference (`opcode_possessify`), so it adds nothing
## either; a library that wrapped such an item would add 6 code units per
## item and refuse these patterns as too large. Each family below is taken to
## the largest count the reader decides, which must compile under `re()`.
##
## R6-09. `routineKey` (`symBodyHash` of a routine symbol) was thought able to
## fail at compile time for a routine with no body: an `importc` one or a
## forward declaration. A SUT calling one of each compiles and runs.
import std/[unittest, strutils, re]
import nelli
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/canonicalize
import nelli/smt/runtime
from nelli/smt/admission import cellKey, axConstruct
import ./s8cu_helpers

proc compiles(p: string): (bool, string) =
  try:
    discard re(p)
    (true, "")
  except RegexError as e:
    (false, e.msg.splitLines()[0])

proc largestDecided(item: string; prefix = ""): int =
  ## The largest `n` such that `prefix & item * n` is decided by the reader,
  ## by bisection over the count (the bound grows with `n`).
  var lo = 1
  var hi = 70_000
  while lo < hi:
    let mid = (lo + hi + 1) div 2
    if parsePcre(prefix & repeat(item, mid)).status != psUnknown: lo = mid
    else: hi = mid - 1
  lo

suite "INT-37 R2-09: a possessive non-group repeat near PCRE's size limit":

  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 413

  test "every family the reader decides at its limit compiles under re()":
    var bad: seq[string]
    for (item, prefix) in [("a*+", ""), ("a{2,3}+", ""), ("\\d++", ""),
                           ("[ab]?+", ""), ("\\1*+", "(x)"), (".++", ""),
                           ("\\w{0,4}+", "")]:
      let at = if prefix.len > 0: prefix else: ""
      let n = largestDecided(item, at)
      let p = at & repeat(item, n)
      let pr = parsePcre(p)
      check pr.status == psUnmodelled      # a possessive is not modelled
      let (ok, msg) = compiles(p)
      checkpoint item & " x " & $n & " (len " & $p.len & "): " & msg
      if not ok: bad.add item & " x " & $n & ": re() refuses: " & msg
      # Near the limit: one more item would be past the reader's bound.
      check parsePcre(at & repeat(item, n + 1)).status == psUnknown
    check bad.len == 0
    pinNever(cellKey(axConstruct, "regex/possessive/size"), bad.len == 0,
      "PCRE 8.45 compiles a possessive repeat of a character, type, class " &
      "or back-reference at no extra size: every family the reader decides " &
      "at its size limit compiles")

# R6-09: a SUT that calls a routine with no body of its own.
proc cAbs(x: cint): cint {.importc: "abs", header: "<stdlib.h>".}
proc fwdTwice(x: int): int

proc sutBodiless(x: int) =
  if fwdTwice(x) == 8 and cAbs(cint(x)) == 4:
    symexTarget("bodiless")

proc fwdTwice(x: int): int = 2 * x

suite "INT-37 R6-09: a bodiless routine is keyed at compile time":

  test "an importc callee and a forward declaration compile and run":
    let db = inMemoryDatabase()
    let fs = symexFindAllWitnesses(sutBodiless, db)
    check fs.len == 1
    # Natively, x = 4 reaches it.
    check fwdTwice(4) == 8 and cAbs(4) == 4
    pinNever(cellKey(axConstruct, "cache/key/bodiless"), fs.len == 1,
      "a SUT calling an importc routine and a forward-declared one compiles: " &
      "`routineKey` keys both")

# ---- R2-08: no lowering leaves taint for another to find --------------------
#
# `claimStrayPendingTaint` found taint a lowering had left queued with no
# owner and, not knowing whose it was, put it on every path and finding of the
# statement: one path's decline tainted its siblings. Every raw `lower` now
# drains its own queue onto its own path, so a stray is a walker fault: a
# debug build stops on it, and a release build keeps the sound fallback.

suite "INT-37 R2-08: stray pending taint is a fault, not a statement's":

  test "a stray found at a lowering's entry stops a debug build":
    let r = strayClaimProbe()
    checkpoint $r
    when defined(release):
      check not r.tripped
      check r.strayKept == {scSpurious}
    else:
      check r.tripped
    check r.pendingAfter == {}
    pinNever(cellKey(axConstruct, "walk/stmt/stray-claim"),
      r.tripped or defined(release),
      "no lowering leaves pending taint for another lowering to claim: a " &
      "debug walk stops on one, a release walk keeps it for the statement")

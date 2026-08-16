## Chapulin 0.1.0 re-test triage — catalog #6 (chained dependent scans →
## "REGRESSED sxUnknown→crash"), walker v64. Root cause was NOT the Q1/R14
## loop machinery: DESTRUCTURING a tuple return from a loop-bearing callee
## that can raise sent a composite-typed retSym into `retBindEq`, whose
## non-primitive arm RAISED ValueError from inside the walk — unwinding
## through live `seq[Path]` state, the b7258f7/CR-1c C-backend silent-loss
## hazard. That one raise manifested nondeterministically: chapulin's
## re-test saw a hard native crash (bare non-zero exit); the same repro on
## the same commit also surfaced as a net-caught `weInternalWalkerFault`.
## v64 replaces the raise with an in-band classified degrade
## (`feUnsupportedOp`, path tainted uncertain) at the scalar-raise drain's
## binding site — deterministic, sound, never a crash.
##
## Kind-pinning note (verified while landing v64): the STRING-building
## chapulin shape (`readCStringTwin` with `s.add char(b)`) now degrades
## EARLIER, at the pre-existing `seUnsupportedStringOp` classified gap for
## a char-arg `.add` — so those tests pin "classified sxUnknown, never the
## walker-fault route", not one specific kind. The INT-only tuple shape
## (`scanPair`) has no string op to degrade at, reaches the composite
## `retBindEq` bind itself, and pins the new guard's `feUnsupportedOp`.
##
## Round-6 B3 (ADR-0028, walker v81) upgrade: `scanPair`'s loop is now
## recognized by `tryRecognizeScanPairIdiom`, the int-result sibling of
## Q1/B0's scan-lift closed form — the genuine decidability boundary v69
## reached (`beBudgetExhausted` on the `s.len`-bounded scan) is now
## DECIDED. `destructurePair`'s pin below upgrades from the k-unroll
## residue to a real `sxUnsat` PROOF: no `IndexDefect` is reachable
## anywhere in `destructurePair` — the entry-read probe only fires at the
## literal, always-in-bounds offset `2`, and the closed form eliminates
## the unbounded loop entirely, so every path is decided rather than
## budget-exhausted. `readCStringTwin`'s accumulating shape (`s.add
## char(b)` between the match check and the increment) is a DIFFERENT
## shape B3 deliberately does not match (B4/B5 scope, ADR-0028) — the
## `chained`/`singleDiscard`/`singleDestructure` pins below are unaffected
## and stay exactly as before.
import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

type ScanError = object of CatchableError

proc readCStringTwin(data: seq[int], offset: int): (string, int) =
  var s = ""
  var i = offset
  while i < data.len:
    let b = ((data[i] mod 256) + 256) mod 256
    if b == 0:
      return (s, i + 1)
    s.add char(b)
    i.inc
  raise newException(ScanError, "Unterminated at " & $offset)

proc scanPair(s: string, offset: int): (int, int) =
  ## Tuple-returning scan via the early-return idiom (round-6 B3's
  ## `scanPair` shape, ADR-0028): nothing degrades before the return bind,
  ## so this exercises the composite-retSym drain guard AND (since B3
  ## landed, walker v81) the int-result scan-lift recognizer
  ## (`tryRecognizeScanPairIdiom`), which closed-forms this exact loop —
  ## `while i < s.len: (if s[i] == lit: return (i, i+1)); inc i` — via the
  ## same `iekStrFind` primitive Q1/B0 use. Originally a `seq[int]` with a
  ## `mod 256` byte-mask (pre-round-6, before the representation work
  ## existed); migrated to `string` for B3 — the mask-and-`seq[int]`
  ## spelling is a recorded dead workaround the engine deliberately does
  ## not chase (ADR-0028 Leg 1), and the scan-lift family (Q1/B0/B3) only
  ## ever recognized `itString` receivers.
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return (i, i + 1)
    i.inc
  raise newException(ScanError, "Unterminated at " & $offset)

proc singleDiscard(data: seq[int]) =
  if data.len < 2: return
  discard readCStringTwin(data, 2)

proc singleDestructure(data: seq[int]) =
  if data.len < 2: return
  let (_, p1) = readCStringTwin(data, 2)
  if p1 > data.len:
    return

proc destructurePair(s: string) =
  if s.len < 2: return
  let (a, b) = scanPair(s, 2)
  if a > b:
    return

proc chained(data: seq[int]) =
  ## The catalog-#6 headline shape: 2nd scan's offset = 1st's symbolic result.
  let (_, p1) = readCStringTwin(data, 2)
  discard readCStringTwin(data, p1)

suite "symex re-test C6 — tuple-return destructure through the raise drain":

  test "discarded tuple-returning call degrades like its bound twin (v68 honesty)":
    ## Until v68 this pinned sxUnsat — an ARTIFACT: the discard arm dropped
    ## the call, so the walk saw only the length guard (the same vacuity
    ## class as the pre-v67 "slices prove on HEAD" ledger note). v68 walks
    ## discarded expressions, so this shape now degrades EXACTLY like
    ## `singleDestructure` below (same call, bound): classified sxUnknown,
    ## never the walker-fault route.
    let r = symexFind(singleDiscard, tIndexError())
    check r.status == sxUnknown
    check r.errors.len > 0
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "int-tuple destructure from a raising scan: B3 closed form proves defect-freedom":
    ## v69 upgraded this pin to reach the genuine decidability boundary — the
    ## s.len-bounded scan loop (`beBudgetExhausted`, the Q2/maxLoopUnwind
    ## class) — past the composite `retBindEq` tuple bind. Round-6 B3 (walker
    ## v81) upgrades it AGAIN: `tryRecognizeScanPairIdiom` closed-forms
    ## `scanPair`'s loop via the same `iekStrFind` primitive Q1/B0 use, so the
    ## scan is DECIDED rather than budget-exhausted. No `IndexDefect` is
    ## reachable anywhere in `destructurePair` — a REAL sxUnsat proof, the
    ## strongest possible verdict, not merely "some real verdict".
    let r = symexFind(destructurePair, tIndexError())
    check r.status == sxUnsat

  test "destructured string-tuple return: deterministic classified degrade, never the walker-fault route":
    let r = symexFind(singleDestructure, tIndexError())
    check r.status == sxUnknown
    check r.errors.len > 0
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "chained dependent scans (the catalog-#6 repro): classified sxUnknown, never a crash":
    let r = symexFind(chained, tIndexError())
    check r.status == sxUnknown
    check r.errors.len > 0
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

suite "symex re-test C6 — walker version pin":

  test "walker version floor >= 81 (round-6 B3 int-result scan-lift closed form)":
    check parseInt(symexWalkerVersion) >= 81

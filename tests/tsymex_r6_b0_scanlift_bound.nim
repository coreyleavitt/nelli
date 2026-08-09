## Round-6 B0 — the v60 scan-lift soundness hotfix.
##
## The landed `tryRecognizeScanIdiom` accepted ANY int-typed loop bound and
## rewrote the loop to Z3 `str.find`, which never raises: per spec it
## returns -1 for out-of-range starts, indistinguishable from "delimiter
## absent". Two shapes therefore reported clean fall-through (false
## `sxUnsat` under tIndexError search) where real Nim raises IndexDefect:
##   (a) bound > s.len — the loop reads s[i] at i == s.len while i < bound;
##   (b) negative scan start — the first s[i] read is OOB.
## v70: the recognizer only accepts a bound that is syntactically the
## scanned string's own `.len` (anything else falls through to k-unroll,
## whose SND-4 index reads deposit honest OOB forks), and the emitted
## closed form prepends a guarded entry-read probe (`if i < bound: s[i]`)
## so a negative start deposits the real IndexDefect fork the loop's first
## iteration would raise. The canonical i=0/bound=s.len shape (every
## pre-existing q1 pin) is unaffected.
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

proc overLenBound(s: string, bound: int) =
  ## (a): unconstrained bound — bound > s.len is satisfiable, and then the
  ## real loop raises IndexDefect at i == s.len.
  var i = 0
  while i < bound and s[i] != ':':
    inc i

proc negStart(s: string, start: int) =
  ## (b): unconstrained start — start < 0 is satisfiable, and then the
  ## real loop's first s[i] read raises IndexDefect.
  var i = start
  while i < s.len and s[i] != ':':
    inc i

proc canonicalScan(s: string) =
  ## The blessed shape: zero start, s.len bound — provably defect-free.
  var i = 0
  while i < s.len and s[i] != ':':
    inc i

suite "symex round-6 B0 — scan-lift bound soundness":

  test "bound > s.len: the IndexDefect is FOUND (was false sxUnsat)":
    let r = symexFind(overLenBound, tIndexError())
    check r.status == sxRaised

  test "negative start: the IndexDefect is FOUND (was false sxUnsat)":
    let r = symexFind(negStart, tIndexError())
    check r.status == sxRaised

  test "canonical zero-start s.len-bound scan still proves (sxUnsat)":
    let r = symexFind(canonicalScan, tIndexError())
    check r.status == sxUnsat

proc chainedNotFound(s: string) =
  ## Round-2 review finding: the closed form ran UNCONDITIONALLY — for a
  ## zero-iteration loop (entry index already past the bound) it clamped
  ## the index to `bound` where real Nim leaves it untouched. The chained
  ## composition hits this exactly: after a not-found first scan,
  ## i == s.len, so the second scan starts at s.len + 1 > bound and must
  ## PRESERVE that value.
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  var j = i + 1
  while j < s.len and s[j] != ';':
    inc j
  if i == s.len and j == s.len + 1:
    symexTarget("j-preserved")

suite "symex round-6 B0 — zero-iteration value preservation":

  test "second scan seeded past the bound preserves its index (SAT)":
    ## Reachable whenever ':' is absent: i lands at s.len, j starts and
    ## stays at s.len + 1. The unguarded clamp made this falsely UNSAT.
    let r = symexFind(chainedNotFound, tLabel("j-preserved"))
    check r.status == sxSat

suite "symex round-6 B0 — walker version pin":

  test "walker version floor >= 70 (scan-lift bound soundness)":
    check parseInt(symexWalkerVersion) >= 70

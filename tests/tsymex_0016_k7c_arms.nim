## RFC-0016 K7c -- every `walkStmt` arm returns `Survivors` (section 8.4, K7).
##
## A refactor: no verdict moves and no walker bump. What K7c makes true is
## that the statement walker has ONE exit channel: `walkStmt` returns
## `Survivors`, so no arm can pass a bare `seq[Path]` (a continuation
## dropped or invented without saying how) out of the walk. The compiler
## holds that for the arms inside `walkStmt`; this file pins the declaration
## and ratchets the arm HELPERS (`walk*Arm`, the follow-concrete walkers)
## that still hand `walkStmt` a `seq[Path]` which it wraps in `exact(`.
## `helperCeiling` only goes down; the remainder is listed in the handoff.
import std/[unittest, os, strutils]
import nelli/symex
import nelli/smt/types
import ./s8cu_helpers

const smtDir = currentSourcePath.parentDir() / ".." / "src" / "nelli" / "smt"

proc runtimeFiles(): seq[string] =
  for f in walkFiles(smtDir / "runtime*.nim"): result.add f

proc walkStmtBody(): seq[string] =
  ## The code lines of `walkStmt`, signature first.
  var on = false
  for raw in readFile(smtDir / "runtime.nim").splitLines():
    if raw.startsWith("proc walkStmt("): on = true
    elif on and raw.len > 0 and raw[0] != ' ': break
    if on:
      let t = raw.strip()
      if t.len > 0 and not t.startsWith("#"): result.add raw

const helperCeiling = 13   ## ratchet: `walkStmt` helpers still on `seq[Path]`

suite "RFC-0016 K7c -- one exit channel":

  test "walkStmt is declared to return Survivors":
    let b = walkStmtBody()
    check b.len > 0
    check b.len > 0 and b[0].endsWith("): Survivors =")

  test "no arm unwraps a Survivors back to seq[Path] inside walkStmt":
    var hits: seq[string]
    let b = walkStmtBody()
    for i in 1 ..< b.len:
      if ").live" in b[i] or b[i].strip().endsWith(".live"):
        hits.add b[i]
    checkpoint($hits)
    check hits.len == 0

  test "every case arm of walkStmt ends in a Survivors expression":
    ## Arms are the two-space `of is...:` lines; each one's tail is read
    ## through the compiler (the return type), so what is pinned here is
    ## that the arm count is the one the census knows.
    var arms = 0
    for t in walkStmtBody():
      if t.startsWith("  of is"): inc arms
    check arms == 27   ## 29 statement kinds; one arm shares three

  test "walkStmt helpers returning seq[Path] only ratchet down":
    var helpers: seq[string]
    for f in runtimeFiles():
      let ls = readFile(f).splitLines()
      var i = 0
      while i < ls.len:
        let raw = ls[i]
        if raw.startsWith("proc walk") and
           (raw.startsWith("proc walkHeapArm(") or
            "Arm(" in raw or "FollowConcrete(" in raw):
          var sig = raw
          var j = i
          while not ls[j].endsWith("=") and j < i + 4:
            inc j
            sig.add " " & ls[j].strip()
          if "): seq[Path]" in sig: helpers.add raw
        inc i
    checkpoint($helpers)
    check helpers.len <= helperCeiling

# ---- the wrapped arms still decide -------------------------------------------

proc k7cBranchLoop(n, x: int) =
  var acc = 0
  var i = 0
  while i < n:
    if x > i: acc = acc + 1 else: acc = acc + 2
    i = i + 1
  if n == 3 and acc == 4:
    symexTarget("k7c_branch_loop")

proc k7cTry(x: int) =
  try:
    if x == 9: raise newException(ValueError, "boom")
  except ValueError:
    symexTarget("k7c_try")

suite "RFC-0016 K7c -- arms still produce the same verdicts":

  test "if/while arms reach a satisfiable target":
    check symexFind(k7cBranchLoop, tLabel("k7c_branch_loop")).status == sxSat

  test "try/raise arms reach the handler":
    check symexFind(k7cTry, tLabel("k7c_try")).status == sxSat

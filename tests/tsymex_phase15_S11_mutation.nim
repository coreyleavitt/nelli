## Phase 15 — Cluster S, cycle S11: string mutation classification + walker
## version bump (CLOSES Cluster S).
##
## Z3 String theory strings are IMMUTABLE (ADR-0006). Two Nim string MUTATION
## operations therefore have no sound symbolic encoding and must be honestly
## classified `seUnsupportedStringOp` → `sxUnknown` (Invariant 3 — never a
## silent UNSAT, never a crash):
##   * `s[i] = c`   — string index ASSIGNMENT (an `nnkAsgn` STATEMENT whose LHS
##                    is `s[i]` on an `itString` receiver). Reason: immutability
##                    (NOT a byte/codepoint mismatch — the model is byte-faithful).
##   * `s.add(c)` / `s.add(otherStr)` — string APPEND call on an `itString`
##                    receiver. Reason: immutability.
## Both reuse the S9/S3 idiom: route to `iekStrUnsupported` carrying the op
## name → the residual `lower` arm raises `SymexUnsupportedStringOpError` → the
## `runSymex` boundary maps it to `sxUnknown` + `seUnsupportedStringOp`.
##
## S11 also performs the Cluster-S walker version bump `"5"` → `"6"`, single-
## sourced in `canonicalize.nim:symexWalkerVersion` (re-exported via symex.nim).
import std/[unittest, strutils]
import proptest/symex

# --- `s[i] = c` index-assign: classified seUnsupportedStringOp -------------
# A SUT with a local `var s: string`; assigning to a string index is the
# immutable-string mutation. (The condition keeps the path reachable so the
# walker actually lowers the mutation statement.)
proc indexAssign(c: char) =
  var s = "abc"
  s[0] = c
  if s == "xbc":
    symexTarget("idxAsg")

# --- `s.add(c)` append a char: classified seUnsupportedStringOp ------------
proc addChar(c: char) =
  var s = "ab"
  s.add(c)
  if s == "abc":
    symexTarget("addC")

# --- `s.add("x")` append a string: classified seUnsupportedStringOp --------
proc addStr() =
  var s = "ab"
  s.add("c")
  if s == "abc":
    symexTarget("addS")

# --- surrounding string path still works: a plain read is unaffected -------
proc plainRead(s: string) =
  if s == "abc":
    symexTarget("plain")

suite "symex Phase 15 S11 — string mutation classified + walker version 6":
  test "s[i] = c index-assign → sxUnknown + seUnsupportedStringOp (no crash/UNSAT)":
    let r = symexFind(indexAssign, tLabel("idxAsg"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seUnsupportedStringOp

  test "s.add(c) char append → sxUnknown + seUnsupportedStringOp":
    let r = symexFind(addChar, tLabel("addC"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seUnsupportedStringOp

  test "s.add(\"x\") string append → sxUnknown + seUnsupportedStringOp":
    let r = symexFind(addStr, tLabel("addS"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seUnsupportedStringOp

  test "surrounding string read unaffected: plain s == \"abc\" is SAT":
    let r = symexFind(plainRead, tLabel("plain"))
    check r.status == sxSat
    check r.witness[0] == "abc"

  test "walker version is \"9\" (S11 to 6; E7 to 7; G10 to 8; Cluster-C close-out C6 to 9; CR-2 to 11)":
    check parseInt(symexWalkerVersion) >= 9

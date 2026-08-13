## RFC-chapulin-hardening Cluster 3, slice M2: `parseBiggestInt(s)` routes to the
## SAME `iekStrToInt` IR that `parseInt(s)` already models. On this (64-bit)
## platform `BiggestInt` is `int64` — identical to `parseInt`'s result type — so
## the two are semantically identical here; M2 only widens `dsl_parser.nim`'s
## name guards (expression match + discarded-call raise fork) from `"parseInt"`
## to `{"parseInt", "parseBiggestInt"}`. `iekStrToInt`'s runtime lowering
## dispatches purely on `e.kind`, never on `e.strOp`, so no runtime.nim change
## was needed — failure-mode parity (the `ValueError` raise on non-numeric
## input) is automatic once the parse-time routing is shared.
##
## RED (pre-fix, empirically confirmed): `parseBiggestInt` had NO dedicated
## match, so `parseBiggestInt(s)` (a call whose sole string-typed arg makes it
## match the string-receiver guard) fell through to the generic
## `getStdlibModelFor`-unregistered catch-all → `mkStrOp(iekStrUnsupported,
## "parseBiggestInt", ...)` → classified `seUnsupportedStringOp` (msg: "string
## op `parseBiggestInt` is not modeled until its Cluster-S cycle") →
## `sxUnknown`. NOT a compile-abort (the CR-2a expr-kind catch-all never
## triggers here — the call node itself is a perfectly well-known `nnkCall`).
##
## GREEN: `parseBiggestInt` now resolves real `sxSat`/`sxUnsat`/`sxRaised`
## verdicts, mirroring `parseInt` exactly (S10a/S10b precedent).
import std/[unittest, strutils]
import nelli/symex

proc nimVPBI(s: string): string =
  ## Ground truth: what Nim's parseBiggestInt actually does with `s`.
  try: "=" & $parseBiggestInt(s) except ValueError: "RAISES"

# --- Happy path: parseBiggestInt(s) == 42 → witness s parses to 42 ----------
proc pbiEq(s: string) =
  if parseBiggestInt(s) == 42:
    symexTarget("pbi")

# --- Negative-prefix regression (mirrors parseInt's S10a parseNeg case) -----
proc pbiNeg(s: string) =
  if s == "-42" and parseBiggestInt(s) == -42:
    symexTarget("pbiNeg")

# --- Failure-mode parity: non-digit input RAISES ValueError (S10b shape) ----
proc pbiNonDigit(s: string) =
  if s == "abc":
    let n = parseBiggestInt(s)
    symexTarget("pbiND")

# --- UNSAT soundness: s pinned to "100" contradicts parseBiggestInt(s)==42 --
proc pbiUnsat(s: string) =
  if s == "100" and parseBiggestInt(s) == 42:
    symexTarget("pbiUnsat")

# --- Discard-raise-fork parity (mirrors tsymex_discard_raise.nim D1/D2) -----
proc sutDiscardThenAfterPBI(s: string) =
  discard parseBiggestInt(s)
  symexTarget("afterPBI")

# --- Regression: a concrete VALID discard must not spuriously raise --------
proc sutDiscardValidPBI(n: int) =
  discard parseBiggestInt("512")
  if n == 5:
    symexTarget("okPBI")

suite "symex RFC-chapulin-hardening M2 — parseBiggestInt via iekStrToInt":

  test "M2-1: parseBiggestInt(s) == 42 is SAT with witness s parsing to 42":
    let r = symexFind(pbiEq, tLabel("pbi"))
    check r.status == sxSat
    check r.witness[0] == "42"
    check nimVPBI(r.witness[0]) == "=42"   # SOUND: witness truly parses to 42

  test "M2-2: parseBiggestInt(\"-42\") produces sxSat with int value -42":
    let r = symexFind(pbiNeg, tLabel("pbiNeg"))
    check r.status == sxSat
    check r.witness[0] == "-42"

  test "M2-3 (failure-mode parity): non-digit input RAISES ValueError (sxRaised)":
    ## Mirrors parseInt's S10b: parseBiggestInt("abc") raises ValueError
    ## identically to parseInt — proving the shared iekStrToInt raise-path is
    ## NOT just the happy path.
    let r = symexFind(pbiNonDigit, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check nimVPBI(r.raisedWitness[0]) == "RAISES"

  test "M2-4 (UNSAT soundness): s pinned to \"100\" contradicts ==42":
    ## Proves REAL modeling (not a trivial always-SAT/always-unknown stub):
    ## parseBiggestInt("100") is forced to 100, contradicting ==42.
    let r = symexFind(pbiUnsat, tLabel("pbiUnsat"))
    check r.status == sxUnsat

  test "M2-5 (discard parity): discarded parseBiggestInt RAISES for non-numeric input":
    let r = symexFind(sutDiscardThenAfterPBI, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check nimVPBI(r.raisedWitness[0]) == "RAISES"

  test "M2-6 (discard parity): SOUND — afterPBI reachable only via parseable string":
    let r = symexFind(sutDiscardThenAfterPBI, tLabel("afterPBI"))
    check r.status == sxSat
    check nimVPBI(r.witness[0]) != "RAISES"

  test "M2-7: regression — concrete valid discard does not spuriously raise":
    let r = symexFind(sutDiscardValidPBI, tLabel("okPBI"))
    check r.status == sxSat
    check r.witness[0] == 5

  test "M2-8: symexWalkerVersion floor (>=48)":
    check parseInt(symexWalkerVersion) >= 48

## Phase 15 — Cluster S, cycle S9 (perturbation for Phase 16 A9).
##
## `toLower`/`toUpper` (std/unicode) have NO Z3 native full-Unicode fold
## primitive and remain classified `seUnsupportedStringOp` → sxUnknown
## (Invariant 3 — never a silent UNSAT, never a crash).
##
## `toLowerAscii`/`toUpperAscii` (std/strutils) are NOW MODELED via a
## quantifier-free BV18-ITE seqMap (Phase 16 A9, ADR-0015). They lower to
## sxSat with a correct witness: `toLowerAscii("Abc") == "abc"`,
## `toUpperAscii("Abc") == "ABC"`.
##
## S9 ONLY classifies the unicode ops; the surrounding string path (plain
## `s == "lit"`) still solves normally (sxSat).
import std/[unittest, strutils, unicode]
import proptest/symex

# --- toLower → classified unsupported (sxUnknown, not crash, not silent UNSAT) ---
proc toLowerEq(s: string) =
  if s.toLower == "abc":
    symexTarget("low")

# --- toLowerAscii (std/strutils) parallel ---
proc toLowerAsciiEq(s: string) =
  if s.toLowerAscii == "abc":
    symexTarget("lowA")

# --- toUpper → classified unsupported ---
proc toUpperEq(s: string) =
  if s.toUpper == "ABC":
    symexTarget("up")

# --- toUpperAscii (std/strutils) parallel ---
proc toUpperAsciiEq(s: string) =
  if s.toUpperAscii == "ABC":
    symexTarget("upA")

# --- the surrounding string path is unaffected: plain == still solves ---
proc plainEq(s: string) =
  if s == "abc":
    symexTarget("plain")

suite "symex Phase 15 S9 — toLower/toUpper classified seUnsupportedStringOp":
  test "toLower: classified seUnsupportedStringOp → sxUnknown (no crash/UNSAT)":
    let r = symexFind(toLowerEq, tLabel("low"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seUnsupportedStringOp

  test "toLowerAscii: now modeled (A9) → sxSat with correct witness":
    ## Phase 16 A9 (ADR-0015): toLowerAscii now lowers via seqMapBody BV18-ITE.
    ## The witness must satisfy `s.toLowerAscii == "abc"`.
    let r = symexFind(toLowerAsciiEq, tLabel("lowA"))
    check r.status == sxSat
    check r.witness[0].toLowerAscii == "abc"

  test "toUpper: classified seUnsupportedStringOp → sxUnknown":
    let r = symexFind(toUpperEq, tLabel("up"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seUnsupportedStringOp

  test "toUpperAscii: now modeled (A9) → sxSat with correct witness":
    ## Phase 16 A9 (ADR-0015): toUpperAscii now lowers via seqMapBody BV18-ITE.
    ## The witness must satisfy `s.toUpperAscii == "ABC"`.
    let r = symexFind(toUpperAsciiEq, tLabel("upA"))
    check r.status == sxSat
    check r.witness[0].toUpperAscii == "ABC"

  test "surrounding string path unaffected: plain s == \"abc\" is SAT":
    let r = symexFind(plainEq, tLabel("plain"))
    check r.status == sxSat
    check r.witness[0] == "abc"

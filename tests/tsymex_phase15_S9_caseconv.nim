## Phase 15 — Cluster S, cycle S9: `toLower` / `toUpper` classified unsupported.
##
## Nim's case-folding string ops — `toLower`/`toUpper` (std/unicode) and the
## ASCII-only `toLowerAscii`/`toUpperAscii` (std/strutils) — have NO Z3 native
## case-folding primitive (ADR-0006; a regex-range approximation is deferred to
## Phase 16). Per Invariant 3 they must lower to a CLASSIFIED
## `seUnsupportedStringOp` error → `sxUnknown` — never a silent UNSAT, never a
## crash. This reuses the existing `iekStrUnsupported` / `SymexUnsupportedStringOpError`
## mechanism (an unrecognised `itString`-receiver call routes to `iekStrUnsupported`,
## which the runSymex boundary maps to `seUnsupportedStringOp`).
##
## S9 ONLY classifies these case-conv ops; the surrounding string path (plain
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

  test "toLowerAscii: classified seUnsupportedStringOp → sxUnknown":
    let r = symexFind(toLowerAsciiEq, tLabel("lowA"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seUnsupportedStringOp

  test "toUpper: classified seUnsupportedStringOp → sxUnknown":
    let r = symexFind(toUpperEq, tLabel("up"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seUnsupportedStringOp

  test "toUpperAscii: classified seUnsupportedStringOp → sxUnknown":
    let r = symexFind(toUpperAsciiEq, tLabel("upA"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seUnsupportedStringOp

  test "surrounding string path unaffected: plain s == \"abc\" is SAT":
    let r = symexFind(plainEq, tLabel("plain"))
    check r.status == sxSat
    check r.witness[0] == "abc"

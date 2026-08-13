## Phase 15 — Cluster S, cycle S4: string substring predicates + search.
##
## Wires the four substring-predicate / substring-search operations directly to
## their Z3 String-theory equivalents (no stdlib model lookup — direct dispatch):
##   * `s.contains(sub)` / `sub in s` → Z3 `(seq.contains s sub)`     → svBool
##   * `s.startsWith(p)`              → Z3 `(seq.prefixof p s)`        → svBool
##   * `s.endsWith(q)`                → Z3 `(seq.suffixof q s)`        → svBool
##   * `s.find(sub)` (strutils.find)  → Z3 `indexOf`, −1 when absent   → svInt
##
## Byte-faithful (ADR-0006): under the ≤0xFF char-range constraint asserted on
## every free string, a byte offset equals a Z3 position offset, so `find`'s
## return value is a Nim byte index with no codepoint adjustment.
##
## Critical routing check: `sub in s` over an `itString` receiver semchecks to
## `contains(s, sub)` and MUST lower to `iekStrContains` (the Z3 String path),
## NOT `iekContains` (the seq/table/set membership path).
import std/unittest
import std/strutils  ## contains/find/startsWith/endsWith on strings
import nelli/symex

# --- contains: gate on substring membership ---
proc containsEll(s: string) =
  if s.contains("ell"):
    symexTarget("hit")

proc containsContradiction(s: string) =
  if s == "world" and s.contains("ell"):
    symexTarget("hit")

# --- `sub in s` routing: must take the string-contains path ---
proc inEll(s: string) =
  if "ell" in s and s == "hello":
    symexTarget("hit")

# --- startsWith ---
proc startsHe(s: string) =
  if s == "hello" and s.startsWith("he"):
    symexTarget("hit")

proc startsXy(s: string) =
  if s == "hello" and s.startsWith("xy"):
    symexTarget("hit")

# --- endsWith ---
proc endsLo(s: string) =
  if s == "hello" and s.endsWith("lo"):
    symexTarget("hit")

# --- find: present → byte offset ---
proc findBc(s: string) =
  if s == "abc" and s.find("bc") == 1:
    symexTarget("hit")

# --- find: absent → -1, no crash ---
proc findAbsent(s: string) =
  if s == "abc" and s.find("zz") == -1:
    symexTarget("hit")

suite "symex Phase 15 S4 — string find/contains/startsWith/endsWith":
  test "contains: s.contains(\"ell\") is SAT (a string with ell exists)":
    let r = symexFind(containsEll, tLabel("hit"))
    check r.status == sxSat

  test "contains contradiction: \"world\".contains(\"ell\") is UNSAT":
    let r = symexFind(containsContradiction, tLabel("hit"))
    check r.status == sxUnsat

  test "`sub in s` routes to iekStrContains (string path) and is SAT":
    let r = symexFind(inEll, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "hello"

  test "startsWith: \"hello\".startsWith(\"he\") is SAT":
    let r = symexFind(startsHe, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "hello"

  test "startsWith contradiction: \"hello\".startsWith(\"xy\") is UNSAT":
    let r = symexFind(startsXy, tLabel("hit"))
    check r.status == sxUnsat

  test "endsWith: \"hello\".endsWith(\"lo\") is SAT":
    let r = symexFind(endsLo, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "hello"

  test "find: \"abc\".find(\"bc\") == 1 is SAT (byte offset)":
    let r = symexFind(findBc, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "abc"

  test "find absent: \"abc\".find(\"zz\") == -1 is SAT (no crash, -1 sentinel)":
    let r = symexFind(findAbsent, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "abc"

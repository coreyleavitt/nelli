## Chapulin round-4 backlog item 1 (walker v65) — CHAR needles for the
## string-search family. Half of strutils' search overloads take a `char`
## (`s.find(']')`, `s.rfind(':')`, `s.contains('x')`, …); the needle lowers
## as svBV8 and the former bare `doAssert sub.kind == svString` at the
## `runtime_strings.nim` needle sites was an uncaught AssertionDefect —
## the FIRST walker-backlog entry the round-3 Defect net caught in the
## field (chapulin's real `parseTftpUri`, `rest.find(']')`). v65 bridges a
## BV8 char to the 1-char string via `(str.from_code codepoint)` — exact
## under the ≤0xFF byte-faithful constraint (ADR-0006).
##
## The UNSAT tests are load-bearing soundness pins: a stub that fabricated
## an unconstrained result would report them sxSat.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

proc findColonAt2(s: string) =
  if s.find(':') == 2:
    symexTarget("colon-at-2")

proc findNeverMinus2(s: string) =
  ## `find` returns -1 or a valid index — never -2.
  if s.find(':') == -2:
    symexTarget("impossible-find")

proc rfindColonAt0(s: string) =
  ## Last colon at index 0 — exactly one colon, at the front.
  if s.rfind(':') == 0:
    symexTarget("last-colon-front")

proc containsAt(s: string) =
  if s.contains('@'):
    symexTarget("has-at")

proc containsInEmpty(s: string) =
  ## An empty string contains no character.
  if s.len == 0 and s.contains('@'):
    symexTarget("impossible-contains")

suite "symex re-test v65 — char-needle string search (was a native crash)":

  test "s.find(':') == 2 is SAT with a consistent witness":
    let r = symexFind(findColonAt2, tLabel("colon-at-2"))
    check r.status == sxSat
    check r.witness[0].find(':') == 2

  test "s.find(':') == -2 is UNSAT (soundness)":
    let r = symexFind(findNeverMinus2, tLabel("impossible-find"))
    check r.status == sxUnsat

  test "s.rfind(':') == 0 is SAT with a consistent witness":
    let r = symexFind(rfindColonAt0, tLabel("last-colon-front"))
    check r.status == sxSat
    check r.witness[0].rfind(':') == 0

  test "s.contains('@') is SAT with a consistent witness":
    let r = symexFind(containsAt, tLabel("has-at"))
    check r.status == sxSat
    check r.witness[0].contains('@')

  test "empty-string contains('@') is UNSAT (soundness)":
    let r = symexFind(containsInEmpty, tLabel("impossible-contains"))
    check r.status == sxUnsat

suite "symex re-test v65 — walker version pin":

  test "walker version floor >= 65 (char-needle bridge)":
    check parseInt(symexWalkerVersion) >= 65

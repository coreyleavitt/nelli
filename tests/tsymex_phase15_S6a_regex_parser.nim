## Phase 15 — Cluster S, cycle S6a: standalone Nim-regex → Z3-regex parser.
##
## Direct unit tests for `parseNimRegexToZ3Regex` (NO `symexFind` / walker).
## Imports `nelli/smt/regex_parser` directly — the module is standalone
## (no `runtime.nim`/`symex.nim` import). We only assert that parsing succeeds
## (`isOk`) and yields a non-empty Z3 regex AST for supported constructs, and
## that the three rejected families return `isOk == false` with a descriptive
## message. We do NOT solve / execute the regex here.
##
## Byte-faithful (ADR-0006): `.`, `[...]`, `\d`, `\w`, `\s` operate over bytes
## (≤ 0xFF). See regex_parser.nim's module doc and the reconciliation §F-S note.
import std/unittest
import std/strutils
import z3/context
import nelli/smt/regex_parser

# A parsed regex stringifies to its SMT-LIB AST; a successful parse must yield
# a non-trivial, non-empty rendering (sanity that the AST was actually built).
proc rendersNonEmpty(r: RegexParseResult): bool =
  r.isOk and ($r.regex).len > 0

suite "symex Phase 15 — S6a regex parser (standalone)":
  # One context for the whole suite; the byte-faithful AST is built against it.
  let ctx = newContext()
  discard ctx

  # --- supported constructs ---

  test "parser: literal string":
    let r = parseNimRegexToZ3Regex("abc")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: dot -> any byte":
    let r = parseNimRegexToZ3Regex(".")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: [a-z] -> range":
    let r = parseNimRegexToZ3Regex("[a-z]")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: star":
    let r = parseNimRegexToZ3Regex("a*")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: plus":
    let r = parseNimRegexToZ3Regex("a+")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: question":
    let r = parseNimRegexToZ3Regex("a?")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: alternation -> union":
    let r = parseNimRegexToZ3Regex("a|b")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: {2,5} -> loop":
    let r = parseNimRegexToZ3Regex("a{2,5}")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: {3} -> exact loop":
    let r = parseNimRegexToZ3Regex("a{3}")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: \\d -> digit range":
    let r = parseNimRegexToZ3Regex(r"\d")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: \\w -> word union":
    let r = parseNimRegexToZ3Regex(r"\w")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: \\s -> whitespace union":
    let r = parseNimRegexToZ3Regex(r"\s")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: [^abc] -> complement":
    let r = parseNimRegexToZ3Regex("[^abc]")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: (?:...) non-capturing transparent":
    let r = parseNimRegexToZ3Regex("(?:abc)+")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: (...) capturing transparent":
    let r = parseNimRegexToZ3Regex("(ab)|c")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: escaped metachar is literal":
    let r = parseNimRegexToZ3Regex(r"a\.b\*")
    check r.isOk
    check rendersNonEmpty(r)

  test "parser: composite a[0-9]+\\w*":
    let r = parseNimRegexToZ3Regex(r"a[0-9]+\w*")
    check r.isOk
    check rendersNonEmpty(r)

  # --- rejected constructs ---

  test "parser: backreference -> Err seUnsupportedRegex":
    let r = parseNimRegexToZ3Regex(r"(.)\1")
    check (not r.isOk)
    check "backreference" in r.error
    check "seUnsupportedRegex" in r.error

  test "parser: lookahead -> Err seUnsupportedRegex":
    let r = parseNimRegexToZ3Regex("foo(?=bar)")
    check (not r.isOk)
    check "lookahead" in r.error
    check "seUnsupportedRegex" in r.error

  test "parser: named group (?P<n>x) -> Err seUnsupportedRegex":
    let r = parseNimRegexToZ3Regex("(?P<n>x)")
    check (not r.isOk)
    check "named group" in r.error
    check "seUnsupportedRegex" in r.error

  test "parser: named group (?<n>x) -> Err seUnsupportedRegex":
    let r = parseNimRegexToZ3Regex("(?<n>x)")
    check (not r.isOk)
    check "named group" in r.error
    check "seUnsupportedRegex" in r.error

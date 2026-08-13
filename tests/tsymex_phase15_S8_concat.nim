## Phase 15 — Cluster S, cycle S8: `&` string concatenation.
##
## Wires Nim's `&` operator on `string` operands to Z3's `Z3_mk_seq_concat`
## (nim-z3 `concat` / `&` on `Z3String`):
##   `a & b`  →  SymVal(svString, concat(a.str, b.str))
##
## Covers `string & string`, `string & "lit"`, `"lit" & string`, and the
## chained left-associative `a & b & c` form (the typed AST nests each `&` as a
## binary node). The existing seq-concat / other-type `&` paths are NOT affected
## — the parser only intercepts `&` when BOTH operands classify as `itString`.
##
## Byte-faithful (ADR-0006): concat length is additive over byte counts, so
## `(a & b).len == a.len + b.len` (uses S3's `iekStrLen`).
import std/unittest
import nelli/symex

# --- literal & literal: "foo" & "bar" == "foobar" ---
proc litConcat(s: string) =
  if s == "foo" & "bar":
    symexTarget("hit")

# --- variable concat with a pinned prefix → solves for the suffix ---
proc varConcat(a, b: string) =
  if (a & b) == "hello" and a == "he":
    symexTarget("hit")

# --- chained left-associative concat ---
proc chainedConcat(s: string) =
  if s == "a" & "b" & "c":
    symexTarget("hit")

# --- length is additive over concat (S3 len) ---
proc concatLen(a, b: string) =
  if (a & b).len == a.len + b.len:
    symexTarget("hit")

# --- contradiction: a result can't be shorter than a fixed-length prefix ---
proc concatContradiction(a, b: string) =
  if (a & b) == "xy" and a == "zzz":
    symexTarget("hit")

suite "symex Phase 15 S8 — `&` string concatenation":
  test "literal concat: s == \"foo\" & \"bar\" is SAT with witness \"foobar\"":
    let r = symexFind(litConcat, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "foobar"

  test "variable concat: (a & b) == \"hello\" and a == \"he\" → b == \"llo\"":
    let r = symexFind(varConcat, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "he"
    check r.witness[1] == "llo"

  test "chained concat: \"a\" & \"b\" & \"c\" == \"abc\" is SAT":
    let r = symexFind(chainedConcat, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "abc"

  test "concat length is additive: (a & b).len == a.len + b.len is SAT":
    let r = symexFind(concatLen, tLabel("hit"))
    check r.status == sxSat

  test "concat contradiction: (a & b) == \"xy\" and a == \"zzz\" is UNSAT":
    let r = symexFind(concatContradiction, tLabel("hit"))
    check r.status == sxUnsat

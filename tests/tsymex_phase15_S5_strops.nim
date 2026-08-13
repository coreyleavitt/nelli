## Phase 15 — Cluster S, cycle S5: string replace / replaceAll / split / join.
##
## The densest Cluster-S cycle. Wires the four replacement / sequence-decomposition
## operations:
##   * `s.replace(old, new)`   → Z3 `(seq.replace s old new)` first-occurrence  → svString
##   * `s.replaceAll(old, new)`→ Z3 `(seq.replace_all …)` — VERSION-GATED: on a
##                               build without `-d:z3WithSeqReplaceAll` (this one),
##                               yields sxUnknown + seZ3VersionMissing (never a crash).
##   * `s.split(sep)`          → symbolic `seq[string]`; tractable special cases:
##                               (a) empty-sep → single-byte parts; (b) concrete
##                               input + length-1 concrete sep → concrete inline parts.
##                               General symbolic split → seZ3StringIncomplete (sxUnknown).
##   * `xs.join(sep)`          → Z3 concat of `xs` with `sep` interleaved          → svString
##
## Byte-faithful (ADR-0006): offsets/lengths are bytes; `split("abc","")` yields
## single-BYTE parts `@["a","b","c"]`.
import std/unittest
import std/strutils  ## replace/split/join on strings
import nelli/symex

# Nim's `strutils.replace` is already global (all-occurrence) and there is no
# `replaceAll` in the stdlib. The symex parser dispatches on the *callee name*
# for an `itString` receiver, so a local `replaceAll` shim routes to
# `smkStrReplaceAll` → `iekStrReplaceAll` (the version-gated path under test).
# The body never runs under symex (the walker models the call, not its source).
proc replaceAll(s, old, neu: string): string =
  s.replace(old, neu)

# --- replace: first-occurrence ---
proc replaceFoo(s: string) =
  if s == "foofoo" and s.replace("foo", "bar") == "barfoo":
    symexTarget("hit")

# --- replaceAll: version-gated (this build lacks the gate → seZ3VersionMissing) ---
proc replaceAllFoo(s: string) =
  if s == "foofoo" and s.replaceAll("foo", "bar") == "barbar":
    symexTarget("hit")

# --- split: concrete-inline path (concrete input, length-1 concrete sep) ---
# The receiver is a string LITERAL, so the walker takes the concrete-inline
# path: it computes the parts in Nim and emits a concrete `seq[string]` — no
# Z3 universal quantifier. `s` is present only so the witness has a parameter.
proc splitConcreteLen(s: string) =
  if s == "x":
    let parts = "a,b,c".split(",")
    if parts.len == 3:
      symexTarget("hit")

proc splitConcreteElem(s: string) =
  if s == "x":
    let parts = "a,b,c".split(",")
    if parts.len == 3 and parts[0] == "a" and parts[2] == "c":
      symexTarget("hit")

# --- split: empty-sep special case → single-byte parts ---
proc splitEmptySep(s: string) =
  if s == "x":
    let parts = "abc".split("")
    if parts.len == 3 and parts[0] == "a" and parts[1] == "b" and parts[2] == "c":
      symexTarget("hit")

# --- join over a concrete seq[string] result (split round-trip stays in Z3String) ---
proc splitJoinRoundtrip(s: string) =
  if s == "x" and "a,b,c".split(",").join(",") == "a,b,c":
    symexTarget("hit")

# --- general symbolic split → seZ3StringIncomplete (sxUnknown), never a hang ---
proc splitSymbolic(s: string, sep: string) =
  let parts = s.split(sep)
  if parts.len == 2:
    symexTarget("hit")

suite "symex Phase 15 S5 — string replace/replaceAll/split/join":
  test "replace: replace(\"foofoo\",\"foo\",\"bar\") == \"barfoo\" (first-occ)":
    let r = symexFind(replaceFoo, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "foofoo"

  test "replaceAll: emits seZ3VersionMissing on this Z3 build (no crash)":
    let r = symexFind(replaceAllFoo, tLabel("hit"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seZ3VersionMissing

  test "split: split(\"a,b,c\",\",\") has len 3 (concrete-inline path)":
    let r = symexFind(splitConcreteLen, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "x"

  test "split: split(\"a,b,c\",\",\") parts are a,b,c (concrete-inline, no quantifier)":
    let r = symexFind(splitConcreteElem, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "x"

  test "split empty-sep: split(\"abc\",\"\") yields single-byte parts @[\"a\",\"b\",\"c\"]":
    let r = symexFind(splitEmptySep, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "x"

  test "join: split(\"a,b,c\",\",\").join(\",\") == \"a,b,c\" round-trip":
    let r = symexFind(splitJoinRoundtrip, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "x"

  test "split general symbolic: classified seZ3StringIncomplete → sxUnknown (no hang)":
    let r = symexFind(splitSymbolic, tLabel("hit"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seZ3StringIncomplete

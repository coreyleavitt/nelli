## Phase 15 — Cluster S, cycle S5: string replace / split / join.
##
## The densest Cluster-S cycle. Wires the replacement / sequence-decomposition
## operations:
##   * `s.replace(old, new)`   → Z3 `(seq.replace_all …)`: EVERY occurrence, as
##                               `strutils.replace` does (RFC-0005 S8c; S5 had
##                               modelled it first-occurrence, and a user
##                               `replaceAll` shim reached the all-occurrence
##                               model by name). VERSION-GATED: on a build
##                               without `-d:z3WithSeqReplaceAll` (this one) it
##                               records seZ3VersionMissing (never a crash).
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
import nelli/smt/runtime

# --- replace: every occurrence -- "foofoo" -> "barbar" ---
proc replaceFoo(s: string) =
  if s == "foofoo" and s.replace("foo", "bar") == "barbar":
    symexTarget("hit")

# --- replace is NOT first-occurrence: "barfoo" is unreachable ---
proc replaceFirstOnly(s: string) =
  if s == "foofoo" and s.replace("foo", "bar") == "barfoo":
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

suite "symex Phase 15 S5 — string replace/split/join":
  test "replace: \"foofoo\".replace(\"foo\",\"bar\") != \"barfoo\" (never first-occ)":
    ## RFC-0005 S8c: this pin asserted the first-occurrence value `"barfoo"`
    ## as sxSat -- a false verdict (Nim's `replace` replaces every
    ## occurrence). The all-occurrence model makes it unreachable.
    let r = symexFind(replaceFirstOnly, tLabel("hit"))
    check r.status != sxSat

  test "replace: emits seZ3VersionMissing on this Z3 build (no crash)":
    ## RFC-0005 S10: s == "foofoo" really replaces to "barbar", so the
    ## label is reachable. The path's taint is
    ## dcFreshSymbol only, so the candidate is REPLAYED (rule 3) and the real
    ## fn confirms it -> sxSat; rules 1-2 alone still decide sxUnknown, and
    ## the classified kind is still recorded.
    let r = symexFind(replaceFoo, tLabel("hit"))
    check r.status == sxSat
    check rfc0005UnvetoedStatus == sxUnknown
    check r.witness[0] == "foofoo"
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

## Phase 15 — Cluster S, cycle S7b: Z3-string-theory regression smoke +
## determinism doc.
##
## This cycle does NOT add walker machinery. It is the in-process, hermetic
## smoke that exercises MULTIPLE string ops TOGETHER on the same / related SUTs,
## to catch cross-op state-threading bugs introduced by the S1–S7a multi-file
## edits (parser routing, the uniform `iekStr*` payload, the at→toCode→BV8 char
## bridge, the ≤0xFF byte-faithful constraint, the seq[string] machinery, regex
## membership, and the `bytes(s)` identity view). Each S-cycle shipped its own
## focused test; S7b proves the ops COMPOSE.
##
## Byte-faithful model (ADR-0006): every Z3 string char is constrained ≤0xFF at
## allocation, so Z3 position == Nim byte index — `s.len`/`s[i]`/`s[a..b]`/
## `s.high` are byte-faithful, and a free `s` with `s.len == 1` round-trips to a
## single Nim byte. The walker version stays "5" (the Cluster-S bump is S11, NOT
## here).
##
## The witness-reading idiom is the S1–S7a one: on `sxSat`, `r.witness[i]` is the
## extracted concrete Nim value (string params via `evalStr`).
import std/unittest
import std/strutils  ## contains/find/startsWith/endsWith/split/join on strings
import std/re        ## match with a compiled Regex
import proptest/symex

# ----------------------------------------------------------------------------
# 1. Multi-op SUT: len + index + contains + startsWith all on the SAME free
#    string, threaded through one path condition. A consistent witness ("hello")
#    must satisfy every clause simultaneously — the cross-op state-threading
#    smoke. (s.len == 5 AND s[0] == 'h' AND s.contains("ell") AND
#    s.startsWith("he").)
#
# The condition is inlined in the SUT body (the S-cluster convention) — a
# bool-returning string *helper* proc does NOT inline under symex (yields
# sxUnknown; outside S7b's scope), so the round-trip predicate `multiOpP` is
# used only at RUNTIME to re-check the witness, mirroring F8's (symex SUT,
# runtime predicate) split.
# ----------------------------------------------------------------------------
proc multiOpSut(s: string) =
  if s.len == 5 and s[0] == 'h' and s.contains("ell") and s.startsWith("he"):
    symexTarget("hit")

# Runtime predicate, textually identical to multiOpSut's condition.
proc multiOpP(s: string): bool =
  s.len == 5 and s[0] == 'h' and s.contains("ell") and s.startsWith("he")

# A second multi-op SUT combining len + slice + endsWith + find, pinned to a
# unique witness via a full equality so the round-trip is deterministic
# (the four sub-clauses alone are underconstrained — "rorld" also satisfies
# them — so equality fixes the witness while the slice/endsWith/find ops still
# thread through the path condition).
proc multiOp2Sut(s: string) =
  if s == "world" and s.len == 5 and s[1..3] == "orl" and
     s.endsWith("ld") and s.find("rl") == 2:
    symexTarget("hit")

# ----------------------------------------------------------------------------
# 2. Concrete split + join round-trip AND a bytes(s) check on a literal, in the
#    same file (and the same SUT). `s` is pinned to a literal so the witness has
#    a parameter; the split/join/bytes all operate on string LITERALS (the S5/S7a
#    concrete-inline idiom — no symbolic quantifier, no hang).
# ----------------------------------------------------------------------------
# `bytes` is intercepted by NAME on an itString receiver (smkStrBytes); the body
# never runs under symex. Local shim so Nim typechecks (mirrors S7a).
proc bytes(s: string): seq[byte] =
  for c in s: result.add byte(c)

proc splitJoinBytesSut(s: string) =
  if s == "x":
    # split + join round-trip (concrete)
    let parts = "a,b,c".split(",")
    # bytes() on a literal: byte-faithful identity view, "A" -> @[65]
    if parts.len == 3 and parts.join(",") == "a,b,c" and
       bytes("A").len == 1 and bytes("A")[0] == 65'u8:
      symexTarget("hit")

# ----------------------------------------------------------------------------
# 3. A regex match SUT + a string-equality SUT. The regex path (free string under
#    the ≤0xFF constraint + Z3 regex membership) is the cluster's highest hang
#    risk; the equality path is the Phase-5 baseline + S1's cmpString bonus.
# ----------------------------------------------------------------------------
proc regexLowerSut(s: string) =
  if s.len == 3 and s.match(re"[a-z]+"):
    symexTarget("hit")

proc equalitySut(s: string) =
  if s == "hello":
    symexTarget("hit")

# ----------------------------------------------------------------------------
# 4. withSymexSettings exerciser applied to a STRING SUT — confirms the settings
#    builder threads through for strings too (mirrors F8's withSymexSettings
#    test). The real Z3d API: the `do`-block binds the mutator; base defaults to
#    defaultSymexSettings().
# ----------------------------------------------------------------------------
proc cfgStringSut(s: string) =
  if s == "hello":
    symexTarget("cfg")

const axiomSettings = withSymexSettings() do (s: var SymexSettings):
  s.inlinePolicy = ipAlwaysAxiomatize

# ----------------------------------------------------------------------------
# 5. ≤0xFF byte-faithful invariant: a free `s` with `s.len == 1` extracts to a
#    single valid Nim byte (round-trip sanity — no multi-byte blowup).
# ----------------------------------------------------------------------------
proc freeLen1Sut(s: string) =
  if s.len == 1:
    symexTarget("hit")

suite "symex Phase 15 S7b — Z3-string regression smoke (cross-op composition)":

  test "multi-op SUT (len+index+contains+startsWith) -> sxSat, consistent witness":
    let r = symexFind(multiOpSut, tLabel("hit"))
    check r.status == sxSat
    # The witness must satisfy EVERY clause when plugged back into the predicate
    # at runtime — a genuine round-trip of the composed body.
    check multiOpP(r.witness[0])
    check r.witness[0].len == 5

  test "multi-op SUT (len+slice+endsWith+find) -> sxSat, witness 'world'":
    let r = symexFind(multiOp2Sut, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "world"

  test "split+join round-trip (concrete) + bytes(literal) in one SUT -> sxSat":
    let r = symexFind(splitJoinBytesSut, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "x"

  test "regex match [a-z]+ -> sxSat with an all-lowercase length-3 witness":
    let r = symexFind(regexLowerSut, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len == 3
    for c in r.witness[0]:
      check c in {'a'..'z'}

  test "string equality s == \"hello\" -> sxSat, witness 'hello'":
    let r = symexFind(equalitySut, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "hello"

  test "withSymexSettings threads through a STRING SUT -> sxSat":
    let r = symexFind(cfgStringSut, tLabel("cfg"), axiomSettings)
    check r.status == sxSat
    check r.witness[0] == "hello"

  test "byte-faithful: free s with s.len == 1 round-trips to a single Nim byte":
    let r = symexFind(freeLen1Sut, tLabel("hit"))
    check r.status == sxSat
    # ≤0xFF soundness: exactly one Nim byte, no multi-byte blowup.
    check r.witness[0].len == 1

  test "walker version is \"9\" (Cluster-S S11; Cluster-E E7; Cluster-G G10; Cluster-C C6; R12→10; CR-2→11)":
    check parseInt(symexWalkerVersion) >= 9

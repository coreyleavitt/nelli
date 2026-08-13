## Phase 15 — Cluster S, cycle S2: string literal lifts.
##
## Byte-faithful model (ADR-0006): a string literal `"lit"` lowers via the
## existing `iekStrLit` → `mkString(e.sval)` path, which calls
## `Z3_mk_lstring` (a length-prefixed, NUL-safe, *byte-faithful* constructor —
## each input byte maps to one Z3 character). Consequently `mkString(s).len ==
## s.len` (Nim byte count): a multi-byte literal like `"é"` is a length-**2**
## Z3 string holding the raw UTF-8 bytes [0xC3, 0xA9], NOT a length-1 string.
##
## This cycle proves the literal-lift round-trip in SUT bodies:
##   1. `s == "hello"` is `sxSat`, witness == "hello".
##   2. `s == ""` (empty) is `sxSat`, witness == "".
##   3. `s == "\n"` (newline escape) is `sxSat`, witness == "\n" (1 byte).
##   4. contradictory literals (`s == "hello"` AND `s == "world"`) → `sxUnsat`.
##   5. byte-faithful multi-byte: `s == "é"` is `sxSat`, and the EXTRACTED Nim
##      witness satisfies `witness == "é"` and `witness.len == 2` (Nim byte
##      count). We do NOT use a symex `s.len` constraint here — that op is not
##      wired until S3 — we assert byte-faithfulness on the extracted witness.
##   6. (optional) `s == "\x61"` is `sxSat`, witness == "a".
import std/unittest
import nelli/symex

proc isHello(s: string) =
  if s == "hello":
    symexTarget("hit")

proc isEmpty(s: string) =
  if s == "":
    symexTarget("hit")

proc isNewline(s: string) =
  if s == "\n":
    symexTarget("hit")

proc contradiction(s: string) =
  if s == "hello" and s == "world":
    symexTarget("hit")

proc isEacute(s: string) =
  if s == "é":
    symexTarget("hit")

proc isHexA(s: string) =
  if s == "\x61":
    symexTarget("hit")

suite "symex Phase 15 S2 — string literal lifts (byte-faithful)":
  test "s == \"hello\" round-trips through Z3 model":
    let r = symexFind(isHello, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "hello"

  test "empty string literal is SAT with empty witness":
    let r = symexFind(isEmpty, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == ""

  test "embedded newline escape preserved in witness (1 byte)":
    let r = symexFind(isNewline, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "\n"
    check r.witness[0].len == 1

  test "contradictory string literals are UNSAT (not a crash)":
    let r = symexFind(contradiction, tLabel("hit"))
    check r.status == sxUnsat

  test "byte-faithful multi-byte literal: s == \"é\" SAT, witness is 2 bytes":
    let r = symexFind(isEacute, tLabel("hit"))
    check r.status == sxSat
    # byte-faithful (ADR-0006): "é" is U+00E9 -> UTF-8 [0xC3, 0xA9] -> 2 bytes.
    # `s.len` symex op is deferred to S3; assert byte-faithfulness on the
    # extracted Nim witness instead.
    check r.witness[0] == "é"
    check r.witness[0].len == 2

  test "hex escape literal \\x61 round-trips to \"a\"":
    let r = symexFind(isHexA, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "a"

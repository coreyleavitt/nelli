# ADR-0017 — A7: parallel `Rune`/codepoint path (Path B only)

- **Status:** ACCEPTED (2026-06-29)
- **Cluster:** A7 (Phase 16 — language fragments part 2) — the final Phase-16 cluster
- **Constraint:** **Path B only.** ADR-0006 (byte-faithful `string`, free chars
  pinned ≤ 0xFF) is **Corey-locked and stays untouched.** Path A (lifting the
  ≤0xFF pin so Z3 picks full codepoints) is FORBIDDEN — it would break all 14
  S-cluster tests. A7 adds a *parallel* codepoint path; it does not modify the
  `string` model.
- **Feasibility:** 7 both-backend Z3 probes (rc recorded; the tractable encodings
  are all rc=0, no 137). Evidence summarized below.

## Context

Nim's `std/unicode` exposes `Rune` (= `distinct int32`, a Unicode codepoint) and
`runes(s)`/`runeLen`/`runeAt` (UTF-8 views over a `string`). The engine models a
`string` byte-faithfully as `Z3Seq[Z3Char]` (each free char ≤ 0xFF, ADR-0006), so
"string position == Nim byte index." Runes are codepoints (0..0x10FFFF), a
*different* unit. The design question: how much of the rune surface can be modeled
hang-free and byte/codepoint-exact **without** touching the byte model.

Two boundaries the probes pinned down, both load-bearing:
1. **`fromCode(codepoint)` is NOT a byte encoder.** It builds a *single Unicode
   char* string, not the multi-byte UTF-8 form (probe P3c: a 3-byte `"\xE2\x82\xAC"`
   lstring ≠ `fromCode(0x20AC)`). So `$r` must be built from *byte values*, not the
   codepoint.
2. **Z3's char sort is BV18** (`UnicodeCharWidth = 18`), max codepoint 0x3FFFF — so
   `fromCode(codepoint)` is unsound for high-plane runes (P6d). The byte-level
   `$r` encoding sidesteps this entirely: it only ever calls `fromCode(byteVal)`
   with `byteVal ∈ [0,0xFF] ⊂ BV18`, and the probe recovered r=0x40000 from its
   bytes (P7c). Byte-level is the *sound* path; codepoint-level `fromCode` is not.

## Decision

Add a parallel codepoint path with three modeled sub-parts and explicit degrades.
A `Rune` value is modeled as **`svInt` (Z3Int) pinned to [0, 0x10FFFF]** — NOT a
BV32 — so `ord`, comparisons, and the `$r` byte arithmetic stay in linear integer
arithmetic with no `bv2int` cross-theory mixing.

### MODEL (TRACTABLE-HANG-FREE)

| Op | Encoding | Probe |
|---|---|---|
| free `Rune` SUT param | `svInt` pinned `0 ≤ r ≤ 0x10FFFF` at allocation (mirrors the ADR-0006 ≤0xFF char pin at `runtime.nim:1533`) | P1a–d sat/unsat correct |
| `ord(r)` / `int(r)` | identity on the `svInt` term | trivial |
| `r == Rune(lit)`, `!=`, `<`,`<=`,`>`,`>=` | Z3Int (in)equality / comparison | P1a–c |
| `Rune(intExpr)` | coerce the int term + range-pin [0,0x10FFFF] | P1 |
| `$r` (symbolic rune → UTF-8 `string`) | `runeToUtf8Sym`: a 4-branch ITE over codepoint range; each branch `concat`s `fromCode(byteVal)` for byteVals derived by linear div/mod. Output chars all ≤ 0xFF ⇒ **byte-faithful `svString`, ADR-0006-compatible** | P5a–d, P7a–c (incl. r>0x3FFFF) |
| `runes(lit)`, `runeLen(lit)`, `lit.runeAt(i)` over a **concrete/literal** string | decode in Nim at parse time → emit concrete Z3Int codepoint literals / numeral | P4a (pure Nim) |

### DEGRADE (sound `sxUnknown`, classified — no new error kind)

| Op | Kind | Reason |
|---|---|---|
| `runes(s)` / `runeLen(s)` over a **symbolic** string | `seZ3StringIncomplete` | symbolic UTF-8 decode = variable-length (1–4 byte) grouping over an unknown byte stream → no quantifier-free Z3 encoding; quantified form hangs (G4) |
| `toLower`/`toUpper`/`isAlpha`/`isUpper`/… on `Rune` (full Unicode) | `seUnsupportedStringOp` | full-Unicode tables = hundreds–thousands of ranges; ITE depth excessive, and context-dependent folds (Turkish ı/I) need a locale oracle Z3 lacks (genuine-cannot, per RFC). ASCII fold stays A9's `toLowerAscii`. |

`runeToUtf8Sym` is an **engine-internal** helper (lives in `runtime_strings.nim`),
NOT a nim-z3 addition: `fromCode`/`toCode`/`concat`/`len`/`ite`/`mkInt` are all
already wrapped. **No FFI change for A7** (`Z3_mk_u32string` confirmed absent and
not needed).

## Soundness (Invariant 3)

Every modeled op is exact vs Nim: `ord`/compare are identity; `$r` reproduces Nim's
UTF-8 byte encoding (the standard 1/2/3/4-byte rule, probe-verified incl. the émoji
plane); `runes(lit)` is decoded by Nim itself. Every non-modeled op returns a
classified `sxUnknown`, never a wrong verdict and never a hang. The byte model is
untouched, so all 14 S-cluster tests are unaffected (Path B = additive).

## Implementation — sliced (each behaviour-changing slice bumps the walker + 4 pins)

The walker bump fires at **S1** (first verdict change: a `Rune` SUT that was
`sxUnknown` becomes decidable): **v34 → v35**, update + run all 4 pins
(`CR2_cachekey`, `R16_1_arithcheck_foundation`, `a3_closure_iterators`, `a8_radix`).
Later slices that add new modeled ops bump again (v36, v37) per
[[symex-version-bump-cr2]].

- **A7-S1 (foundation):** `Rune` type classification → `svInt` pinned [0,0x10FFFF];
  `ord(r)`/`int(r)`; `Rune(intExpr)`; comparisons + equality vs `Rune(lit)`.
  New `tests/tsymex_a7_rune.nim` (free-param sat, comparison, ord-arith, the
  high-bound unsat soundness direction). **v34→v35 + 4 pins.**
- **A7-S2 (`$r`):** `runeToUtf8Sym` in `runtime_strings.nim`; route `$r` where the
  operand is a `Rune` to it (distinct from the existing int→dec `iekIntToStr`).
  Tests: `$r == "\xC3\xA9"` (é, 2-byte), `"\xE2\x82\xAC"` (€, 3-byte),
  `"\xF0\x9F\x98\x80"` (😀, 4-byte/high-plane) — each sat with the right witness.
- **A7-S3 (concrete `runes`):** parse-time decode of `runes(lit)`/`runeLen(lit)`/
  `lit.runeAt(i)` → concrete codepoint literals; plus the symbolic-`runes`
  DEGRADE pin (`seZ3StringIncomplete`).

Perturbation: **NEW TESTS ONLY** — `grep -rln 'Rune|\.runes|runeLen|toRunes'
tests/tsymex_*.nim` is empty; S9 (`std/unicode` `toLower`/`toUpper`) keeps its
DEGRADE classification unchanged. Zero S-cluster edits.

## Alternatives rejected

- **Path A (lift the ≤0xFF pin)** — reopens Corey-locked ADR-0006, breaks 14
  S-cluster files. Forbidden without an explicit lock-unlock + sign-off.
- **`Rune` as BV32** — works (P2) but forces `bv2int` for `ord` and the `$r`
  arithmetic (cross-theory). `svInt` is cleaner and equally decidable. Rejected.
- **`$r` via `fromCode(codepoint)`** — unsound: single-codepoint string ≠ UTF-8
  bytes (P3c) and breaks above BV18 (P6d). The byte-level ITE is mandatory.
- **Model `runes(symbolic_s)`** — symbolic UTF-8 decode hangs/needs quantifiers.
  Degrade is the sound outcome (cf. A6's filter decision).

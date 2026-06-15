# ADR-0006 — String codepoint-indexing model for the symex walker

| | |
|---|---|
| **Status** | Accepted |
| **Date** | 2026-06-15 |
| **Deciders** | proptest maintainers |
| **Supersedes** | — |
| **Superseded by** | — |
| **Related** | [SYMEX_PLAN.md § Cluster S](../SYMEX_PLAN.md), [RFC-phase15-language-fragments.md § Cluster S](RFC-phase15-language-fragments.md), [RFC-phase15-reconciliation.md § F — Cluster S](RFC-phase15-reconciliation.md), [nim-z3 v2.0.0 `z3/strings.nim` / `z3/sequence.nim`](https://github.com/coreyleavitt/nim-z3) |

## Context

Cluster S promotes the symex engine's `string` support from the Phase 5
baseline — where `string` is a Z3 free variable that participates only in
equality and table-key indexing — to the full Z3 String + Regex theory
surface (`len`, `at`, `substr`, `find`/`indexOf`, `contains`, `startsWith`/
`endsWith`, `replace`, `split`, `join`, regex membership, int interop). The
moment the walker exposes a *length* or an *index* operation it must commit
to an indexing model, and Nim's native model and Z3's native model disagree.

Nim's `string` is a **mutable, UTF-8-encoded byte sequence**. `s.len` is a
byte count; `s[i]` is the byte at offset `i` (a `char`); `for c in s` iterates
bytes; `s.high == s.len - 1` is a byte index. A multi-byte codepoint such as
`"é"` (U+00E9) occupies **two** bytes (`0xC3 0xA9`), so `"é".len == 2` and
`"é"[0]` is the lead byte `'\xC3'`, not the character.

Z3's SMT-LIB `String` sort is `(Seq Char)` — a finite sequence of characters,
indexed by position. `(str.len s)` counts **characters**, `(seq.at s i)`
returns the single-character subsequence at character position `i`, and
`(seq.extract s off len)` slices by character offset. There is no notion of
multi-byte encoding inside the theory: every character is one position.

The two models therefore diverge on `s.len`, `s[i]`, iteration, slicing, and
the length of any multi-byte literal. The walker must pick one model and apply
it uniformly; the wrong choice either admits witnesses that fail at Nim runtime
(unsoundness) or rejects witnesses that would succeed (false UNSAT).

### Reality note — how `mkString` actually encodes literals

The RFC's S0-ADR draft asserted that `mkString(nimStr)` produces a Z3 string
whose Z3-side `len` equals `nimStr.runeLen` (the Unicode scalar count), so that
`mkString("é").len == 1`. **This is not what the real nim-z3 `mkString` does**
and the ADR is written to the true semantics (verified against
`_deps/z3/src/z3/strings.nim` at S0-ADR; see reconciliation § F — Cluster S):

- `mkString(s)` calls `Z3_mk_lstring(ctx.raw, cuint(s.len), s.cstring)`
  (`strings.nim:54-58`). `Z3_mk_lstring` is a **length-prefixed, byte-faithful**
  constructor — it maps each input *byte* to one Z3 character. Its documented
  purpose in the wrapper is "carries the bytes of `s` … so embedded NULs are
  preserved" (`strings.nim:17`).
- Consequently the real invariant is `mkString(s).len == s.len` — the Z3-side
  character count equals the Nim **byte** count, for every `s`. For ASCII this
  coincides with the codepoint count and everything is intuitive. For a
  multi-byte literal it does **not**: `mkString("é")` builds a length-**2** Z3
  string whose character *values* are the raw UTF-8 bytes `[195, 169]`, not a
  length-1 string holding the scalar U+00E9 (233).
- There is no `Z3_mk_u32string` (scalar-value literal constructor) in this
  nim-z3 FFI, so the byte-faithful path is the only literal path. True Unicode
  scalar values are reachable only through `toCode`/`fromCode`
  (`Z3_mk_string_to_code` / `Z3_mk_string_from_code`, `strings.nim:107/114`),
  which the `bytes(s)` lift (cycle S7a) uses.

So the engine's "codepoint model" is *Z3's positional character model*, and for
literals built via `mkString` each position holds a UTF-8 byte value. Cluster S
adopts Z3's positional/character indexing as the canonical symbolic model and
documents that the *length* of `mkString`-built literals tracks Nim's byte
length (a property authors can rely on), while warning that the character
*values* of non-ASCII literals are byte values, not scalar values.

## Options considered

### Indexing model

#### Option A — Z3 positional character model (codepoint-indexed), adopted

Model `string` directly as Z3's `String` sort and use the native theory ops
(`len`, `at`, `substr`, `indexOf`, `contains`, `prefixof`/`suffixof`,
`to_re`/`in_re`, `str.to_int`/`int.to_str`) for every string operation. All
offsets are Z3 character positions. Free `string` variables are
`mkStringVar`; literals are `mkString`; witnesses are extracted with `evalStr`.

**Pros:**
- Z3-native: no encoding layer, no auxiliary constraints, queries stay in the
  String/Seq theory where Z3's solver is strongest.
- The entire op surface (regex membership, `str.to_int`, lexicographic compare,
  `substr`, `indexOf`) is defined on this sort and only this sort.
- Phase 5 already shipped `itString`/`svString` on exactly this representation
  (`mkStringVar`/`mkString`/`evalStr`), so Cluster S is an *extension*, not a
  migration — every existing string SUT keeps working.

**Cons:**
- Diverges from Nim byte semantics for `s.len` / `s[i]` / iteration on
  multi-byte input. Mitigated by (a) the `bytes(s)` escape hatch for authors who
  need real byte access, (b) classifying the irreducibly byte-shaped Nim ops
  (`s.high`, `for c in s`, byte-index mutation) as structured errors rather than
  silently mismodeling them, and (c) surfacing the distinction in witness output
  and `determinism.md`.

**Accepted.**

#### Option B — BV8-sequence model (byte-faithful `Z3Seq[Z3BV8]`)

Represent `string` as a sequence of 8-bit bitvectors mirroring Nim's UTF-8
bytes exactly, so `s.len`, `s[i]`, and iteration match Nim byte-for-byte.

**Pros:** Exact Nim byte semantics; `s[i]` and `for c in s` would model
faithfully.

**Cons:** Z3's String-theory operations — regex membership (`in_re`),
`str.to_int` / `int.to_str`, lexicographic `str.<`, `substr` as `seq.extract`
on the String sort — are defined on the `String` sort, **not** on an arbitrary
`Seq[BV8]`. A BV8-sequence model forfeits the entire high-value op surface and
forces hand-rolled re-encodings of UTF-8 decode logic (multi-byte boundary
arithmetic) into every operation. It also discards the working Phase 5 String
foundation. Byte-indexed witnesses would additionally require Z3 to reason about
multi-byte codepoint-boundary arithmetic to satisfy any constraint touching both
`len` and content — exactly the class of off-by-one boundary bugs the engine
would then fail to detect.

**Rejected.**

#### Option C — Hybrid (detect byte- vs codepoint-context at parse time)

Choose byte or codepoint semantics per `string` variable based on which kind of
operation is first observed against it.

**Cons:** Produces two incompatible constraint sets for the *same* variable
depending on observation order; a SUT that mixes `s == "é"` with `s.len` would
constrain `s` under contradictory encodings. Unsound and complex.

**Rejected.**

#### Option D — Warn-and-continue with byte semantics

Model everything with byte semantics and emit a warning when a multi-byte
literal is observed, continuing anyway.

**Cons:** Silent model divergence violates Invariant 3 (no silent fallbacks);
"warn and proceed" still admits or rejects witnesses under a model the author
did not choose.

**Rejected.**

## Decision

1. **Codepoint-indexed (Z3 positional character) model, adopted.** `string`
   maps to Z3's `String` sort; `svString{str: Z3String}` is unchanged from
   Phase 5. Every string operation lowers to its Z3 String/Seq theory
   equivalent (`len`, `at`, `substr`, `indexOf`, `contains`, `startsWith`,
   `endsWith`, `replace`, `mkRegex`/`matches`, `toInt`/`toStr`). All offsets are
   Z3 character positions; no byte-boundary arithmetic is introduced.

2. **`mkString(s).len == s.len` (Nim byte count) is the literal-length
   invariant.** Because `mkString` lowers to `Z3_mk_lstring` (byte-faithful),
   the Z3-side length of any literal equals its Nim byte length. For ASCII this
   equals the codepoint count; for multi-byte literals the Z3 string holds one
   character per UTF-8 byte (byte values, not scalar values). A constraint
   `len(mkString("é")) == 2` is **SAT**; `len(mkString("é")) == 1` is **UNSAT**.
   Property-test authors writing literal `len` constraints must use the Nim byte
   length. (This corrects the RFC draft, which specified `== 1`; see the Reality
   note and the reconciliation drift table.)

3. **`bytes(s)` is the explicit byte-level escape hatch (cycle S7a).** Authors
   who need genuine raw-UTF-8 byte access opt in via the `bytes(s)` DSL lift,
   which lowers to a `seq[byte]` SymVal built from `toCode`/`fromCode` with
   UTF-8 BMP constraints. There is no implicit byte view; byte semantics are
   always explicit.

4. **Irreducibly byte-shaped Nim ops are classified, never silently modeled.**
   - `s.high` → `seByteIndexUnsupported` (Nim's `s.len - 1` is a byte index).
   - `for c in s` → `seByteIterUnsupported` (Nim's byte iterator yields `char`).
   - `s[i] = c` and `s.add(c)` → `seUnsupportedStringOp` (byte-index mutation /
     byte append; may split a multi-byte codepoint). (Cycle S11.)
   - `toLower` / `toUpper` → `seUnsupportedStringOp` (no sound Z3 native;
     regex-range approximation is a Phase 16 backlog item). (Cycle S9.)

   Each emits a structured `SymexErrorInfo{kind: …, severity: sevError}` and
   yields `sxUnknown` (Invariant 3), never a wrong witness. (`seByteIndexUnsupported`,
   `seByteIterUnsupported`, `seUnsupportedStringOp` already exist in
   `SymexErrorKind`, `types.nim:441-459`.)

5. **The codepoint/byte distinction is surfaced to authors.** Witness output for
   `string` params reports the Z3-positional value (and, when `bytes(s)` is used,
   the byte view); `determinism.md` documents that `s.len` in symex equals the
   Z3 character count (Nim byte count for `mkString` literals) and that this
   affects multi-byte Unicode literals. Authors are never silently surprised.

6. **No quantifiers introduced by the indexing model.** The String/Seq theory
   ops used here are quantifier-free; the model keeps string queries in the
   decidable QF fragment Z3's string solver targets (with the documented
   general-incompleteness caveat for free-variable + regex + arithmetic mixes).

## Z3 String/Seq-theory API mapping

| Nim operation | Z3 / SMT-LIB | nim-z3 wrapper (`z3/strings`, `z3/sequence`) |
|---|---|---|
| `"lit"` literal | `Z3_mk_lstring` (byte-faithful) | `mkString(s)` |
| free `s: string` | `Z3_mk_string_symbol` const | `mkStringVar(name)` |
| witness extract | `Z3_get_lstring` | `evalStr(m, sv.str)` |
| `s.len` | `(str.len s)` | `len(sv.str): Z3Int` |
| `s[i]` (codepoint) | `(seq.at s i)` | `at(sv.str, i): Z3String` |
| `s[a..b]` | `(seq.extract s a (b-a+1))` | `substr(sv.str, a, len)` |
| `s.find(sub)` | `(seq.indexof s sub 0)`; −1 if absent | `indexOf(sv.str, sub)` |
| `s.contains(sub)` | `(seq.contains s sub)` | `contains(sv.str, sub)` |
| `s.startsWith(p)` | `(seq.prefixof p s)` | `startsWith(sv.str, p)` |
| `s.endsWith(q)` | `(seq.suffixof q s)` | `endsWith(sv.str, q)` |
| `a & b` | `(seq.++ a b)` | `` `&`(a, b) `` / `concat` |
| `s.replace(o, n)` | `(seq.replace s o n)` first-occurrence | `replace(s, o, n)` |
| `a < b` | `(str.< a b)` | `` `<`(a, b) `` (no `str.gt`/`ge`; `>` flips args) |
| `$i` / `parseInt` | `(int.to.str i)` / `(str.to.int s)` | `Z3Int.toStr` / `Z3String.toInt` |
| codepoint of 1-char | `(str.to_code s)` | `toCode(s): Z3Int` |
| char from codepoint | `(str.from_code c)` | `fromCode(c): Z3String` |
| regex membership | `(seq.in.re s r)` | `matches(s, r): Z3Bool` |
| literal → regex | `(seq.to.re s)` | `mkRegex(s)` |

## Consequences

### Intended

- The full Z3 String/Regex op surface (S3–S10) is available with no encoding
  layer; every op is a single theory-level call.
- Phase 5 string SUTs (equality + table-key) keep passing unchanged — Cluster S
  extends, not migrates, the foundation (S7b regression smoke confirms this).
- ASCII string reasoning is fully intuitive: `len`/`[i]`/slicing all match Nim.
- Byte-level needs are met explicitly and soundly via `bytes(s)` (S7a).

### Accepted as cost

- For multi-byte literals, `s.len` in symex equals the Nim **byte** count, and
  the per-position character *values* are UTF-8 byte values rather than Unicode
  scalar values. A SUT that asserts a codepoint-count `len` for a multi-byte
  literal will be modeled against byte length. This is documented at every use
  site and in `determinism.md`; it is the natural consequence of `Z3_mk_lstring`
  being the only literal constructor in this nim-z3 build.
- `s.high`, `for c in s`, `s[i] = c`, `s.add(c)`, `toLower`/`toUpper` are not
  modeled; they produce classified errors and `sxUnknown` rather than witnesses.

### Deferred

1. **Codepoint-aware multi-byte literal lifting** (a `runeLen`-correct,
   scalar-value literal path) — would require a `Z3_mk_u32string`-style
   constructor absent from this FFI, or a manual scalar-decode at lift time.
   Phase 16 backlog.
2. **`toLower` / `toUpper`** via regex-range case-folding approximation. Phase 16.
3. **Byte-index mutation / byte iterator** (`s[i]=c`, `for c in s`, `s.add`) —
   sound modeling requires the `bytes(s)` round-trip; deferred to Phase 16.
4. **`cstring` interop** — FFI surface, excluded from Phase 15; parse-time
   `error()` pointing at the Phase 16 backlog.

## Validation

ADR-0006 is validated by Cluster S cycle tests (TDD):

- **S2 DoD (corrected):** `s == "hello"` is SAT and round-trips via `evalStr`;
  `s == ""` is SAT (empty witness); the multi-byte literal test asserts
  `s == "é"` is SAT **with `s.len == 2`** (Z3 byte-faithful length), confirming
  the real `mkString`/`Z3_mk_lstring` semantics — *not* `== 1` as the RFC draft
  stated.
- **S3 DoD:** `s.len == 5` is SAT; `s[1..3] == "ell"` for `s == "abcde"` is SAT;
  `s.high` → `sxUnknown` with `errors[0].kind == seByteIndexUnsupported`;
  `for c in s` → `sxUnknown` with `seByteIterUnsupported`.
- **S7a DoD:** `bytes(s)` lowers to a `seq[byte]` SymVal via `toCode`/`fromCode`.
- **S9 / S11 DoD:** `toLower`/`toUpper`, `s[i]=c`, `s.add(c)` →
  `seUnsupportedStringOp` (classified, `severity: sevError`).
- **S7b / S11 DoD:** `determinism.md` documents the codepoint/byte split.

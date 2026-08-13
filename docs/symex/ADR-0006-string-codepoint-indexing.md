# ADR-0006 — Byte-faithful string model for the symex walker

> **Filename note.** This ADR's filename (`ADR-0006-string-codepoint-indexing.md`)
> is historical: an earlier draft proposed a codepoint-indexed model. The decision
> recorded here is the **byte-faithful** model (Corey-locked). The filename is kept
> to avoid cross-reference churn; the title and content are authoritative.

| | |
|---|---|
| **Status** | Accepted |
| **Date** | 2026-06-15 |
| **Deciders** | nelli maintainers (project owner locked the byte-faithful decision) |
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
to an indexing model, and the apparent question is whether Nim's native model
(bytes) and Z3's native model (positional characters) agree.

Nim's `string` is a **UTF-8-encoded byte sequence**. `s.len` is a byte count;
`s[i]` is the byte at offset `i` (a `char`); `for c in s` iterates bytes;
`s.high == s.len - 1` is a byte index. A multi-byte codepoint such as `"é"`
(U+00E9) occupies **two** bytes (`0xC3 0xA9`), so `"é".len == 2` and `"é"[0]`
is the lead byte `'\xC3'`, not the character.

Z3's SMT-LIB `String` sort is `(Seq Char)` — a finite sequence of characters,
indexed by position. `(str.len s)` counts **characters**, `(seq.at s i)`
returns the single-character subsequence at character position `i`, and
`(seq.extract s off len)` slices by character offset. A Z3 character may range
over the full Unicode space (0..0x2FFFF), so in general one Z3 character is not
one byte.

The naive reading is that these two models diverge on `s.len`, `s[i]`,
iteration, slicing, and the length of any multi-byte literal. **They do not have
to.** The key fact (below) is that `mkString` is byte-faithful and that a free
`string` variable can be *constrained* to the byte range; once that constraint
is asserted, one Z3 position is exactly one Nim byte and the two models
**coincide**. This ADR records the decision to take that path.

### Reality note — how `mkString` actually encodes literals

The RFC's S0-ADR draft asserted that `mkString(nimStr)` produces a Z3 string
whose Z3-side `len` equals `nimStr.runeLen` (the Unicode scalar count), so that
`mkString("é").len == 1`. **This is not what the real nim-z3 `mkString` does**
and this ADR is written to the true semantics (verified against
`_deps/z3/src/z3/strings.nim` at S0-ADR; see reconciliation § F — Cluster S):

- `mkString(s)` calls `Z3_mk_lstring(ctx.raw, cuint(s.len), s.cstring)`
  (`strings.nim:54-58`). `Z3_mk_lstring` is a **length-prefixed, byte-faithful**
  constructor — it maps each input *byte* to one Z3 character. Its documented
  purpose in the wrapper is "carries the bytes of `s` … so embedded NULs are
  preserved" (`strings.nim:17`).
- Consequently the real invariant is `mkString(s).len == s.len` — the Z3-side
  character count equals the Nim **byte** count, for every `s`. For a multi-byte
  literal: `mkString("é")` builds a length-**2** Z3 string whose character
  *values* are the raw UTF-8 bytes `[0xC3, 0xA9]` (`[195, 169]`), **not** a
  length-1 string holding the scalar U+00E9 (233).
- There is no `Z3_mk_u32string` (scalar-value literal constructor) in this
  nim-z3 FFI, so the byte-faithful path is the only literal path. True Unicode
  scalar values are reachable only through `toCode`/`fromCode`
  (`Z3_mk_string_to_code` / `Z3_mk_string_from_code`, `strings.nim:107/114`).

So a literal built via `mkString` is already a per-byte sequence: each Z3
position holds one UTF-8 byte value. The remaining question is what to do about
**free** `string` variables (`mkStringVar`), where Z3 is otherwise free to
choose full-Unicode characters that occupy a single Z3 position but multiple
Nim bytes — which would break witness round-trip. The decision below closes that
gap with a range constraint.

## Decision

**Byte-faithful string model (Corey-locked).** Cluster S models `string` as a
Z3 `String` whose characters are constrained to the **Latin-1 byte range
(≤ 0xFF)**, so that **one Z3 position is exactly one Nim byte**. Under this
constraint Z3's positional character model and Nim's byte model **coincide**:
there is no divergence to manage. Concretely:

1. **The ≤ 0xFF character constraint is the soundness mechanism.** At allocation
   time, every free `string` variable (`mkStringVar`) asserts that **every
   character is ≤ 255**. This is the core mechanism of the model: without it Z3
   would be free to pick full-Unicode codepoints (0..0x2FFFF) that are a single
   Z3 position but multi-byte in Nim, so a witness extracted via `evalStr` would
   not round-trip to a Nim string of the same length/content. With the
   constraint, every Z3 position maps to exactly one Nim byte, and **Z3 position
   == Nim byte index**. (Literals via `mkString` are already in-range — each
   character is a raw byte 0..255 — so the constraint is consistent with every
   literal.) *(This is the design intent the implementing cycles S1/S3 enforce in
   code; this ADR records the decision.)*

2. **`mkString(s).len == s.len` (Nim byte count) is the literal-length
   invariant.** Because `mkString` lowers to `Z3_mk_lstring` (byte-faithful), the
   Z3-side length of any literal equals its Nim byte length. A constraint
   `len(mkString("é")) == 2` is **SAT**; `len(mkString("é")) == 1` is **UNSAT**.
   Property-test authors writing literal `len` constraints use the Nim byte
   length. (This corrects the RFC draft, which specified `== 1`.)

3. **Positional string operations are byte-faithfully supported.** With chars
   ≤ 0xFF, the Z3 positional model **is** Nim's byte model, so all of the
   following lower directly to their Z3 String/Seq theory equivalent and match
   Nim byte-for-byte:
   - `s.len` → `(str.len s)` — Z3 length == Nim byte length.
   - `s[i]` (read) → `(seq.at s i)` — Z3 position == Nim byte index.
   - `s[a..b]` → `(seq.extract s a (b-a+1))` — byte-offset slice.
   - `s.high` → `len(s) - 1` — byte index of the last byte.
   - `for c in s` → positional iteration; each yielded character == the Nim byte.

   The remaining higher-level ops (`find`/`indexOf`, `contains`, `startsWith`,
   `endsWith`, `replace`, `&`, regex membership, `toInt`/`toStr`) likewise lower
   directly and are byte-faithful.

4. **Genuinely unsupported ops are classified, never silently modeled.** These
   stay out of scope and emit a structured `SymexErrorInfo{… severity: sevError}`
   yielding `sxUnknown` (Invariant 3), never a wrong witness — and the reason is
   **immutability / a missing Z3 op, NOT a byte/codepoint mismatch**:
   - `s[i] = c` and `s.add(c)` → `seUnsupportedStringOp`. Z3 strings are
     **immutable**: true in-place mutation has no encoding in the theory. (Cycle
     S11.)
   - `toLower` / `toUpper` (std/unicode) → `seUnsupportedStringOp`. **No Z3
     native full-Unicode case folding** (Turkish ı/I, Greek σ/ς etc. require a
     locale oracle Z3 lacks). Genuine-cannot; not a Phase 16 backlog item.
     (Cycle S9.)
   - `toLowerAscii` / `toUpperAscii` (std/strutils) → **MODELED** (Phase 16 A9,
     ADR-0015). Lowered via `seqMapBody` BV18-ITE quantifier-free fold.
     `iekStrToLower` / `iekStrToUpper` in StrOpKinds. Result equals Nim's
     byte-for-byte (Invariant 3 verified by probe). (Walker v34.)

5. **`bytes(s)` (cycle S7a) is a thin convenience view, not a subsystem.**
   Because the base model is already a byte sequence (each character is a value
   0..255), `bytes(s)` is essentially the **identity view**: it maps each Z3
   character position to its byte value as a BV8/int. It is no longer a separate
   UTF-8-decoding subsystem; it is a presentation lift over the same per-position
   bytes the model already holds.

6. **Coverage limitation, stated honestly.** Witnesses are limited to the Latin-1
   byte range **per character**: the engine cannot synthesize a free-variable
   witness in which a single Nim character is a multi-byte UTF-8 sequence. This is
   a documented coverage boundary, consistent with Invariant 3 — any operation
   that would require more emits a classified error, never a silent UNSAT. Note
   that this does **not** prevent a SUT from using a multi-byte string *literal*:
   a literal like `"é"` lowers via `mkString` to its raw bytes `[0xC3, 0xA9]`
   (length 2), and a free `string` variable can match those exact byte values
   (each ≤ 0xFF) — so `s == "é"` is SAT with `s.len == 2`. What the engine cannot
   do is *invent* a multi-byte sequence and present it as a single Nim rune.

7. **No quantifiers introduced by the indexing model.** The String/Seq theory
   ops used here are quantifier-free; the per-character ≤ 0xFF range bound is a
   quantifier-free constraint over the sequence (asserted via the Seq/String
   theory at allocation). The model keeps string queries in the decidable QF
   fragment Z3's string solver targets (with the documented general-incompleteness
   caveat for free-variable + regex + arithmetic mixes).

## Options considered

### Option A — Codepoint-indexed (Z3 positional, characters unconstrained) — REJECTED

Model `string` directly as Z3's `String` sort with characters ranging over the
full Unicode space, and treat the Z3 positional/character model as the canonical
"codepoint" model (offsets are Z3 character positions over arbitrary codepoints).

**Rejected**, for two decisive reasons:

1. **It is not what the FFI gives.** `mkString` lowers to `Z3_mk_lstring`, which
   is byte-faithful — each literal character is a raw UTF-8 byte, not a Unicode
   scalar. There is no scalar-value literal constructor (`Z3_mk_u32string`) in
   this FFI. So "codepoint-indexing" does not even describe the literal path the
   engine actually has; the literal model is already per-byte.

2. **It breaks free-variable witness round-trip.** If free `string` characters
   are left unconstrained, Z3 may choose full-Unicode codepoints (0..0x2FFFF)
   that are a single Z3 position but multi-byte in Nim. A witness extracted via
   `evalStr` would then have a different `len`/content when materialized as a Nim
   string, silently mismodeling `s.len`, `s[i]`, and iteration on the very
   witnesses the engine produces — an unsoundness, not a documentation caveat.

The byte-faithful model (the ≤ 0xFF constraint, adopted in the Decision above)
is the corrected form of this option: it keeps Z3's positional `String` sort and
its full high-value op surface, but pins each character to one byte so the
positional model and Nim's byte model coincide and witnesses round-trip.

### Option B — BV8-sequence model (byte-faithful `Z3Seq[Z3BV8]`) — REJECTED

Represent `string` as a sequence of 8-bit bitvectors (`Seq[BV8]`) instead of the
Z3 `String` sort.

**Pros:** Exact Nim byte semantics by construction.

**Cons / rejected:** Z3's String-theory operations — regex membership (`in_re`),
`str.to_int` / `int.to_str`, lexicographic `str.<`, `substr` as `seq.extract` on
the String sort — are defined on the `String` sort, **not** on an arbitrary
`Seq[BV8]`. A BV8-sequence model forfeits the entire high-value op surface and
forces hand-rolled re-encodings into every operation, and it discards the working
Phase 5 String foundation. The byte-faithful **String** model (Decision) obtains
the same exact byte semantics via the ≤ 0xFF constraint **without** leaving the
String sort, so it strictly dominates this option.

### Option C — Hybrid (detect byte- vs codepoint-context at parse time) — REJECTED

Choose byte or codepoint semantics per `string` variable based on which kind of
operation is first observed against it.

**Cons:** Produces two incompatible constraint sets for the *same* variable
depending on observation order; a SUT that mixes `s == "é"` with `s.len` would
constrain `s` under contradictory encodings. Unsound and complex. (Moot under the
byte-faithful decision: there is one model, always.)

### Option D — Warn-and-continue with byte semantics — REJECTED

Model everything with byte semantics but emit a warning when a multi-byte literal
is observed, continuing anyway.

**Cons:** Silent model divergence violates Invariant 3 (no silent fallbacks).
(Also moot: under the byte-faithful decision there is no divergence to warn
about — literals and free vars are both per-byte and coincide with Nim.)

## Z3 String/Seq-theory API mapping

| Nim operation | Z3 / SMT-LIB | nim-z3 wrapper (`z3/strings`, `z3/sequence`) | byte-faithful? |
|---|---|---|---|
| `"lit"` literal | `Z3_mk_lstring` (byte-faithful) | `mkString(s)` | ✓ each char is a raw byte |
| free `s: string` | `Z3_mk_string_symbol` const + ∀char ≤ 0xFF | `mkStringVar(name)` + range assert | ✓ (constraint at alloc) |
| witness extract | `Z3_get_lstring` | `evalStr(m, sv.str)` | ✓ round-trips byte-for-byte |
| `s.len` | `(str.len s)` | `len(sv.str): Z3Int` | ✓ == Nim byte len |
| `s[i]` (read) | `(seq.at s i)` | `at(sv.str, i): Z3String` | ✓ == Nim byte index |
| `s.high` | `len(s) - 1` | `len(sv.str) - 1` | ✓ last byte index |
| `for c in s` | positional iteration | per-position `at` | ✓ == Nim byte iteration |
| `s[a..b]` | `(seq.extract s a (b-a+1))` | `substr(sv.str, a, len)` | ✓ byte-offset slice |
| `s.find(sub)` | `(seq.indexof s sub 0)`; −1 if absent | `indexOf(sv.str, sub)` | ✓ |
| `s.contains(sub)` | `(seq.contains s sub)` | `contains(sv.str, sub)` | ✓ |
| `s.startsWith(p)` | `(seq.prefixof p s)` | `startsWith(sv.str, p)` | ✓ |
| `s.endsWith(q)` | `(seq.suffixof q s)` | `endsWith(sv.str, q)` | ✓ |
| `a & b` | `(seq.++ a b)` | `` `&`(a, b) `` / `concat` | ✓ |
| `s.replace(o, n)` | `(seq.replace s o n)` first-occurrence | `replace(s, o, n)` | ✓ |
| `a < b` | `(str.< a b)` | `` `<`(a, b) `` (no `str.gt`/`ge`; `>` flips args) | ✓ |
| `$i` / `parseInt` | `(int.to.str i)` / `(str.to.int s)` | `Z3Int.toStr` / `Z3String.toInt` | ✓ |
| `bytes(s)[i]` | `(seq.at s i)` value as BV8/int | identity view over chars (S7a) | ✓ trivial |
| regex membership | `(seq.in.re s r)` | `matches(s, r): Z3Bool` | ✓ |
| literal → regex | `(seq.to.re s)` | `mkRegex(s)` | ✓ |
| `s[i] = c` | — (Z3 strings immutable) | **unsupported** → `seUnsupportedStringOp` | n/a |
| `s.add(c)` | — (Z3 strings immutable) | **unsupported** → `seUnsupportedStringOp` | n/a |
| `toLowerAscii`/`toUpperAscii` | `(seq.map (lambda ...) s)` BV18-ITE | `seqMapBody` BV18-ITE fold (A9, ADR-0015) | ✓ (v34) |
| `toLower`/`toUpper` (unicode) | — (no Z3 case folding) | **unsupported** → `seUnsupportedStringOp` | n/a |

## Consequences

### Intended

- The full Z3 String/Regex op surface (S3–S10) is available with no encoding
  layer; every op is a single theory-level call **and** is byte-faithful, so
  `len`/`[i]`/slicing/iteration all match Nim exactly (not just for ASCII).
- Free-variable witnesses round-trip byte-for-byte through `evalStr` because the
  ≤ 0xFF constraint pins one Z3 position to one Nim byte.
- Phase 5 string SUTs (equality + table-key) keep passing unchanged — Cluster S
  extends, not migrates, the foundation (S7b regression smoke confirms this).
- `bytes(s)` (S7a) collapses to a thin identity view; no separate UTF-8-decode
  subsystem is needed.

### Accepted as cost

- **Latin-1 per-character coverage boundary.** Free-variable witnesses cannot
  contain a multi-byte UTF-8 sequence presented as a single Nim character; each
  character is a byte 0..255. Multi-byte literals still work (they lower to their
  raw bytes and a free var can match those byte values). This is documented at
  every use site and in `determinism.md`. It is the natural consequence of
  `Z3_mk_lstring` being the only literal constructor plus the ≤ 0xFF soundness
  constraint.
- `s[i] = c`, `s.add(c)` (Z3-string **immutability**) and `toLower`/`toUpper`
  (std/unicode, **no Z3 full-Unicode case-folding op**) are not modeled; they
  produce classified errors and `sxUnknown` rather than witnesses. Note:
  `toLowerAscii`/`toUpperAscii` (std/strutils) ARE modeled as of Phase 16 A9.

### Deferred

1. **Multi-byte rune witnesses** — synthesizing a free-variable witness whose
   single Nim character spans multiple UTF-8 bytes. Would require either a
   scalar-value literal/var path (a `Z3_mk_u32string`-style constructor absent
   from this FFI) or a UTF-8 (de/re)encode layer over the byte sequence. Phase 16
   backlog.
2. **`toLower` / `toUpper`** (std/unicode) — full-Unicode fold has
   context-dependent equivalences (Turkish ı/I, Greek σ/ς) requiring a locale
   oracle Z3 lacks; genuine-cannot, stays unmodeled.
3. **String mutation** (`s[i]=c`, `s.add`) — Z3 strings are immutable; sound
   modeling would require a copy-on-write / functional-update encoding. Phase 16.
4. **`cstring` interop** — FFI surface, excluded from Phase 15; parse-time
   `error()` pointing at the Phase 16 backlog.

## Validation

ADR-0006 is validated by Cluster S cycle tests (TDD):

- **S2 DoD (corrected):** `s == "hello"` is SAT and round-trips via `evalStr`;
  `s == ""` is SAT (empty witness); the multi-byte literal test asserts
  `s == "é"` is SAT **with `s.len == 2`** (Z3 byte-faithful length), confirming
  the real `mkString`/`Z3_mk_lstring` semantics — *not* `== 1`.
- **S3 DoD (byte-faithful):** `s.len == 5` is SAT; `s[1..3] == "ell"` for
  `s == "abcde"` is SAT; `s[i]` read, `s.high`, and `for c in s` are all
  **supported** and match Nim byte semantics (free-var characters constrained
  ≤ 0xFF). `s[i] = c` → `sxUnknown` with `errors[0].kind ==
  seUnsupportedStringOp` (immutability).
- **S7a DoD:** `bytes(s)` is a trivial identity view — each Z3 character position
  read out as its byte value (no UTF-8 decode).
- **S9 DoD (perturbation for A9):** `toLower`/`toUpper` (unicode) →
  `seUnsupportedStringOp` (classified, `severity: sevError`). `toLowerAscii`/
  `toUpperAscii` (ASCII) → `sxSat` with a correct witness (Phase 16 A9, ADR-0015).
- **S11 DoD:** `s[i]=c`, `s.add(c)` → `seUnsupportedStringOp` (immutability).
- **S7b / S11 DoD:** `determinism.md` documents the Latin-1 coverage boundary
  (free-var witnesses are per-byte; multi-byte literals still match).

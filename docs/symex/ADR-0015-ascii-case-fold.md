# ADR-0015 — ASCII case-fold (`toLowerAscii` / `toUpperAscii`) via direct-lambda `seqMap`

- **Status:** ACCEPTED (2026-06-29)
- **Cluster:** A9 (Phase 16 — language fragments part 2)
- **Supersedes (scope-narrowing):** ADR-0006 §Consequences listing of `toLowerAscii`/`toUpperAscii` as unmodeled
- **Feasibility:** proven by a both-backend Z3 probe (rc=0, no 137; 5/5 goals incl. the UNSAT soundness direction)

## Context

`std/strutils.toLowerAscii` / `toUpperAscii` over a **symbolic** string currently
degrade to `seUnsupportedStringOp` → `sxUnknown` (Phase-15 S9 stub). Case-fold is a
pure per-character remap, the natural shape for a sequence `map`. nim-z3 exposes
`seqMap` (`funcdecl.nim`), but it builds `(seq.map (lambda ((x E)) (f x)) s)` with an
**uninterpreted** `Z3FuncDecl f` — defining the actual fold then requires a
`∀c. f(c)=…` axiom, which is **hang-prone** (G4 quantifier class). The byte-faithful
string model (ADR-0006) represents a string as `Z3Seq[Z3Char]` with each `Z3Char`
backed by an 18-bit BV (`UnicodeCharWidth = 18`), all free chars pinned ≤ 0xFF.

## Decision

Add a **direct-body** `seqMap` variant and lower ASCII case-fold to a
**quantifier-free** per-char BV18 ITE — no uninterpreted function, no quantifier.

**New nim-z3 wrapper** (`_deps/z3/src/z3/funcdecl.nim`, beside `seqMap`):

```nim
proc seqMapBody*[E, F](boundVar: E, body: F, s: Z3Seq[E]): Z3Seq[F] =
  ## (seq.map (lambda ((boundVar E)) body) s) — direct-body variant.
  ## body is a concrete Z3 expr over boundVar (no uninterpreted fn, no ∀): hang-free.
  let ctx = s.ctx
  var xApp = ctx.checkErr Z3_to_app(ctx.raw, boundVar.raw)
  let lambdaRaw = ctx.checkErr Z3_mk_lambda_const(ctx.raw, 1'u32,
    cast[ptr UncheckedArray[RawZ3App]](addr xApp), body.raw)
  wrap[Z3Seq[F]](ctx, ctx.checkErr Z3_mk_seq_map(ctx.raw, lambdaRaw, s.raw))
```

No new raw FFI bindings — `Z3_mk_lambda_const` / `Z3_mk_seq_map` are already declared
and used by the existing `seqMap`. This is purely a Nim wrapper that hands a prebuilt
lambda body instead of an uninterpreted-function application.

**Fold body** (per char element `x: Z3Char`, bridged via `x.toBitVec : Z3BitVec[18]`
and `mkChar(bv) : Z3Char`, both already in `chars.nim`):

- `toLowerAscii`: `ite( 65 ≤ x ≤ 90 , x+32 , x )`  (range `'A'..'Z'`)
- `toUpperAscii`: `ite( 97 ≤ x ≤ 122, x-32 , x )`  (range `'a'..'z'`)

Bytes ≥ 0x80 and non-letters fall to the ITE `else` branch unchanged → byte-faithful
passthrough is automatic. Length is preserved by `seq.map`.

## Scope

- **In:** `toLowerAscii` / `toUpperAscii` (`std/strutils`) — ASCII/Latin-1 letters.
- **Out (still `seUnsupportedStringOp` → sxUnknown):** `toLower` / `toUpper`
  (`std/unicode`) — full-Unicode fold has context-dependent equivalences (Turkish
  ı/I, Greek σ/ς) needing a locale oracle Z3 lacks (genuine-cannot, ADR-0006).

## Soundness (Invariant 3)

The fold result equals Nim's `toLowerAscii`/`toUpperAscii` byte-for-byte (the ITE is
the exact ASCII rule). The probe confirmed both directions hang-free on c+cpp:
`toLowerAscii(s)=="abc"` → sat (witness "Abc"); `toLowerAscii(s)=="ABC"` → **unsat**
(decided by BV arithmetic alone — the result provably cannot contain uppercase, no
string-solver search); non-ASCII bytes pass through (`"\xC3\xA9"` round-trips).

## Implementation

- New IR kinds `iekStrToLower` / `iekStrToUpper` (append to `IRExprKind` + `StrOpKinds`,
  mind ordinal stability).
- `dsl_parser.nim` (~1623): route `toLowerAscii`/`toUpperAscii` → the new kinds;
  keep `toLower`/`toUpper` → `iekStrUnsupported`.
- `runtime_strings.nim` `lowerStrArm`: new arms emitting the BV18-ITE `seqMapBody`
  fold; remove them from the unmodeled exclusion set.
- `symexWalkerVersion` 33→34 + all 3 pins to "34".
- Perturbation: `tests/tsymex_phase15_S9_caseconv.nim` — `toLowerAscii`/`toUpperAscii`
  tests flip `sxUnknown`→`sxSat` (+ witness `r.witness[0].toLowerAscii == "abc"`);
  `toLower`/`toUpper` tests unchanged. ADR-0006 §Consequences (lines ~126, ~243,
  ~268, ~279, ~300): split the `toLower/toUpper` entries so the ASCII ops move to
  *modeled (A9)* and the unicode ops stay unmodeled.

## Alternatives rejected

- **Uninterpreted-`f` `seqMap` + `∀c` fold axiom** — quantifier → hang (G4). Rejected;
  the direct-body lambda is the whole point.
- **Per-position unroll** (like A8 `iekRadixFmt`) — impossible at symbolic length
  (unknown digit/char count). `seq.map` handles symbolic length natively.

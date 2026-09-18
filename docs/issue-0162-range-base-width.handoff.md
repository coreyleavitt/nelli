# Issue #162 — a range subtype carries its base type, not just its bounds

Issue-scoped handoff (not an RFC; no `docs/rfc/NNNN` number). Newest entries
at the BOTTOM.

- **Branch:** `rfc-162-range-base-width`, stacked on
  `rfc-161-overflow-obligation` (named `rfc-*` deliberately — the three
  Windows legs trigger on `[main, 'rfc-*']`, and this is a walker semantics
  change that `symex-mingw` must verify).
- **Base:** `b1bea5c` (the tip of #161). The stack is real, not cosmetic:
  #162 retires the `mul32` trip-wire #161 slice 5 planted, and its
  `isOptimised` half runs through #161's live-obligation machinery.
- **Issue:** #162.

## The defect

`classifyType` returned `tInt(64, signed = true)` for **every**
`range[lo..hi]`, keeping the bounds and discarding the base type they are
written in.

```nim
proc mul32(a, b: range[0'i32..100_000'i32]) =
  let c = a * b            # typeof(c) is int32; 1e10 does not fit
  symexTarget("t")
```

`range[0'i32..100_000'i32]` is a subtype of **int32**. Nim performs its
arithmetic in int32 and checks overflow against int32's window, so
`mul32(100_000, 100_000)` raises `OverflowDefect` at runtime. The walker
checked that multiply against a 64-bit window, where 1e10 fits, and the
defect path vanished.

This sits **upstream of promotion**, which is why `isExact` — which never
promotes — was wrong too. #161 stamps the width it is given; #162 is about
the width it is given.

## Design decision

No fork was surfaced: the right answer is forced by Nim's semantics and was
verified by execution rather than argued. The base type is recovered from a
**bound literal's own node kind** (`nnkInt32Lit`, `nnkUInt16Lit`, …), which
semcheck stamps and which survives on both routes into the module —
`getTypeInst` for an inline formal, `getImpl` for a named alias. Reading the
kind rather than calling `getTypeInst` on the literal is what makes the alias
route safe: there the bound comes from the type *definition's* AST and need
not carry a type at all.

The one judgement call worth recording is **unsigned**, and it reuses #161
slice 3's argument with one fewer remedy available:

| | keeps the obligation how |
|---|---|
| signed, checked | live — `overflowCondInt`'s raise fork |
| signed, unchecked (`-d:danger`) | wrap scan bans promotion (#161 slice 3) |
| **unsigned** | **nothing to keep it live in — refuse promotion outright** |

Nim wraps unsigned arithmetic silently. An unbounded `Z3Int` cannot wrap and
there is no raise fork for unsigned, so the representation that wraps by
construction is the only sound one. Refused outright rather than made
conditional on a wrap proof, because before #162 **no unsigned param could
carry `hasRange` at all** — `dsl_typebridge`'s enum arm declines to attach
one, for exactly this reason — so there is no existing promotion to preserve,
only one not to introduce.

`nnkCharLit` deliberately keeps the historical 64-bit signed answer: Nim has
no `+` on chars, so a char range carries no arithmetic obligation to get
wrong.

## Slice status — ALL FOUR LANDED

| # | Slice | Commit | Nature |
|---|---|---|---|
| 1 | signed narrow widths, inline formal | `8ee0664` | fix (walker 128→129) |
| 2 | unsigned bases wrap, never promote | `9a36e2c` | fix |
| 3 | the named-alias route | `9f3a562` | fix |
| 4 | pins + non-regression anchor | `ef9124d` | pins only |

### Slice 1 — the floor

`rangeBaseType` (`smt/dsl_typebridge.nim`) + the structural `range[lo..hi]`
arm. Scope limited to the signed narrow widths so the slice is sound
end-to-end on its own; unsigned needed its promotion guard to land in the
same change, so it waited for slice 2.

`mul32` answers `sxRaised` in **both** integer modes. The #161 trip-wire
retires here, as its own doc instructed.

### Slice 2 — unsigned

Two changes that have to land together: `rangeBaseType` recovers signedness,
and `allocateSym` adds `p.ty.signed` to `promoteSound`. Without the second,
correcting the first would model `uint8` arithmetic as non-wrapping
unbounded `Z3Int` — a new soundness hole in the same class as #161 slice 3.

### Slice 3 — the named-alias route

`classifyType`'s `nnkSym` arm had its own copy of the 64-bit answer. Its
literal-kind guard also admitted only `nnkIntLit..nnkInt64Lit`, so
`type Weight = range[0'u16..60_000'u16]` did not merely classify wrongly — it
failed the guard, fell through to the unsupported-parameter-type path, and
degraded the **entire run** to `sxUnknown`. Both arms now call
`rangeBaseType`, so a third route cannot drift.

### Slice 4 — pins, no implementation

Every test passed on first run. Pins int8/int16 widths, the plain-`int`
non-regression anchor, range tightening at a 32-bit sort, and that slice 2's
unsigned ban did not reach into signed.

## Method note — the oracle is executed, not asserted

Every symbolic expectation in `tests/tsymex_162_range_base_width.nim` is
paired with the same computation **run for real in the same file**:

```
mul32(100_000, 100_000)    → raises OverflowDefect
mul8(100, 100)             → raises OverflowDefect
addU8(200, 100)            → 44          (unsigned wraps silently)
addAlias(60_000, 60_000)   → 54_464
mulPlain(100_000,100_000)  → 10_000_000_000   (int base, no defect)
```

That is deliberate. A width bug is exactly the kind of defect where a test
can encode the same wrong model as the code and pass. Running Nim itself
removes the model from the loop.

## Blast radius

Ranges written over plain `int` bounds classify **exactly** as before — that
is every range in the suite predating this issue (`command grep -rn
"range\[" tests/*.nim` shows only `tsymex_161`'s, which are `'i64`, and
plain-`int` ones elsewhere). `Natural`/`Positive` have dedicated handlers and
are untouched. Array index ranges go through a different arm.

## Walker versions

- **129** — #162. Verdict change: `a * b` over `range[0'i32..100_000'i32]`
  answered `sxUnsat` under both modes at 128, answers `sxRaised` at 129.
  `tests/tsymex_phase15_CR2_cachekey.nim` pin updated; floor pinned in the
  round's test file.

## Gates run

| Gate | Result |
|---|---|
| `tsymex_162_range_base_width`, `c` | 15/15 |
| `tsymex_162_range_base_width`, `cpp` | 15/15 |
| `tsymex_161_overflow_obligation`, `c` | 13/13 (trip-wire retired) |
| `tsymex_161_overflow_obligation`, `cpp` | 13/13 — this also clears #161's one deferred gate |
| `tsymex_phase15_CR2_cachekey`, `c` | 7/7 |
| `tsymex_phase2_abstraction`, `c` | 5/5 |
| `tsymex_rectify_abstraction`, `c` | 2/2 |
| `tsymex_phase14_nonenum_disc`, `c` | 1/1 (named range alias as variant disc) |
| full `-f tsymex` sweep diff | **see below** |

Registered in `nelli.nimble`'s `test` task, so it is not sweep drift and
`derive-ci-suites.ps1` pulls it into the `symex-mingw` corpus.

## Sweep baseline

Same procedure as #161 — see that handoff, and the
`sweep-baseline-contamination` memory. Short version: pin a worktree to the
base sha and **copy `_deps` and `nim.cfg` into it**, or every test fails to
compile and the log is 100% `rc=1`.

## Completeness check — the three routes into a range

Asked explicitly rather than assumed, because slice 3 proved a second route
existed and that fixing one arm left the defect a `type` declaration away.

| Route | Reaches | Status |
|---|---|---|
| inline formal (`getTypeInst`) | slice 1 | fixed |
| named alias (`getImpl`) | slice 3 | fixed |
| object FIELD (`classifyFieldType`) | falls through to `classifyType` | inherits the fix — **but see below** |

## Surfaced, NOT fixed here — object fields drop their declared range

Probing the third route turned up a **separate, pre-existing bug**, reported
rather than folded in:

```nim
type Cfg = object
  w: range[0..100_000]
  h: range[0..100_000]

proc area(c: Cfg) =
  let a = c.w * c.h
  symexTarget("t")
  discard a

discard symexFind(area, tRaisedExn("OverflowDefect"))
# Error: unhandled exception: value out of range:
#        9223372036854775792 notin 0 .. 100000 [RangeDefect]
```

`ClassifiedType.range` is dropped for object fields — only `.ty` is kept — so
a range-typed field gets **no range constraint**, the model picks a value
outside the declared range, and witness construction then **crashes the
user's test process** with an unhandled `RangeDefect`. A crash, not a wrong
verdict.

Not #162, and not caused by it: the repro above uses **plain `int` bounds**,
the one shape this issue provably does not touch, and it fails identically
with an int64-scale witness. The narrow-width variant
(`range[0'i32..100_000'i32]` fields) fails the same way with an int32-scale
one. Worth its own issue; not filed (filing is outward-facing).

Probes left in `scratchpad/bench/` (gitignored): `probe_range_field.nim`,
`probe_range_field_plain.nim`, plus `probe_range_ast.nim`,
`probe_range_alias_ast.nim`, `probe_range_truth.nim`.

## Open items

- Unsigned 64-bit ranges (`range[0'u64..…]`) still funnel their bounds
  through `IRParam.rangeLo/rangeHi: int64`, so a bound above `int64.high`
  round-trips negative. Pre-existing and unchanged by this issue: such a
  range is not expressible with literal bounds anyway (`high(uint64)` is a
  symbolic bound and falls out of the structural arm). Noted so it is not
  rediscovered as new.
- #161's five surfaced-but-unfiled follow-ups are still unfiled; see that
  handoff.

## Resume command

```
git -C /home/corey/projects/nim/libs/proptest log --oneline -6 rfc-162-range-base-width
```

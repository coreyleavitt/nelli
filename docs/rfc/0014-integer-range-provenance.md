+++
type    = "rfc"
id      = "0014"
title   = "RFC — integer-range provenance: only declared-range params carry a bound"
state   = "seed"
wiring   = "unproven"
stage   = "rfc"
profile = "rfc-flow@3"

[[item]]
id    = "i1"
title = "S0 representation: widen the three bound fields to Int128, or decline"
state = "open"
owner = "corey"
lean  = "widen"
+++

# RFC — integer-range provenance: only declared-range params carry a bound

- **Status:** seed — composed 2026-09-20 from four issues (#166, #167, #168,
  #169) filed out of the #161–#163 audit. The mechanism is identified, the
  slice order is forced by a measured blowup, and the representation choice in
  S0 is the one open item. Nothing is designed past the slice sketch in §4.
- Category: symex
- Size: L
- Value: high
- **Depends on:**
  - none open. Builds directly on issue #161 (the `ziWidth`/`ziSigned` stamp
    and `tryDischargeOverflowInt`) and issue #162 (`IRType.itInt`'s range
    fields), both landed on `main` at `2e675c7`.

## §0 — Thesis

The abstraction layer can prove an integer bound for exactly one kind of value:
a parameter whose Nim type *is* a `range[lo..hi]`. Every other integer in a
symbolically-executed program carries no interval at all —

- a literal-initialised local, `var acc = 0`;
- a `let` bound to an expression, `let s = a + b`;
- a scan-traced accumulating offset, the thing `collectIntOffsetParams` exists
  to find.

Two consumers read interval evidence, and both fall back to "unknown" when it
is absent:

| consumer | site | behaviour with no interval |
|---|---|---|
| `tryDischargeOverflowInt` | `runtime.nim:4737` | cannot prune the overflow fork; hands it to Z3 |
| `collectBanFromExpr` | `abstraction.nim:358` | node is not "provably inside the window"; bans promotion |

**The four issues in this RFC are not four defects. They are one missing
capability, whose absence has been paid for once in soundness and twice in
precision.** That is the claim that makes them one doc, and §2 is the argument
for it.

The soundness payment is the important one, because it is *derived* from the
precision gap rather than independent of it. `isIntOffset` promotions
deliberately do not stamp a width:

```nim
let soundWidth = if promoteSound: p.ty.width else: 0   # runtime.nim:13298
```

so `lowerArith` pushes no `overflowCondInt` and derived arithmetic on a
scan-traced offset **drops the OverflowDefect fork entirely** (#166). The
rationale is recorded at `canonicalize.nim:2137` and tracked as open walker gap
**W8** at `canonicalize.nim:434`. It is not an oversight: stamping the width
with no interval to prune against reintroduces a measured blowup —
`tsymex_r6_b4_readcstring.nim` went from sub-minute to not finishing, because
with no range in the initial path condition every emitted fork looks
satisfiable and Z3 explores all of them.

So the sequence is forced. Build the provenance first, and #166 closes as a
consequence. Stamp the width first, and the suite stops finishing.

## §1 — Evidence

### 1.1 Precision, measured

`scratchpad/bench/probe_obligations.nim` (gitignored), `isOptimised`, at
`95f7669`:

| SUT | obligations | discharged | live |
|---|---|---|---|
| `boundedAccum` — `var acc = 0; while i < n: acc = acc + k`, `n: range[0..24]`, `k: range[0..1000]` | 5 | 0 | 5 |
| `constrainedChain` | 2 | 2 | 0 |
| `ladder` | 3 | 3 | 0 |

`acc` is bounded by `24 * 1000`. Every one of those five forks is UNSAT. The
two SUTs that discharge fully are the ones whose arithmetic is over
declared-range params only — which is precisely the boundary this RFC moves.

### 1.2 The whole-program ban

#161 slice 3 made `isOptimised` sound under unchecked arithmetic
(`arithChecks` without `acOverflow`) by having `collectBan` ban promotion **for
the whole run** when any add/sub/mul/neg is not provably inside the type's
window. The ban is whole-program on purpose: a partial ban leaves one param
BV-sorted and another Int-sorted, and `reconcileInt` converts the BV side up to
an unbounded Int, reintroducing exactly the non-wrapping arithmetic the ban
exists to prevent.

Two costs, recorded in the code comment at that site:

1. An unprovable node *anywhere* disables promotion *everywhere* for that run.
2. Locals carry no interval in the scan, so `let s = a + b` makes every later
   use of `s` unprovable even when `a` and `b` are ranged.

Net effect on unchecked builds: `isOptimised` degrades toward `isExact`. Sound,
and the honest answer for whole-program analysis of wrapping arithmetic — but
it gives up the speedup on exactly the code the abstraction exists for.

### 1.3 The representation is `int64` in all three places

This is the part the issues did not connect, and it is why #169 is slice 0 of
this RFC rather than a cosmetic chore filed beside it.

| field | site |
|---|---|
| `Interval.lo`, `Interval.hi` | `types.nim:1229` |
| `IRType.itInt.rangeLo`, `.rangeHi` | `types.nim:126–127` (#162 slice 5) |
| `IRParam.rangeLo`, `.rangeHi` | `types.nim:1121–1122` |

A `range[0'u64..hi]` whose `hi` exceeds `int64.high` round-trips negative
through every one of them.

**Today that is nearly harmless**, and #169 says so: such a range is not
expressible with literal bounds anyway (`high(uint64)` is a symbolic bound and
falls out of the structural arm), #162 slice 2 never promotes an unsigned
param, and the wrapped value only mis-asserts the `bvRangeConds` constraints
on a BV.

**The moment this RFC lands it stops being harmless.** Once intervals flow
through derived arithmetic, a wrapped bound is no longer a wrong *constraint* —
it is a wrong *proof*. The pruner discharges a fork that is actually SAT, and a
discharged fork is never handed to Z3, so nothing downstream can catch it. A
latent representation bug becomes a soundness bug the day its consumer starts
reasoning with it. That is the whole argument for doing it first.

## §2 — Why these four are one mechanism

Read against the wiring-audit taxonomy, the set is not a theme:

- #167 and #168's cost 2 are the **same** absence — an interval on a local —
  observed by the two **different** consumers in §0's table.
- #168's cost 1 and its first fix route (per-param bans over a provenance
  dataflow) need the same def-use information S1/S2 build. It is not a
  separate analysis.
- #166 is that absence again, on a third value kind, where the fallback was not
  "be imprecise" but "emit no obligation" — so the same gap surfaces as
  unsoundness instead of slowness.
- #169 is the representation the other three store their results in.

One lattice, one dataflow, one representation, two existing consumers. The four
issues are four *symptoms* at four call sites.

## §3 — Design sketch

Not designed yet; this is the shape, for `/architect` to accept or replace.

**An interval environment in the walker.** `SymVal.ziIvl` already exists on
`svInt` (`runtime.nim:299`) and `arithInt` already composes intervals through
`bAdd`/`bSub`/`bMul` (`runtime.nim:4453–4463`). What is missing is (a) a seed
for non-param values and (b) survival across assignment and loop iteration.
The loop case is where this gets hard — `acc = acc + k` inside `while i < n`
needs a fixpoint (widen to the type window after N iterations, or derive the
closed form from the trip count, which the scan already computes for offsets).

**Two consumers, one predicate.** Both §0 consumers are asking the same
question: *is this expression provably inside a window?* They currently ask it
with different code over different representations (`SymVal` at runtime,
`IRExpr` in the scan). A single `provableInterval(e): Option[Interval]` over
the IR, consulted by both, is the deep-module version and is what makes S2 and
S3 cheap instead of duplicative.

**S4's interval comes from the scan, not the walker.** An offset param's bound
is a property of the accumulating scan that traced it (`collectIntOffsetParams`
already knows the low bound — it is what the promotion exists for). That is a
closed form, not a fixpoint, so S4 does not depend on solving the loop case
in general.

## §4 — Slice plan

**The order is load-bearing.** S4 before S1–S3 reintroduces the §0 blowup.

| # | slice | closes | gate |
|---|---|---|---|
| S0 | widen the three bound fields (§1.3) to `Int128`, the type the choice IR already uses for integer constraints; or decline an out-of-`int64` bound with a classified reason | #169 | `type Big = range[0'u64..0xFFFF_FFFF_FFFF_FFF0'u64]` with a target guarded by `x > 0x8000_0000_0000_0000'u64`; walker version bump + CR2_cachekey pin |
| S1 | seed an interval on a literal-initialised local and propagate it through assignment in `arithInt`'s BV arm (or reconcile such a local to `svInt` once every operand has an interval) | #167 | `boundedAccum` reports 5 obligations, **5 discharged, 0 live**, same verdict; promote `probe_obligations.nim` out of `scratchpad/` into a registered test |
| S2 | give the wrap scan a local interval environment, so `let s = a + b` is provable when `a` and `b` are ranged | #168 cost 2 | `probe_wrap.nim`, both modes agree: `a * b < 0` is `sxSat` for `a, b: range[0'i64..4_000_000_000'i64]` unchecked |
| S3 | per-param ban over a provenance dataflow — a param stays BV only if its **own** def-use chain contains the unprovable node | #168 cost 1 | `reconcileInt` must **refuse** to bridge a banned BV to an Int rather than convert up; that refusal is the soundness condition, and without it a partial ban is unsound. Four-function abstraction benchmark under unchecked settings |
| S4 | derive the offset params' proven interval from the scan's closed form, then stamp `ziWidth`/`ziSigned` and retire walker gap W8 | #166 | an offset-promoted value multiplied past the window makes `tRaisedExn("OverflowDefect")` answer `sxRaised`; **and** `tsymex_r6_b4_readcstring.nim` still finishes |

Rejected for S3: encoding the wrap as a Z3 Int `mod 2^W` constraint and keeping
the promotion. Precise, but mod-by-2^64 is a real performance risk and this
codebase has CR-17 non-termination history with mixed-theory terms. If S3's
dataflow route fails, that is the fallback to reconsider — as an escalation,
not a silent substitution.

## §5 — Gates

Standard whole-suite discipline: `scripts/sweep.sh` against
`nelli-sweep-baselines/base-bbde48c.log` via `scripts/sweep-diff.sh`, per slice.
Two additions specific to this RFC:

**Timing is a gate here, not a nicety.** Every slice from S1 on changes how
many forks reach Z3. The B4/B5/B6 corpus is the measurement the #166 deferral
was made on, so it is the measurement that releases it. All three are
Linux-measurable — `b4_readcstring` is **not** on `sweep.sh`'s
`known_linux_hangs` list, and `b5_chained`/`b6_optionregion` are skip-listed
only on the Windows `symex-mingw` corpus. Record wall-clock per slice, not just
pass/fail; a slice that keeps the suite green while tripling B4 has failed.

**Walker version.** S0, S1, S2 and S4 all change walker semantics: bump
`symexWalkerVersion` (`smt/canonicalize.nim`), add the round's version-floor
pin, and update the CR2_cachekey pin test.

## §6 — Open items

**i1 (S0 representation) — owner: corey.** Widen the three bound fields to
`Int128`, or have `rangeBaseType` decline a `uint64` bound above `int64.high`
with a classified reason.

*Lean: widen.* Declining is cheaper and is defensible today, but it spends the
same walker-version bump and the same pin test to buy a permanent expressiveness
hole, in a representation that three separate features now store results in.
Recorded as an item rather than decided because it fixes the numeric
representation of the whole abstraction layer for everything after it, which is
a bigger commitment than a slice normally makes. If you would rather I just
widen it, say so and this becomes S0 with no fork.

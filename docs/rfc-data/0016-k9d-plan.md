# RFC-0016 K9d — pin the verdict suites with no native idiom (W-54): survey and slice plan

Base: `origin/main` 7f6dca28 (walker 412). Written by K9d-1.

## The figure and the ratchet

F-03 (`docs/rfc/0016-research/F-tests-finishline.md`, `F-testclass.tsv`) counted
481 of 696 verdict-asserting `tsymex_*` suites with no native idiom at 83c1d304.
No allowlist of those suites existed, so K9d-1 adds the ratchet:
`tests/tsymex_0016_k9d_census.nim` (registered). A suite is
**verdict-asserting** when its code (comments stripped) names `sxSat`,
`sxUnsat` or `sxRaised`; it is **pinned** when its code uses a native idiom
(F-03's list — `symexCaptureBegin`, `nativeHits`, `nativeRun`, `native(`,
`replayWitness`, `assertCoveredBy`, `viaCovered`, a child process — plus the
K9 verbs `pinFind`, `pinExact`, `pinCrash`, `pinNever`, `pinCap`,
`pinUndefined`, `pinRefused`). The census fails above its ceiling and below
it, so the ceiling only falls.

At 7f6dca28 the census reads **484** (1045 `tsymex_*` files, 804
verdict-asserting): F-03's 481 plus the suites added since, net of those
pinned since. The census is per file: a pinned suite may still hold a call
`pinFind` returned unpinned (a decline, an untrusted or undefined-behaviour
claim, an unsafe witness).

## The generator: `pinFind` (tests/s8cu_helpers.nim)

`pinFind(fn, target, settings...)` is the suite's own `symexFind` call — same
arguments, same `SymexResult` back — judged by K9a's `pinJudge`, so the edit
to a suite is `symexFind(` → `pinFind(` plus `import ./s8cu_helpers`
(`scratchpad/k9d/convert.py` does it mechanically, code lines only).

- trusted `sxSat`: the witness is replayed natively and must hit the target.
- trusted `sxRaised`: the raising witness is replayed and must raise that type.
- trusted `sxUnsat`: every combination of the per-parameter generated domains
  (`boundaryOf(T)`) is run natively, none may hit (capped at `pinFindCap` =
  65536 combinations, recorded as sampled beyond it).
- anything else (`sxUnknown`, untrusted, `stkUndefined` target, unsafe
  witness): returned unchanged, no record.
- record: entry `symexFind`, cell `family:generic:k9d/<file>/<fn>/<target>`.

`boundaryOf(T)`: every value for `bool`, an Ordinal enum, a one-byte ordinal,
and any ordinal spanning at most ~256 values (small `range`s); otherwise the
boundary sample (`boundaryInts`' points inside the type; unsigned: 0, 1, 7,
high-1, high). Other types are a compile error naming `pinExact` — each later
family adds its `boundaryOf` overload.

**Known limit (F-07): `symexAssume` is a no-op natively.** An `sxUnsat` pin
over a SUT with `symexAssume` runs inputs the walker excluded, so a domain
value outside the assumption can "hit" and fail a correct verdict. K9d-1
therefore pinned no suite that calls `symexAssume`; K9d-4 lands the assume
gate first.

## Census by family (484 at 7f6dca28)

Family = the parameter shape of the SUTs passed to `symexFind` /
`symexFindAllWitnesses` / `symexForAll` in the file (heuristic, from the
signatures; `scratchpad/k9d/classify.py`). **Pure** means the file shows no
module-level `var`/threadvar and no I/O, time or process call; the impure
signal is file-level (an `echo` in a test body counts), so each impure slice
confirms per SUT before choosing a per-suite idiom.

| family | suites | pure-proc pinnable by `pinFind` | with `symexAssume` | with raise/try | generator |
|---|---|---|---|---|---|
| int (ordinal params) | 107 | yes | 15 | 35 | `boundaryOf` ordinals (K9d-1) |
| object (enum, distinct, tuple, object params) | 77 | yes (value types) | 7 | 13 | `boundaryOf` for enum (done), distinct (base), tuple/object (field product, capped) |
| string | 66 | yes | 15 | 26 | `boundaryOf(string)`: a fixed sample ("", one byte, `\0`, a high byte, a long run); the SUT's own literals are not mined, so the domain is sampled |
| regex (PCRE) | 63 | yes, per build (PCRE version/JIT row) | 7 | 32 | string domain; native is the build's PCRE; records carry the row |
| impure (globals, I/O) | 58 | no (state) | 12 | 27 | per suite: reset state per native run, `pinExact` with an explicit domain |
| seq / array / set | 37 | yes | 7 | 18 | `boundaryOf(seq[T])`: lengths 0,1,2,3 over `boundaryOf(T)`, capped |
| ref / ptr | 22 | sat only (witness heap) | 1 | 3 | witness replay; unsat by explicit nil/fresh domain |
| float | 17 | yes | 0 | 6 | `boundaryOf(float)`: ±0, ±1, NaN, ±Inf, min/max, subnormal |
| unresolved SUT (generic, lambda, proc var) | 15 | per suite | 5 | 4 | triage |
| meta (cache keys, query stats) | 12 | n/a | 3 | 4 | triage: most assert no SUT verdict; re-word or pin |
| verdict on a non-`symexFind` path | 6 | per suite | 0 | 2 | triage |
| nullary SUT | 4 | yes | 0 | 0 | `pinFind` as is (one native run) |

## Slice plan (count × ease; each ≤ ~40 suites)

| slice | scope | suites | needs |
|---|---|---|---|
| K9d-1 | this slice: census ratchet, `pinFind` + `boundaryOf` ordinals; int family, no `symexAssume`, the pre-RFC-0005 prefixes (phase1/2/3/6/14/15/16) | 43 | — |
| K9d-2 | int family, no `symexAssume`, the rest (0016, 161, 163rev, CR2a, a8, configdefaults, cr22, p1, p2a, r5, r6, r8, rectify, rfc0005) | 49 → split 2a/2b at ~25 | — |
| K9d-3 | object family, enum and distinct params (`boundaryOf` enum, distinct via base type): done, 8 converted (see the result section) | 8 | `boundaryOf` distinct |
| K9d-4 | the assume gate: `symexAssume` rejects a native run under a pin (markers.nim, opt-in threadvar set by `nativeRun`; a rejected run hits nothing), then the int family with `symexAssume` (15) | 15 | src change in `engine/markers.nim` |
| K9d-5 | object family, tuple/object params (field-product domain) | ~42 → 5a/5b | `boundaryOf` tuple/object |
| K9d-6 | string family (`boundaryOf(string)`) | 66 → 6a/6b | |
| K9d-7 | seq family | 37 | |
| K9d-8 | float family | 17 | |
| K9d-9 | regex family (string domain, per-row records) | 63 → 9a/9b | |
| K9d-10 | ref family (sat replay; unsat explicit domain) | 22 | |
| K9d-11 | impure family, per suite (state reset, `pinExact`) | 58 → 11a/11b | |
| K9d-12 | triage: unresolved, meta, non-`symexFind` path, nullary | 37 | |

After each slice the census ceiling falls by the suites pinned; K9e measures
the pins' strength (mutation kills over `runtime.nim`'s arithmetic and raise
arms) — the int family's boundary domains are where its arithmetic mutants
are expected to die.

## K9d-1 (Part B) result

The 43 suites of the int family's first slice route every `symexFind` call
through `pinFind`. All 43 pass with every definite verdict reproduced
natively; no verdict disagreed with native, so no soundness row was filed.
Census ceiling 484 → 441. Two suites first failed to compile because their
SUT returns a value (`phase15_C1_ir`, `phase15_CR14_exn_missing`); `pinFind`
now discards a SUT's result natively (pinned by `tsymex_0016_k9d_pinfind`).

One call stays `symexFind`: `phase2_overflow`'s `isLoose` test. `isLoose` is
opt-in unsound by design (ADR-0001, AUD-01), and the native run refutes its
`sxUnsat` at 255, which is the false negative that test documents. `pinFind`
reports it as a pin failure, as it should; the call carries a comment instead.

## K9d-2a/2b result

The 49 remaining suites of the int family without `symexAssume` (the 0016,
161, 163rev, CR2a, a8, configdefaults, cr22, p1, p2a, r5, r6, r8, rectify and
rfc0005 prefixes) were taken in 2a/2b; 47 route every `symexFind` call through
`pinFind`. Census ceiling 441 → 394. The int suites that call `symexAssume`
stay for K9d-4. `tsymex_rfc0005_s8ce_raiseshapes` and
`tsymex_rfc0005_s8cr_intro` have a `string` parameter, so they have no
generated domain and move to K9d-6 (string family). No verdict disagreed with
native; no soundness row was filed.

Harness fix: the witness tuple holds a `range[a..b]` parameter as its base
type, so `pinFind` generated an out-of-range domain and its native call raised
on the conversion (`assign_rangedefect`) or failed to bind (`161_overflow`).
`pinFind` now aliases each declared parameter type and generates and replays
through it; `tsymex_0016_k9d_pinfind` pins a wide-range SUT.

## K9d-3 result

`boundaryOf` gained two overloads (self-tested in `tsymex_0016_k9d_pinfind`):
an enum generates every declared value (a holey enum's holes are not values,
so `low .. high` would invent invalid ones; the declared values are read from
the type), and a distinct type generates its base type's domain, each value
converted (`showArg` prints it as the base). `boundaryOf(Cents)` is sampled
like `int`, `boundaryOf(Tiny)` over `distinct int8` exhaustive.

The slice plan's "~35" was an overestimate: the object family's 77 suites hold
object, tuple, string, seq and float parameters far more often than enum or
distinct ones. Of the 69 object-family suites without `symexAssume` (all tried
through `pinFind`), **8 convert**: `tsymex_0016_cr4_enum_layout`,
`tsymex_163rev_enum_domain`, `tsymex_163rev_enum_ordinal`,
`tsymex_163rev_enum_valueshapes`, `tsymex_163rev_range_bounds`,
`tsymex_phase15_CR15_enum_ordinal`, `tsymex_phase6_case`,
`tsymex_r6_a1_variantlit`. No verdict disagreed with native. Census ceiling
394 → 386.

Soundness finding (INT-72): `tsymex_a7_rune`'s `runeOob` is `sxUnsat` because
the walker pins a `Rune` parameter to [0, 0x10FFFF], while native `Rune` is
`distinct int32` and `Rune(2147483646)` hits the target. The suite stays
unconverted.

The 60 that stay (a failed compile with "no generated domain" for a parameter
type; targets are by the signatures' parameter types, so a suite with several
shapes goes to its latest slice):

- tuple, object or variant-object parameters (K9d-5): everything not listed
  below, including the `phase14_*` variants, `phase11_walker`, `phase4_*`,
  `rectify_*`, the `r6_*` records, `163audit_*`, `162_range_base_width`,
  `163rev_enum_field_witness`, `163rev_enum_positions`,
  `163rev_int_literal_width`, `163rev_nested_clamp`, `augmented_assign`,
  `0016_cr2_h3_epochpin`, `0016_w3z_r5b_diag`, `CR2c_witnessreader_catchall`
  (with its tuple), `rfc0005_s1c_verdict` (object and string)
- string or Rune parameters (K9d-6): `a7_rune`, `a7_runes_iter` and
  `m6_probeproto_strproto` (converted by INT-72, below), `phase15_S10b_strconv`, `rfc0005_s8bx_extractraise`
  and `_b`, `snd1_uncertain_taint`, `r1_draingap`, `phase15_g10_smoke`,
  `phase15_N0_kindgate_widen`, `rfc0005_s8d_typeheads`
- seq, set or table parameters (K9d-7): `h_containers`, `phase5_hashset`,
  `phase5_table`, `163rev_table_elem`, `phase15_M1_seq_fixedwidth`,
  `rectify_cardinality`, `rectify_mutation`, `rfc0005_s0_exhibit`,
  `rfc0005_s8e_scoping`
- distinct over float64 (K9d-8): `phase15_g4_distinct_sort`,
  `phase15_g5_distinct_borrow`
- ref parameters (K9d-10): `h_stepC_heapidentity`, `p2b_refobjconstr_expr`,
  `phase15_r9_recursive`, `rectify_refs`, `rfc0005_s8ao_remainder`

## INT-72 result (`rfc-0016-w4int72`)

INT-72 is fixed in the walker (426): a free `Rune` ranges over int32, `$r`,
`toUTF8` and `size` follow std/unicode out of range, `Rune(n)` checks int32
and an int conversion of a Rune converts its value. With that, the three
Rune-parameter suites the K9d-3 note held back convert: `tsymex_a7_rune`
(every call; `runeOob` is now `sxSat` and replays natively, its pin was the
red), `tsymex_a7_runes_iter` (the three calls without a `string` parameter)
and `tsymex_m6_probeproto_strproto` (`hexEqFF`, `runeEqA`, `hexNeGG`). The
new `tsymex_0016_int72_runedomain` pins the domain and each operation through
`pinFind`. Census ceiling 386 → 383.

## K9d-4 result (`k9d4`)

The assume gate: `symexAssume` in `engine/markers.nim` is unchanged unless a
pin's native replay arms the gate (`symexAssumeGateOpen`, called by
`nativeRun`); then a false `cond` sets a sticky `rejected` flag and raises
`SymexAssumeRejected`, a `Defect`, so a SUT's `except CatchableError` does not
see it. A SUT that catches `Exception` or Defect still has its run rejected,
because `nativeRun` reads the flag, not the exception: a rejected `NativeRun`
clears its hits and raised type, so it hits nothing and raises nothing. The
walker's semantics are unchanged, so no walker bump. `pinFind` counts rejected
runs; a trusted `sxUnsat` whose generated domain is entirely rejected fails
the pin as vacuous, and a sat or raised witness that violates the assumption
fails as "rejected by symexAssume". `tsymex_0016_k9d_pinfind` pins an
assume-guarded unsat, a sat witness, the vacuous domain, a swallowing SUT, and
the unarmed behaviour.

17 suites convert, all passing with every verdict reproduced natively; no
verdict disagreed, so no soundness row. The 15 int suites with `symexAssume`
and two object-family ones (`phase15_A1_arithmetic`, `phase15_A1_comparison`).
Census ceiling 383 -> 366. Deferred: `phase15_C1_canonical_kind` (float
parameter, K9d-8); `rfc0005_s8aa_remainder`, `rfc0005_s8ac_remainder`,
`rfc0005_s8ac_remainder_b`, `rfc0005_s8c_resolution`, `tot1_totality_corpus`
(tuple or object parameters, K9d-5).

## K9d-5 result (`k9d5`)

`boundaryOf` gained tuple and plain-object (and variant-object) domains, built
by `objectDomain` from each field's own `boundaryOf`:

- a tuple or object is the product of its fields' domains, with the fields
  that exist together crossed: `fieldRows` is the full product when it is at
  most `fieldProductFull` (4096) values, else the all-pairs covering array
  `pairwiseRows` (deterministic greedy: each row starts from the first
  uncovered pair and fills the other fields with the value that covers the
  most uncovered pairs);
- when the product is over 4096, a field of more than 16 values (a one-byte
  ordinal's 256) is first thinned to nine (the first three, the three about
  the middle, the last three: `low`, `0`, `high` for an ordinal), so two
  `int8` fields cross as 9 x 9, not 65536. A thinned or pairwise domain is
  recorded `sampled`; an aggregate whose fields are all exhaustive and whose
  product is under the limit stays `exhaustive`;
- a case object is generated per discriminator value (the discriminator's own
  domain), with that branch's fields crossed together with the common ones, the
  discriminator assigned under `cast(uncheckedAssign)`; nested case objects
  and inherited fields are followed; `ref` objects are skipped (K9d-10);
- `pinFind` itself no longer truncates a parameter product at the cap: beyond
  `pinFindCap` it runs an all-pairs array over the parameters' domains.

Coverage guarantee (the oracle may be any finite subset): a sat or raised
witness is replayed exactly, whatever the domain; for an unsat verdict, each
pair of fields that exist together (and each pair of parameters) meets in every
combination of their domain values, at least pairwise, with the thinned
fields' values standing for the field's boundary. The record's `[n]` is the
domain size. `tsymex_0016_k9d_pinfind` pins a tuple, an object, a variant
object (with and without an `else`), a nested tuple, a sat witness outside the
pairwise set, the size bound and the pairwise property of `pairwiseRows`.

18 suites convert, every verdict reproduced natively; no soundness row.
`tsymex_162_range_base_width`, `163audit_wave2`, `163rev_enum_field_witness`,
`163rev_int_literal_width`, `augmented_assign`, `phase11_walker`,
`phase14_arm_field_zero_init`, `phase14_disc_promotion`, `phase14_else_arms`,
`phase14_multivariant_walker`, `phase14_multivariant_witness`,
`phase14_nonenum_disc`, `phase14_symbolic_disc_reassign`, `phase4_nested`,
`phase4_tuple`, `r6_a2_retbind_variant`, `r6_lows_blockparse`,
`rectify_variants`. Census: the int72 merge brought the count from 366 to 365
(the ceiling was reconciled by the same commit), the 18 conversions to 347.

The other 45 of the 63 not-yet-pinned object-family suites (the plan's 77 less
the 19 already pinned, plus the five K9d-4 deferrals) hold a parameter whose
domain is another family's, so they stay (the compile error names the type):

- string or `cstring` (K9d-6): `phase15_N0_kindgate_widen`,
  `phase15_S10b_strconv`, `phase15_g10_smoke`, `r1_draingap`,
  `rfc0005_s1c_verdict`, `rfc0005_s8bx_extractraise`, `snd1_uncertain_taint`,
  `tot1_totality_corpus` (cstring)
- seq, set, table, array of enum (K9d-7): `163audit_range_elem`,
  `163rev_enum_positions` (array), `163rev_table_elem`, `CR2c_witnessreader_catchall`,
  `phase15_M1_seq_fixedwidth`, `phase15_fieldcontainer`, `phase5_hashset`,
  `phase5_table`, `r6_bug2_scopeddecline`, `r6_n13_reassign_seqarm`,
  `r6_n27_hof_placeholder`, `r6_n49_dottedfield_mutation`,
  `r6_r1_placeholder_totality`, `rectify_cardinality`, `rectify_mutation`,
  `rfc0005_s8aa_remainder`, `rfc0005_s8ac_remainder_b`,
  `rfc0005_s8bx_extractraise_b`, `rfc0005_s8c_resolution`,
  `rfc0005_s8e_scoping`
- float (K9d-8): `phase15_C1_canonical_kind`, `phase15_F9c_variant_float`,
  `phase15_g4_distinct_sort`, `phase15_g5_distinct_borrow`,
  `r6_n36_raise_degrade_b`, `r6_n36_raise_degrade_c`
- ref (K9d-10): `0016_cr2_h3_epochpin`, `0016_w3z_r5b_diag`,
  `163rev_nested_clamp`, `h_containers`, `h_stepC_heapidentity`,
  `p2b_refobjconstr_expr`, `phase15_r9_recursive`, `rectify_refs`,
  `rfc0005_s0_exhibit`, `rfc0005_s8ac_remainder`, `rfc0005_s8ao_remainder`

## K9d-6 result (`k9d6`)

`boundaryOf(string)` is a deterministic finite set, never the type: at most
`stringDomainCap` (2048) values, in priority order, deduplicated. It holds

- the empty string and every byte of a 25-byte alphabet (`'\0'`, `a`, `z`,
  `0`, `9`, space, `-`, `\x7F`, `\x80`, `\xFF`, `A`, `Z`, `_`, `.`, `/`, `\n`
  and the UTF-8 leads and continuations `C3 A9 E2 82 AC F0 9F 98 BF`);
- the whole multi-byte sequences (`é`, `€`, an emoji, an overlong `C0 80`, a
  truncated 3- and 4-byte lead, a surrogate, a code point past U+10FFFF);
- **what the SUT's own source says**: `pinFind` harvests, at macro time, every
  string literal and char literal in the target proc's typed AST, followed
  into the routines and consts it names that live in the same directory
  (stdlib is not followed; a `symexTarget`, `newException` or `echo` call's
  arguments are not data), and its small integer literals (1..256). Each
  literal (the first 32) is in the set along with its characters; its proper
  prefixes and suffixes; it with one byte appended or prepended
  (`\0 a 0 space \xFF`); each single byte removed; each byte changed (to +1,
  -1, `a`, `\0`); upper and lower case; one space of padding. For each integer
  literal `k`, strings of `k-1`, `k` and `k+1` bytes (up to 16 thresholds), and
  fixed lengths 5, 8, 16, 33, 64, 100;
- all pairs over a 10-byte alphabet and all triples over a 5-byte one.

The set is bounded however many literals the SUT holds (the neighbour stages
are filled in order and the cap truncates the last). A string field of an
aggregate, or a string parameter beside another string whose two domains would
multiply past `pinFindCap`, is cut to its first 64 values (`stringCore`: empty,
the single bytes, then the literals), so two string parameters cross 64 x 64
and an object with a string field crosses as pairwise rows. A string domain is
always `sampled`; the record's `[n]` is its size, and `showArg` shows a
string quoted and escaped (a record is text: the raw NUL and high bytes had
made the jsonl invalid UTF-8).

Coverage guarantee: a sat or raised witness is replayed exactly, whatever the
domain. For an unsat verdict, the pin covers every string of up to 3 bytes over
the small alphabets, the single bytes over the full one, and each SUT literal
with its one-edit neighbours and length thresholds (up to the 2048 cap); a bug
that needs a string outside that set (a 4-byte string off any literal, a
neighbour of a 33rd literal) is not found. `cstring` takes the same set minus
the values with a NUL (Nim's `cstring` ends at it), their storage held for the
process. The walker declines a `cstring` parameter (`feUnsupportedParamType`),
so a `cstring` call returns unpinned as it came; the domain is there for the
day it does not. The witness of an unmodelled type is not converted back
(`witnessAs`).

`tsymex_0016_k9d_pinfind` pins the literal harvest (strings, chars, a helper,
the label exclusion, int thresholds), the fixed core, the hinted neighbours,
the bound, a sat witness outside the set, a tuple, an object and two string
parameters, a planted unsat claim refused over a literal's neighbour, the
cstring domain, and that hints do not outlive a `pinFind` call.

66 suites convert (two commits, 33 each), every verdict reproduced natively;
no native/walker disagreement, so no soundness row. `tsymex_rfc0005_s8ai_semantic`
and `_c` pin through a helper-file `include`. Census ceiling 347 -> 281.

Deferred, with the slice that owns them: `phase15_g10_smoke`,
`phase15_N0_kindgate_widen`, `phase15_S10b_strconv`, `snd1_uncertain_taint`
(a float parameter, K9d-8); `r1_draingap`, `rfc0005_s8bx_extractraise` (a
`seq[int]` and a table's pair sequence, K9d-7); `tot1_totality_corpus` (a
`seq[Widget]` besides its `cstring`, K9d-7); `rfc0005_s8cb_order` (its SUTs
call `quit`, which ends the test process natively, so it needs the child-process
idiom, K9d-11).

## K9d-7 result (`k9d7`, WIP: the first pass of the collection family)

`boundaryOf` gained `seq[T]`, `array[I, T]`, `set[E]`, `Table[K, V]` and
`HashSet[T]` (an `openArray[T]` or `varargs[T]` parameter is passed a `seq[T]`,
`fnParamTypes`). Each is a deterministic finite set in priority order, at most
`seqDomainCap` (2048) values, built from the element domain's CORE (`coreOf`,
at most 8 values: all of a small domain, else the low end, the middle and the
high end; a string's first three values and the SUT's literals; an ordinal other
than bool/enum also gets the SUT's first two integer literals, or char literals
for a `char`, each with its neighbours, up to 6 more):

- `seq`: empty; each single; the leading pairs and triples; at each integer
  literal `k` of the SUT (and 4, 5, 8) the lengths k-1, k, k+1 filled with
  all-equal (low, high, middle), ascending, descending, an outlier at either end
  (of either kind) and adjacent duplicates; every pair; every triple (the full
  product up to 512, else all-pairs). Always sampled;
- `array`: fixed length; the full product over positions up to 4096, else the
  all-pairs array (positions up to 32), every all-equal array, and the length
  patterns. Exhaustive only when the element domain is exhaustive, the core is
  all of it and the product is full;
- `set[E]`: empty, full, each singleton, each pair, each complement of a
  singleton, all members; exhaustive when E has at most 4 values;
- `Table`/`HashSet`: empty, singles, every ordered pair of the first eight keys,
  ascending and descending triples of the first five, all keys either way; a
  table's values from a 3-value core as all-equal, ascending, descending and an
  outlier at either end. The insertion orders are both kept (iteration order of
  a colliding table is observable); a repeated key adds no value (the last write
  wins), so it is not a separate member. Never exhaustive.

A collection in an aggregate or beside another is cut to its first 64 values
(`prefixDomain`, as `stringCore`). Coverage guarantee: a sat or raised witness
is replayed exactly; for unsat, every length 0..2 sequence over the core, every
all-pairs of positions in an array and every set/table/hash set above, plus the
length thresholds the SUT's integer literals name (up to 256). A bug that needs a
longer sequence off any literal, an element outside the core, or a literal above
256 is not found. `tsymex_0016_k9d_pinfind` pins one family per test, a sat
witness outside the domain, a planted unsat claim refused over a harvested
length, and the size bound.

49 suites convert (local c runs, rc 0, every verdict reproduced natively); the
census ceiling 281 -> 232: `0016_w3z_p5_shortcircuit_guard`, `163audit_w9`, `163rev_enum_positions`, `a6_symlen_hof`, `g1a_mode`, `phase15_A1_boolean`, `phase15_A2a_atomicir_audit`, `phase15_C2_staticparams`, `phase15_C4_hof`, `phase15_g7_static_param`, `phase16_CR1b_tail_local`, `phase16_D1a_defect_routeraise`, `phase16_m4_str_add_ampeq`, `phase4_array`, `phase4_oob`, `phase5_hashset`, `phase5_seq`, `phase5_table`, `phase6_break`, `phase6_for`, `r1_draingap`, `r4_seq_slice`, `r5_discard`, `r6_b1_stringbacked`, `r6_b7r2_pathscope`, `r6_b7r_bytescan`, `r6_lows_collectors`, `r6_n13_reassign_seqarm`, `r6_n27_hof_placeholder`, `r6_n28_shadow_collision`, `r6_n31_block_counter`, `r6_n37_raise_residue`, `r6_n49_dottedfield_mutation`, `r6_r4_collector_scoping`, `rectify_cardinality`, `rectify_mutation`, `rectify_nested_arrays`, `retest_c3_bitwise_guard`, `retest_c6_tuple_chain`, `rfc0005_s8aa_remainder_checksoff`, `rfc0005_s8ba_remainder_c`, `rfc0005_s8bm_stability`, `rfc0005_s8bq_remainder`, `rfc0005_s8bx_extractraise`, `rfc0005_s8bx_extractraise_b`, `rfc0005_s8t_termination`, `rfc0005_s8w_remainder`, `rfc0005_s8w_remainder_b`, `rfc0005_s8w_remainder_b_checksoff`.

Not converted (reverted, still unpinned), with the owner:

- ref or ptr in a parameter (K9d-10): `163audit_range_elem`,
  `CR2c_witnessreader_catchall`, `h_containers`, `rfc0005_s0_exhibit`,
  `rfc0005_s8aa_remainder`, `rfc0005_s8ac_remainder`,
  `rfc0005_s8ac_remainder_b`, `tot1_totality_corpus` (also float/cstring);
- float (K9d-8): `phase15_g10_smoke`, `rfc0005_s8ba_remainder`;
- the five pin failures of the first pass are triaged in K9d-7b below; none
  was a walker/native disagreement.

### K9d-7b (`k9d7b`): the five failures, and the `fn`/lambda pass

Each failure was a harness defect, so no worklist row was filed.

- `163rev_table_elem`, `163rev_seqelem_promoted_int`: the witness tuple holds
  `Table[string, range[0..100]]` as `Table[string, int]` and
  `seq[range[1..100]]` as `seq[int]`; `witnessAs` tried `T(x)`, which does not
  compile for a container of a range, and fell back to `default(T)`, so the
  replay ran the SUT on an empty table (KeyError) and an empty seq (the
  assume rejected `i < xs.len`). `convWitness` now converts a seq, array,
  Table, HashSet and set element by element (each element range-checked, as
  the SUT's own conversion would be), and a value with no conversion fails the
  pin when replayed instead of replaying a default (a tuple holding a ranged
  container lands there: its field-wise copy does not compile in C, the
  `seq[range]` and `seq[int]` fields sharing one `=sink` instance).
- `rfc0005_s8c_resolution`: not the distinct conversion. The suite declares
  `add(var seq[int], int)` (appends nothing) and `len(seq[int16])` (7) on
  purpose; an overloaded call in a generic routine is looked up again where
  it is instantiated, so the generated `int` domain came out empty and the
  `seq[int16]` core was indexed past its end. The generic domain code now
  appends and measures through closed helpers (`domPut`, `domLen`, `domHas`,
  which reach the stdlib by qualified name), and `pinFind`'s generated code
  binds them with `bindSym`. Self-test: `tests/k9d_hostile.nim` overloads
  `add`/`len`/`items` and instantiates the domains under them.
- `phase15_M1_seq_fixedwidth`: a Nim defect, plain reproducer (gcc):

      var a: seq[seq[cuint]]
      a.add @[1.cuint]
      var b: seq[seq[uint32]]
      b.add @[1u32]   # C: incompatible types when assigning

  `cuint` and `uint32` are one Nim type but two C types, and `system.add`'s
  instance is shared; nim-z3 declares a `seq[seq[cuint]]`, so the
  `seq[uint32]` domain's `add` did not compile. `domPut` (setLen and an index
  store) sidesteps it; the hostile module pins it.
- `rfc0005_s8q_termination`: the vacuous test is `sutAssumeContradiction`,
  whose assumption (`s[0] == 'a' and s[0] == 'b'`) has no model by design: no
  domain can be steered into an empty one, and the refusal is right. That
  call stays `symexFind`; the test checks that `pinFind` refuses it and that
  no candidate passes the assume natively. The suite's other verdicts are
  pinned.

A further harness defect found in the pass: an `sxUnsat` pin runs its domain
in this process, so a SUT that calls `quit` ended the suite
(`rfc0005_s8cb_order`'s exit magics). `pinFind` now refuses at compile time a
SUT whose own body calls `system.quit` (a callee is not inspected); those
calls stay `symexFind` (`s8cb_order`'s `cq`, `w1_parity`'s `w1QuitFirst`).
`s8bo_replay`'s "the replay's writes stay in its child" also stays
`symexFind`: it proves the SUT never ran in this process, which a native pin
would contradict.

93 suites convert (local c runs, rc 0): the five above and 88 reached
through `fn`/a template or lambda, the `symexForAll`/`symexFindAllWitnesses`
suites with collection parameters (their `symexFind` calls are pinned; their
ForAll/FindAll calls are not yet, and no counterpart was needed for the
census since each also calls `symexFind`), `r6_b4_readcstring` and the
remaining seq-family suites: `0016_admir`, `0016_cr1_sharedenv`, `0016_d1_narrow_opaque`, `0016_f2hot_skiplimit`, `0016_k7b_unsupported`, `0016_k9cg_unbacked`, `0016_prc02m_find`, `0016_r2b_blocksync`, `0016_s8cj_mkunique`, `0016_w4perf_demandtail`, `0016_w4perf_tailpools`, `phase15_E2a_cascade`, `phase15_l3_quote_do`, `r6_b4_readcstring`, `r6_r1_placeholder_totality`, `rfc0005_b8_integration_b`, `rfc0005_b8_integration_d`, `rfc0005_b9_integration_b`, `rfc0005_b9_integration_c`, `rfc0005_s11_surface`, `rfc0005_s1b_kinds`, `rfc0005_s5_str`, `rfc0005_s6a_budget`, `rfc0005_s8ad_remainder`, `rfc0005_s8aj_remainder_b`, `rfc0005_s8aj_remainder_c`, `rfc0005_s8aj_remainder`, `rfc0005_s8an_remainder_b`, `rfc0005_s8an_remainder_c`, `rfc0005_s8an_remainder_d`, `rfc0005_s8as_remainder_b`, `rfc0005_s8as_remainder_c`, `rfc0005_s8as_remainder`, `rfc0005_s8au_remainder_b`, `rfc0005_s8au_remainder_c`, `rfc0005_s8aw_remainder`, `rfc0005_s8ax_remainder_b`, `rfc0005_s8ax_remainder_d`, `rfc0005_s8ax_remainder_e`, `rfc0005_s8ax_remainder_f`, `rfc0005_s8ay_remainder_b`, `rfc0005_s8ay_remainder_c`, `rfc0005_s8ay_remainder_d`, `rfc0005_s8ay_remainder`, `rfc0005_s8ba_remainder_b`, `rfc0005_s8bb_captures_b`, `rfc0005_s8bb_captures_c`, `rfc0005_s8bb_captures_d`, `rfc0005_s8bb_captures`, `rfc0005_s8bb_remainder_b`, `rfc0005_s8bb_remainder`, `rfc0005_s8bb_replace_b`, `rfc0005_s8bb_replace_d`, `rfc0005_s8bd_remainder_c`, `rfc0005_s8be_remainder_b`, `rfc0005_s8be_remainder`, `rfc0005_s8bh_remainder`, `rfc0005_s8bi_remainder_b`, `rfc0005_s8bi_remainder_c`, `rfc0005_s8bi_remainder`, `rfc0005_s8bj_replace_lemmas`, `rfc0005_s8bj_walker`, `rfc0005_s8bk_argtiming_checks`, `rfc0005_s8bn_remainder_c`, `rfc0005_s8bo_cells`, `rfc0005_s8bo_replay`, `rfc0005_s8bp_isolation`, `rfc0005_s8bq_remainder_b`, `rfc0005_s8bq_remainder_c`, `rfc0005_s8bt_caps`, `rfc0005_s8bt_libversion`, `rfc0005_s8bt_replace_lemmas_b`, `rfc0005_s8bt_replace_lemmas`, `rfc0005_s8bv_iter_char_count`, `rfc0005_s8bv_iter_char`, `rfc0005_s8ca_stack`, `rfc0005_s8ca_strings_b`, `rfc0005_s8cb_order`, `rfc0005_s8ce_raiseshapes`, `rfc0005_s8cf_point_b`, `rfc0005_s8cf_point`, `rfc0005_s8cr_flips`, `rfc0005_s8cr_intro`, `rfc0005_s8cr_pins`, `rfc0005_s8m_exits_b`, `rfc0005_s8_scope`, `rfc0005_s9_vetoes`, `rfc0005_w1_parity`. The census ceiling 232 -> 139.

Still deferred: ref/ptr (K9d-10) `0016_fieldref`, `rfc0005_s8ao_remainder`,
`rfc0005_s8ax_remainder_c`, `rfc0005_s8bd_remainder_b`,
`rfc0005_s8bh_remainder_b`, `rfc0005_s8bn_remainder_d`,
`rfc0005_s8bn_remainder_e`, `rfc0005_s8bo_nil`, `rfc0005_s8cs_routes_b`,
`rfc0005_s8e_scoping`, plus K9d-7's list; float (K9d-8)
`rfc0005_s8au_remainder`. `rfc0005_s8bh_remainder_c` is red unconverted (its
method-call test returns sxUnknown, feGlobalRouteUnproved) and was left as it
is.

## K9d-8 result (`k9d8`, WIP: the float domain and the first ten suites)

`boundaryOf` gained the float family: `float`/`float64`, `float32`,
`cfloat`/`cdouble`, a float `range` (the values inside it; NaN never is) and a
distinct float through its base. The domain is in the parameter's own width
(`floatDomainValues[F]`), deterministic, at most `seqDomainCap` values, each
value once by its bits (so -0.0 and 0.0 are two values and NaN is one), in
priority order:

- the specials: +-0, +-1, NaN, +-Inf, 0.5, +-the smallest subnormal, +-the
  smallest normal, +-the largest finite, both neighbours of 1;
- the SUT's float AND integer literals (`StringHints.nums`, harvested at macro
  time, at most 32, carried as bits so -0.0 and edge values survive), each in
  the parameter's width with its neighbour either way (`fNextUp`/`fNextDown`:
  a float32 neighbour is one float32 step, not a float64 step rounded back),
  then each negated with its neighbours;
- the tail: +-the largest subnormal, the step above the smallest normal, -0.5,
  the neighbours of -1, +-2, the ties 1.5 and 2.5, 0.1, 3, 10, 100, 1e10,
  1e-10, the step below the largest finite, and 2^e - 1, 2^e with both
  neighbours, 2^e + 1, negated too, for e in 7, 8, 15, 16, 24, 31, 32, 53, 63,
  64 (integer exactness and integer-width conversion edges); a float64 domain
  also holds float32's largest finite and the step above it, float32's
  smallest subnormal and half of it (narrowing overflow and underflow).

Floats are a prefix domain: thinned in an aggregate to the first 64 values
(the specials and the leading literals with their neighbours); a collection's
element core is the first 8 (+-0, +-1, NaN, +-Inf, 0.5) plus the first two
literals with their neighbours. `domHas` compares a float by its bits.

Witness replay is bit-faithful already: `extractLeaf` reads a float through
`Z3_mk_fpa_to_ieee_bv` (`fpBitsToUint64`) and a NaN through the `isNaN`
predicate (the canonical quiet NaN); the self-tests pin a NaN, a -0.0 and a
literal-neighbour witness in both widths, and a planted unsat over a
harvested neighbour, a NaN-only and a -0.0-only hit is refused.

Traps found:

- `cfloat`/`float32` (and `cdouble`/`float`) are one Nim type but two C types,
  as `cuint`/`uint32` in K9d-7b: `sampled(vs)` and a local `seq[T]` built for
  `cfloat` do not compile in C. The float branch appends straight into
  `result.values` with `domPut`.
- A float `range` parameter does not compile in the walker:
  `parseRangeBracket` (`src/nelli/smt/dsl_typebridge.nim`) reads the bounds
  with `intVal` (`Error: node lacks field: intVal`). Its domain is generated
  and self-tested; its pin waits on the walker (not filed: a loud compile
  error, not a disagreement).
- Two suites import the helpers selectively (`from ./s8cu_helpers import
  named`), so a mechanical `symexFind` -> `pinFind` swap does not see
  `pinFind`: `phase15_F5_float_conv`, `phase15_CR3_CR4_CR6_float` (reverted;
  add `pinFind` to the `from` import).

10 suites convert (local c runs, rc 0, every verdict reproduced natively, no
disagreement): `cr9c_intrep`, `phase15_F1_typebridge`,
`phase15_F2_float_literals`, `phase15_F3_float_arith`,
`phase15_F4_float_compare`, `phase15_F6_float_math`,
`phase15_F7_float_extract`, `phase15_F9a_array_float`,
`phase15_F9b_seq_float`, `phase15_F9c_variant_float`. The census ceiling
139 -> 129.

Remaining float candidates (unconverted, unrun): `phase15_F5_float_conv`,
`phase15_CR3_CR4_CR6_float` (the import above), `phase15_C1_canonical_kind`,
`phase15_F5hang_derefwrite`, `phase15_F8_smoke`, `phase15_N0_kindgate_widen`,
`phase15_S10b_strconv`, `phase15_cr9_lowerInExpr`, `phase15_g10_smoke`,
`phase15_g3_type_subst`, `phase15_g4_distinct_sort`,
`phase15_g5_distinct_borrow`, `phase16_A5_float_classify`,
`phase16_R16_2_rangedefect`, `phase16_R16_2b_shortcircuit_conv`,
`r6_n36_raise_degrade_b`, `r6_n36_raise_degrade_c`, `rfc0005_s6b_ops`,
`rfc0005_s8au_remainder`, `rfc0005_s8ba_remainder`,
`snd1_uncertain_taint`, `snd1b_closure_uncertain_axiom`. Ref/ptr parameters
keep `rfc0005_s8k_bounds`, `phase15_rereview_drains` and
`tot1_totality_corpus` in K9d-10.

## The suites by family (at 7f6dca28; K9d-1's 43 are the int family's `phase*` rows without assume)

### int (107)

- `tsymex_0016_cr4_routine_noinit`
- `tsymex_0016_crb_macro_deprecation`
- `tsymex_0016_k10d_drain_checksoff` (exn)
- `tsymex_0016_k10d_removals`
- `tsymex_0016_k4a_guard` (assume, exn)
- `tsymex_0016_w1d1c_cachedprune`
- `tsymex_0016_w1d3_undefined`
- `tsymex_0016_w3z_p1_default`
- `tsymex_0016_w3z_p1_off`
- `tsymex_0016_w3z_r1_noinit_target`
- `tsymex_0016_w3z_r3_default`
- `tsymex_0016_w3z_r3_opaque`
- `tsymex_0016_w3z_r5_render` (exn)
- `tsymex_0016_w4h1b_caseexpr_narrow`
- `tsymex_161_overflow_obligation` (exn)
- `tsymex_163rev_assign_rangedefect` (exn)
- `tsymex_163rev_assign_scope` (exn)
- `tsymex_163rev_concolic_flip_width` (exn)
- `tsymex_163rev_concolic_modes` (exn)
- `tsymex_163rev_concolic_modes_checksoff`
- `tsymex_163rev_degrade_classification` (exn)
- `tsymex_163rev_frontier_default`
- `tsymex_163rev_inert_exclusions` (exn)
- `tsymex_163rev_inert_exclusions_checksoff`
- `tsymex_163rev_transparent_guard` (exn)
- `tsymex_CR2a_expr_catchall`
- `tsymex_a8_radix`
- `tsymex_configdefaults` (exn)
- `tsymex_configdefaults_b` (assume)
- `tsymex_cr22_label_assert_coexist` (exn)
- `tsymex_funcdef_callee` (assume, exn)
- `tsymex_p1_tupleconstr_expr`
- `tsymex_p2a_objconstr_expr` (exn)
- `tsymex_phase14_c4_z3error`
- `tsymex_phase14_frontier_pruning`
- `tsymex_phase14_var_param`
- `tsymex_phase15_A1_bitwise` (assume)
- `tsymex_phase15_A2a_guardcond_pin` (assume)
- `tsymex_phase15_C1_ir`
- `tsymex_phase15_C2b_closure_call`
- `tsymex_phase15_C3_proc_as_value`
- `tsymex_phase15_C5_closure_eq`
- `tsymex_phase15_C6_smoke`
- `tsymex_phase15_CR14_exn_missing` (exn)
- `tsymex_phase15_E2b_raise` (exn)
- `tsymex_phase15_E3_try` (exn)
- `tsymex_phase15_E4_hierarchy` (exn)
- `tsymex_phase15_E4a_userexn` (exn)
- `tsymex_phase15_E6_defect` (exn)
- `tsymex_phase15_E_roundtrip` (exn)
- `tsymex_phase15_G1a_instkey`
- `tsymex_phase15_G1c_instcap`
- `tsymex_phase15_g6_concept_constraint`
- `tsymex_phase15_l1_boundary`
- `tsymex_phase15_l2_untyped_template`
- `tsymex_phase15_r11_unsafecast`
- `tsymex_phase15_r2_new`
- `tsymex_phase15_z3c_classify`
- `tsymex_phase15_z4_walkctx`
- `tsymex_phase16_R16_3_divzero` (exn)
- `tsymex_phase16_R16_4_overflow` (exn)
- `tsymex_phase16_R16_4_overflow_checksoff` (exn)
- `tsymex_phase16_R16_5_overflow_thru_closure` (exn)
- `tsymex_phase16_R16_6_diagnostics_channel` (exn)
- `tsymex_phase16_m5_ifexpr_minmax`
- `tsymex_phase1_arith`
- `tsymex_phase1_assert`
- `tsymex_phase1_bool`
- `tsymex_phase1_let`
- `tsymex_phase2_abstraction`
- `tsymex_phase2_bv_arith`
- `tsymex_phase2_fallback`
- `tsymex_phase2_overflow`
- `tsymex_phase2_overflow_checksoff`
- `tsymex_phase3_inline`
- `tsymex_phase3_recursion`
- `tsymex_phase3_summarization`
- `tsymex_phase6_while`
- `tsymex_r5_bv32_width` (assume, exn)
- `tsymex_r5_neg_bool_conv`
- `tsymex_r5_tuple_return` (assume)
- `tsymex_r6_a4_construct_interactions`
- `tsymex_r6_a6_exported_field_names`
- `tsymex_r6_d2_recursive_budget`
- `tsymex_r6_n16_closure_zerodefault` (assume)
- `tsymex_r6_n20_boundedloop` (assume)
- `tsymex_r6_n39_variant_field_alloc`
- `tsymex_r6_n9_variant_budget`
- `tsymex_r6_r2_zerodefault_result` (assume)
- `tsymex_r8_omitted_field_degrade` (exn)
- `tsymex_rectify_abstraction`
- `tsymex_rectify_generics`
- `tsymex_rfc0005_b9_calldepth`
- `tsymex_rfc0005_s8an_remainder` (assume, exn)
- `tsymex_rfc0005_s8an_remainder_b2` (assume)
- `tsymex_rfc0005_s8av_remainder` (exn)
- `tsymex_rfc0005_s8ax_remainder` (assume)
- `tsymex_rfc0005_s8ax_remainder2` (assume)
- `tsymex_rfc0005_s8ax_remainder_g` (exn)
- `tsymex_rfc0005_s8be_remainder_c` (assume, exn)
- `tsymex_rfc0005_s8bl_seqops`
- `tsymex_rfc0005_s8cb_magics` (exn)
- `tsymex_rfc0005_s8ce_raiseshapes` (exn)
- `tsymex_rfc0005_s8cr_intro`
- `tsymex_rfc0005_s8s_precision_b`
- `tsymex_rfc0005_s8s_precision_f`
- `tsymex_rfc0005_s8s_precision_g`

### object (77)

- `tsymex_0016_cr2_h3_epochpin`
- `tsymex_0016_cr4_enum_layout`
- `tsymex_0016_w3z_r5b_diag` (exn)
- `tsymex_162_range_base_width` (exn)
- `tsymex_163audit_range_elem`
- `tsymex_163audit_wave2`
- `tsymex_163rev_enum_domain`
- `tsymex_163rev_enum_field_witness`
- `tsymex_163rev_enum_ordinal`
- `tsymex_163rev_enum_positions`
- `tsymex_163rev_enum_valueshapes`
- `tsymex_163rev_int_literal_width`
- `tsymex_163rev_nested_clamp`
- `tsymex_163rev_range_bounds`
- `tsymex_163rev_table_elem` (exn)
- `tsymex_CR2c_witnessreader_catchall`
- `tsymex_a7_rune`
- `tsymex_a7_runes_iter`
- `tsymex_augmented_assign`
- `tsymex_h_containers`
- `tsymex_h_stepC_heapidentity`
- `tsymex_m6_probeproto_strproto`
- `tsymex_p2b_refobjconstr_expr`
- `tsymex_phase11_walker` (exn)
- `tsymex_phase14_arm_field_zero_init`
- `tsymex_phase14_disc_promotion`
- `tsymex_phase14_else_arms`
- `tsymex_phase14_multivariant_walker`
- `tsymex_phase14_multivariant_witness`
- `tsymex_phase14_nonenum_disc`
- `tsymex_phase14_symbolic_disc_reassign`
- `tsymex_phase15_A1_arithmetic` (assume)
- `tsymex_phase15_A1_comparison` (assume)
- `tsymex_phase15_C1_canonical_kind` (assume)
- `tsymex_phase15_CR15_enum_ordinal`
- `tsymex_phase15_F9c_variant_float`
- `tsymex_phase15_M1_seq_fixedwidth`
- `tsymex_phase15_N0_kindgate_widen`
- `tsymex_phase15_S10b_strconv` (exn)
- `tsymex_phase15_fieldcontainer`
- `tsymex_phase15_g10_smoke`
- `tsymex_phase15_g4_distinct_sort`
- `tsymex_phase15_g5_distinct_borrow`
- `tsymex_phase15_r9_recursive`
- `tsymex_phase4_nested`
- `tsymex_phase4_tuple`
- `tsymex_phase5_hashset`
- `tsymex_phase5_table`
- `tsymex_phase6_case`
- `tsymex_r1_draingap` (exn)
- `tsymex_r6_a1_variantlit`
- `tsymex_r6_a2_retbind_variant`
- `tsymex_r6_bug2_scopeddecline`
- `tsymex_r6_lows_blockparse`
- `tsymex_r6_n13_reassign_seqarm`
- `tsymex_r6_n27_hof_placeholder`
- `tsymex_r6_n36_raise_degrade_b`
- `tsymex_r6_n36_raise_degrade_c` (exn)
- `tsymex_r6_n49_dottedfield_mutation`
- `tsymex_r6_r1_placeholder_totality`
- `tsymex_rectify_cardinality`
- `tsymex_rectify_mutation`
- `tsymex_rectify_refs`
- `tsymex_rectify_variants`
- `tsymex_rfc0005_s0_exhibit`
- `tsymex_rfc0005_s1c_verdict` (exn)
- `tsymex_rfc0005_s8aa_remainder` (assume, exn)
- `tsymex_rfc0005_s8ac_remainder` (assume, exn)
- `tsymex_rfc0005_s8ac_remainder_b` (assume)
- `tsymex_rfc0005_s8ao_remainder`
- `tsymex_rfc0005_s8bx_extractraise` (exn)
- `tsymex_rfc0005_s8bx_extractraise_b` (exn)
- `tsymex_rfc0005_s8c_resolution` (assume)
- `tsymex_rfc0005_s8d_typeheads`
- `tsymex_rfc0005_s8e_scoping`
- `tsymex_snd1_uncertain_taint`
- `tsymex_tot1_totality_corpus` (exn)

### string (66)

- `tsymex_163rev_inert_argfork` (exn)
- `tsymex_163rev_intoffset_range`
- `tsymex_163rev_scan_counter_range` (exn)
- `tsymex_CR2b_paramtype_catchall`
- `tsymex_a9_casefold`
- `tsymex_discard_raise` (exn)
- `tsymex_phase15_A1_assertarg` (assume)
- `tsymex_phase15_A1_callarg`
- `tsymex_phase15_A1_loopguard` (assume)
- `tsymex_phase15_A1_unary` (assume)
- `tsymex_phase15_A2b_bitwise` (assume)
- `tsymex_phase15_CR11_CR18_splitcap`
- `tsymex_phase15_CR21_parseintraise_arg` (exn)
- `tsymex_phase15_E8_getcurrentexn` (exn)
- `tsymex_phase15_M2_parsebiggestint` (exn)
- `tsymex_phase15_S10a_strconv` (exn)
- `tsymex_phase15_S11_mutation`
- `tsymex_phase15_S1_typebridge`
- `tsymex_phase15_S2_strlit`
- `tsymex_phase15_S3_strindex`
- `tsymex_phase15_S4_strpred`
- `tsymex_phase15_S5_strops`
- `tsymex_phase15_S7a_bytes`
- `tsymex_phase15_S8_concat`
- `tsymex_phase15_S9_caseconv`
- `tsymex_phase15_g8_multi_param`
- `tsymex_phase16_CR1a_bitwise_svint`
- `tsymex_phase16_m3_rfind`
- `tsymex_q1_scanlift`
- `tsymex_q1_sibling_collision`
- `tsymex_r14_case2_degrade`
- `tsymex_r2_scanbound`
- `tsymex_r4_slice_binding`
- `tsymex_r4_strip`
- `tsymex_r5_const_fold` (assume)
- `tsymex_r6_a0_lowhigh`
- `tsymex_r6_b0_scanlift_bound`
- `tsymex_r6_b2_intwidth` (assume, exn)
- `tsymex_r6_b3_scanpair` (assume, exn)
- `tsymex_r6_b6_optionregion` (assume, exn)
- `tsymex_r6_n10_coverage_matrix` (assume, exn)
- `tsymex_r6_n21_pairloop_member` (assume, exn)
- `tsymex_r6_n29_seqlit_sortmismatch`
- `tsymex_r6_n36_raise_degrade` (exn)
- `tsymex_r6_nulwitness` (exn)
- `tsymex_r6_r3_svint_overflow` (assume, exn)
- `tsymex_r6_r5_pairloop_counter` (assume, exn)
- `tsymex_r7_caseexpr` (exn)
- `tsymex_rfc0005_s8ae_remainder`
- `tsymex_rfc0005_s8ag_indexsplit` (exn)
- `tsymex_rfc0005_s8ag_indexsplit_c` (exn)
- `tsymex_rfc0005_s8ai_semantic`
- `tsymex_rfc0005_s8ai_semantic_c`
- `tsymex_rfc0005_s8aq_remainder`
- `tsymex_rfc0005_s8b_substitutions` (exn)
- `tsymex_rfc0005_s8bl_pairloop` (assume, exn)
- `tsymex_rfc0005_s8cb_order` (exn)
- `tsymex_rfc0005_s8o_termination` (assume)
- `tsymex_rfc0005_s8v_termination`
- `tsymex_rfc0005_s8w2_hotfix`
- `tsymex_rfc0005_s8y_budget_decline` (exn)
- `tsymex_snd2_assume` (assume, exn)
- `tsymex_snd3_6_equality_loop`
- `tsymex_snd3_loopdegrade`
- `tsymex_snd4_strindex_oob` (exn)
- `tsymex_uninit_var` (exn)

### regex (63)

- `tsymex_0016_f1_searchdfa_vok` (state/io)
- `tsymex_0016_f2hot_skiplimit` (state/io)
- `tsymex_0016_w3z_p5_shortcircuit_guard` (exn, state/io)
- `tsymex_0016_w4perf_tailpools` (exn, state/io)
- `tsymex_h_verification`
- `tsymex_phase15_A2a_atomize` (assume)
- `tsymex_phase15_E1_ir` (exn)
- `tsymex_phase15_E5_finally` (exn)
- `tsymex_phase15_E7_smoke` (exn)
- `tsymex_phase15_S6b_regex`
- `tsymex_phase15_S7b_smoke`
- `tsymex_phase15_r13_ptr_finally` (exn)
- `tsymex_phase15_rereview_drains`
- `tsymex_r14_continue_guard` (exn)
- `tsymex_r1b_shortcircuit_oob` (exn)
- `tsymex_r6_b5_chained` (exn)
- `tsymex_r6_n43_parity`
- `tsymex_retest_c11_stack`
- `tsymex_retest_c3_bitwise_guard` (exn)
- `tsymex_retest_c6_tuple_chain` (exn)
- `tsymex_retest_char_needle`
- `tsymex_retest_pred_succ`
- `tsymex_rfc0005_s1b_kinds` (exn, state/io)
- `tsymex_rfc0005_s5_str` (exn, state/io)
- `tsymex_rfc0005_s6a_budget` (assume, exn, state/io)
- `tsymex_rfc0005_s6b_ops` (exn, state/io)
- `tsymex_rfc0005_s8as_remainder_c` (assume, exn)
- `tsymex_rfc0005_s8au_remainder_b` (assume, state/io)
- `tsymex_rfc0005_s8au_remainder_c` (assume)
- `tsymex_rfc0005_s8aw_remainder` (exn)
- `tsymex_rfc0005_s8ax_remainder_f` (assume, exn, state/io)
- `tsymex_rfc0005_s8ay_remainder_c` (exn)
- `tsymex_rfc0005_s8ay_remainder_d` (exn)
- `tsymex_rfc0005_s8bb_captures`
- `tsymex_rfc0005_s8bb_captures_b`
- `tsymex_rfc0005_s8bb_captures_c`
- `tsymex_rfc0005_s8bb_captures_d`
- `tsymex_rfc0005_s8bb_remainder` (exn)
- `tsymex_rfc0005_s8bb_remainder_b` (exn)
- `tsymex_rfc0005_s8bb_replace_b` (state/io)
- `tsymex_rfc0005_s8bb_replace_d` (state/io)
- `tsymex_rfc0005_s8bi_remainder` (exn)
- `tsymex_rfc0005_s8bi_remainder_b` (exn)
- `tsymex_rfc0005_s8bi_remainder_c` (exn, state/io)
- `tsymex_rfc0005_s8bj_replace_lemmas` (state/io)
- `tsymex_rfc0005_s8bj_walker` (exn, state/io)
- `tsymex_rfc0005_s8bp_isolation` (state/io)
- `tsymex_rfc0005_s8bq_remainder` (exn)
- `tsymex_rfc0005_s8bq_remainder_b` (exn)
- `tsymex_rfc0005_s8bq_remainder_c` (exn)
- `tsymex_rfc0005_s8bt_caps` (state/io)
- `tsymex_rfc0005_s8bt_libversion` (exn, state/io)
- `tsymex_rfc0005_s8bt_replace_lemmas` (state/io)
- `tsymex_rfc0005_s8bt_replace_lemmas_b` (state/io)
- `tsymex_rfc0005_s8cf_classes` (state/io)
- `tsymex_rfc0005_s8cf_classes_b`
- `tsymex_rfc0005_s8cf_jitlimit`
- `tsymex_rfc0005_s8cf_jitutf` (state/io)
- `tsymex_rfc0005_s8cf_limitgaps` (state/io)
- `tsymex_rfc0005_s8cf_limits`
- `tsymex_rfc0005_s8cf_replace` (state/io)
- `tsymex_rfc0005_s8cf_skipcount` (exn, state/io)
- `tsymex_rfc0005_s8w_remainder` (assume, exn)

### impure (58)

- `tsymex_0016_admir` (assume, exn, state/io)
- `tsymex_0016_cr2_h2_noinit_tail` (state/io)
- `tsymex_0016_fieldhooks` (state/io)
- `tsymex_0016_fieldref` (state/io)
- `tsymex_0016_k7b_unsupported` (exn, state/io)
- `tsymex_0016_k7c_arms` (exn, state/io)
- `tsymex_0016_prc02m_find` (assume, state/io)
- `tsymex_0016_r2b_blocksync` (state/io)
- `tsymex_0016_s8cj_mkunique` (state/io)
- `tsymex_0016_s8cj_runctx` (state/io)
- `tsymex_0016_w3z_r2_candtail` (state/io)
- `tsymex_0016_w3z_r9_tailbudget` (exn, state/io)
- `tsymex_0016_w4perf_demandtail` (exn, state/io)
- `tsymex_0016_wa_runtime_panics` (exn, state/io)
- `tsymex_163_opaque_transparent` (exn, state/io)
- `tsymex_163audit_range_domain` (state/io)
- `tsymex_163rev_degrade_classification_b` (exn, state/io)
- `tsymex_163rev_degrade_classification_c` (exn, state/io)
- `tsymex_163rev_parser_gaps` (exn, state/io)
- `tsymex_163rev_transparent_result` (state/io)
- `tsymex_phase15_A2a_atomicir_audit` (assume, state/io)
- `tsymex_rectify_effects` (state/io)
- `tsymex_rfc0005_b8_integration_b` (exn, state/io)
- `tsymex_rfc0005_b8_integration_d` (state/io)
- `tsymex_rfc0005_b9_integration_b` (state/io)
- `tsymex_rfc0005_b9_integration_c` (state/io)
- `tsymex_rfc0005_s11_surface` (exn, state/io)
- `tsymex_rfc0005_s4_alloc` (state/io)
- `tsymex_rfc0005_s8_scope` (exn, state/io)
- `tsymex_rfc0005_s8an_remainder_c` (assume, exn, state/io)
- `tsymex_rfc0005_s8an_remainder_d` (state/io)
- `tsymex_rfc0005_s8as_remainder` (state/io)
- `tsymex_rfc0005_s8as_remainder_b` (assume, exn, state/io)
- `tsymex_rfc0005_s8au_remainder` (assume, state/io)
- `tsymex_rfc0005_s8ax_remainder_b` (exn, state/io)
- `tsymex_rfc0005_s8ax_remainder_d` (assume, state/io)
- `tsymex_rfc0005_s8az_remainder` (state/io)
- `tsymex_rfc0005_s8ba_remainder` (assume, state/io)
- `tsymex_rfc0005_s8ba_remainder_b` (exn, state/io)
- `tsymex_rfc0005_s8ba_remainder_c` (state/io)
- `tsymex_rfc0005_s8bd_remainder_b` (state/io)
- `tsymex_rfc0005_s8bd_remainder_c` (state/io)
- `tsymex_rfc0005_s8be_remainder` (assume, exn, state/io)
- `tsymex_rfc0005_s8be_remainder_b` (assume, state/io)
- `tsymex_rfc0005_s8bh_remainder_c` (state/io)
- `tsymex_rfc0005_s8bn_remainder_c` (exn, state/io)
- `tsymex_rfc0005_s8bn_remainder_d` (exn, state/io)
- `tsymex_rfc0005_s8bo_replay` (assume, state/io)
- `tsymex_rfc0005_s8ca_stack` (state/io)
- `tsymex_rfc0005_s8cb_cells` (exn, state/io)
- `tsymex_rfc0005_s8cb_replay` (assume, state/io)
- `tsymex_rfc0005_s8cr_flips` (exn, state/io)
- `tsymex_rfc0005_s8cr_pins` (exn, state/io)
- `tsymex_rfc0005_s8cs_routes_b` (state/io)
- `tsymex_rfc0005_s8ct_b19` (exn, state/io)
- `tsymex_rfc0005_s8k_bounds` (exn, state/io)
- `tsymex_rfc0005_s8m_exits_b` (exn, state/io)
- `tsymex_rfc0005_w1_parity` (exn, state/io)

### seq (37)

- `tsymex_163audit_w9` (exn)
- `tsymex_163rev_seqelem_promoted_int` (assume)
- `tsymex_a6_symlen_hof`
- `tsymex_g1a_mode` (exn)
- `tsymex_phase15_A1_boolean`
- `tsymex_phase15_C2_staticparams`
- `tsymex_phase15_C4_hof`
- `tsymex_phase15_F9a_array_float`
- `tsymex_phase15_F9b_seq_float`
- `tsymex_phase15_g7_static_param`
- `tsymex_phase15_l3_quote_do`
- `tsymex_phase16_CR1b_tail_local`
- `tsymex_phase16_D1a_defect_routeraise` (exn)
- `tsymex_phase16_m4_str_add_ampeq`
- `tsymex_phase4_array`
- `tsymex_phase4_oob`
- `tsymex_phase5_seq`
- `tsymex_phase6_break`
- `tsymex_phase6_for`
- `tsymex_r4_seq_slice`
- `tsymex_r5_discard` (exn)
- `tsymex_r6_b1_stringbacked`
- `tsymex_r6_b4_readcstring` (assume, exn)
- `tsymex_r6_b7r2_pathscope` (assume, exn)
- `tsymex_r6_b7r_bytescan` (assume, exn)
- `tsymex_r6_lows_collectors` (exn)
- `tsymex_r6_n28_shadow_collision` (assume, exn)
- `tsymex_r6_n31_block_counter` (exn)
- `tsymex_r6_n37_raise_residue` (exn)
- `tsymex_r6_r4_collector_scoping` (exn)
- `tsymex_rectify_nested_arrays`
- `tsymex_rfc0005_s8aa_remainder_checksoff` (exn)
- `tsymex_rfc0005_s8q_termination` (assume, exn)
- `tsymex_rfc0005_s8t_termination` (assume, exn)
- `tsymex_rfc0005_s8w_remainder_b` (exn)
- `tsymex_rfc0005_s8w_remainder_b_checksoff` (exn)
- `tsymex_rfc0005_s9_vetoes` (exn)

### ref (22)

- `tsymex_0016_wa_runtime`
- `tsymex_163rev_armfield_write`
- `tsymex_163rev_assign_sites` (assume, exn)
- `tsymex_163rev_variant_armfield`
- `tsymex_a2_refvariant_fields`
- `tsymex_phase15_CR1_CR5_closure_heap`
- `tsymex_phase15_R1a_ir`
- `tsymex_phase15_r11b_smoke`
- `tsymex_phase15_r12_bumps`
- `tsymex_phase15_r1_refsort`
- `tsymex_phase15_r1b_callheap`
- `tsymex_phase15_r3_deref_read`
- `tsymex_phase15_r4_deref_write`
- `tsymex_phase15_r5_nil`
- `tsymex_phase15_r6_refobj`
- `tsymex_phase15_r7_alias_chain`
- `tsymex_phase15_r8_ptr`
- `tsymex_phase16_D1c_shortcircuit`
- `tsymex_r6_heap_raise_totality` (exn)
- `tsymex_r6_n42_deref_taint`
- `tsymex_rfc0005_s3_monotonicity` (exn)
- `tsymex_rfc0005_s8bf_alias`

### float (17)

- `tsymex_cr9c_intrep`
- `tsymex_phase15_CR3_CR4_CR6_float` (exn)
- `tsymex_phase15_F1_typebridge`
- `tsymex_phase15_F2_float_literals`
- `tsymex_phase15_F3_float_arith`
- `tsymex_phase15_F4_float_compare`
- `tsymex_phase15_F5_float_conv` (exn)
- `tsymex_phase15_F5hang_derefwrite` (exn)
- `tsymex_phase15_F6_float_math`
- `tsymex_phase15_F7_float_extract`
- `tsymex_phase15_F8_smoke`
- `tsymex_phase15_cr9_lowerInExpr` (exn)
- `tsymex_phase15_g3_type_subst`
- `tsymex_phase16_A5_float_classify`
- `tsymex_phase16_R16_2_rangedefect` (exn)
- `tsymex_phase16_R16_2b_shortcircuit_conv` (exn)
- `tsymex_snd1b_closure_uncertain_axiom`

### unresolved (15)

- `tsymex_0016_cr1_sharedenv`
- `tsymex_0016_d1_narrow_opaque`
- `tsymex_0016_k9cg_unbacked`
- `tsymex_rfc0005_s8an_remainder_b` (assume)
- `tsymex_rfc0005_s8ax_remainder_c` (assume)
- `tsymex_rfc0005_s8ax_remainder_e` (assume, exn)
- `tsymex_rfc0005_s8bh_remainder` (exn)
- `tsymex_rfc0005_s8bh_remainder_b`
- `tsymex_rfc0005_s8bk_argtiming_checks`
- `tsymex_rfc0005_s8bn_remainder_e`
- `tsymex_rfc0005_s8bo_cells` (assume, exn)
- `tsymex_rfc0005_s8bo_nil` (assume)
- `tsymex_rfc0005_s8bv_iter_char`
- `tsymex_rfc0005_s8bv_iter_char_count`
- `tsymex_rfc0005_s8ca_strings_b` (exn)

### meta (12)

- `tsymex_0016_k5a_segment` (exn)
- `tsymex_phase15_E2a_cascade` (exn)
- `tsymex_phase15_r10_budget`
- `tsymex_rfc0005_s8ad_remainder` (assume, exn)
- `tsymex_rfc0005_s8aj_remainder` (assume)
- `tsymex_rfc0005_s8aj_remainder_b`
- `tsymex_rfc0005_s8aj_remainder_c` (assume, exn)
- `tsymex_rfc0005_s8ay_remainder`
- `tsymex_rfc0005_s8ay_remainder_b`
- `tsymex_rfc0005_s8bm_stability`
- `tsymex_rfc0005_s8cf_point` (state/io)
- `tsymex_rfc0005_s8cf_point_b` (state/io)

### no-direct-call (6)

- `tsymex_0016_d3b_walklog` (exn, state/io)
- `tsymex_0016_k8a_gen` (state/io)
- `tsymex_rfc0005_s1_lattice` (state/io)
- `tsymex_rfc0005_s7_closure` (exn, state/io)
- `tsymex_rfc0005_s8bk_argtiming`
- `tsymex_rfc0005_s8bk_argtiming_addr`

### nullary (4)

- `tsymex_phase15_r13_closure_ref`
- `tsymex_phase15_r8b_varref`
- `tsymex_phase16_CR1c_internal_fault`
- `tsymex_retest_defect_net`


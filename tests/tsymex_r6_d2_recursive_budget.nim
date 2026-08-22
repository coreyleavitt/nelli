## Round-6 review D2 — `isVariantConstructSym` field-allocation budget made
## RECURSIVE (N9 companion, confirmed Medium resource-budget undercount).
##
## Finding: N9 (round-6 review remediation) added
## `maxVariantConstructorFieldAllocs` (default 64) to bound
## `isVariantConstructSym`'s per-fork field-allocation cost, computed as
## `vcsTagSet.len * (sum of arm.fieldTypes.len across every declared arm)`
## — a FLAT field COUNT. But `allocateSym` (`runtime.nim`) — which is what
## actually performs the allocation for each of those fields — RECURSES:
## an `itArray` field allocates `size` copies of its element (`for i in 0
## ..< ty.size`), an `itTuple` field allocates every one of its own fields,
## an `itVariant`/`itMultiVariant` field allocates every ONE of ITS OWN
## arms' fields, compounding when nested. N9's flat count treats a
## composite field exactly like a scalar one — `array[1_000_000, int]`
## counts as `1`, not 1,000,000 — so a shape whose FLAT field count clears
## the budget can still perform an amount of real allocation work the
## budget was supposed to prevent.
##
## Fix: `allocCostOf` (`smt/types.nim`) mirrors `allocateSym`'s own
## recursive dispatch to compute the true leaf-allocation cost of a type
## WITHOUT allocating anything, and `isVariantConstructSym`'s budget check
## now sums `allocCostOf(ft)` over every arm field instead of a flat `1`
## per field. `itSeq`/`itTable`/`itSet` stay O(1) in this cost function,
## mirroring `allocateSeqDataRaw`'s single-array-const allocation (it never
## loops per element regardless of the seq's element type) — the
## recursion is a real amplifier ONLY for `itArray`/`itTuple`/
## `itVariant`/`itMultiVariant`/`itDistinct` fields.
##
## Bumps `symexWalkerVersion` 98->99: verdict-surface change — a
## composite-arm-field shape whose FLAT field count previously cleared the
## budget (and so constructed, producing a real verdict) may now exceed
## the RECURSIVE leaf-allocation cost and classify `beBudgetExhausted`
## instead. The default budget value (64) is unchanged; only its unit
## changed (fields -> leaf allocations), per the fix-slice's own doc
## comment (`symexWalkerVersion`, `canonicalize.nim`).
##
## Honesty note on RED construction (mirrors N9's own honesty note): this
## is a resource-exhaustion/perf finding, not a soundness bug — pre-fix,
## test D2-1's shape below does not crash or hang, it PROCEEDS to real
## (unbudgeted) allocation work and returns a genuine `sxSat` verdict.
## What is observable and countable is the verdict-KIND flip: pre-fix
## `sxSat` (confirmed by stashing this slice's `runtime.nim`/`types.nim`/
## `canonicalize.nim` changes and re-running this file in isolation before
## writing this pin — see the fix-slice summary for the exact stash
## commands and output), post-fix `beBudgetExhausted`. Test D2-4 exercises
## the SAME flip through a deeper nesting path (array nested inside a
## tuple, inside a variant arm field) and was stash-verified the same way.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

# ---------------------------------------------------------------------------
# D2-1 (RED pin): composite (array-typed) arm fields. FLAT field count
# clears the default budget (2 forks x 2 flat fields = 4, far under 64) —
# the pre-fix check passes and construction proceeds. But each field is
# `array[40, int]`, costing 40 leaf allocations apiece under the recursive
# scheme: 2 forks x (40 + 40) = 160 > 64 — the post-fix check declines.
# Kept small (40, not 1_000_000) so the pre-fix RED run stays fast — the
# amplification is proven by the ARITHMETIC (2x40x2=160), not by making
# the pre-fix run itself slow.
# ---------------------------------------------------------------------------

type
  D2CompTag = enum d2cA, d2cB
  CompositeWideObj = object
    tag: int
    case kind: D2CompTag
    of d2cA: bigArrA: array[40, int]
    of d2cB: bigArrB: array[40, int]

proc sutCompositeArmBudget(b: byte, n: int) =
  let op = if b == 1'u8: d2cA else: d2cB
  let p = CompositeWideObj(kind: op, tag: n)
  if p.tag == 5:
    symexTarget("d2_composite_budget_reached")

# ---------------------------------------------------------------------------
# D2-2: scalar-fields companion at the SAME flat field count as D2-1 (2
# forks x 2 flat fields = 4). Recursive cost of a scalar `int` field is `1`
# — identical to the old flat count — so this shape's verdict must be
# UNCHANGED by the fix (no over-decline of an ordinary scalar-fielded
# variant construction).
# ---------------------------------------------------------------------------

type
  D2ScalarTag = enum d2sA, d2sB
  ScalarWideObj = object
    tag: int
    case kind: D2ScalarTag
    of d2sA: fieldA: int
    of d2sB: fieldB: int

proc sutScalarArmBudget(b: byte, n: int) =
  let op = if b == 1'u8: d2sA else: d2sB
  let p = ScalarWideObj(kind: op, tag: n)
  if p.tag == 5:
    symexTarget("d2_scalar_budget_reached")

# ---------------------------------------------------------------------------
# D2-3: itSeq-fielded arms stay CHEAP (O(1) per field, mirroring
# `allocateSeqDataRaw`'s single-array-const allocation — it never loops per
# element). 4 declared arms x 2 seq[int] fields each: recursive cost per
# field is `2` (length var + data array var), so total = 4 forks x (2
# fields x 2 cost) = 4 x 4 = 16 leaf allocations per arm's contribution,
# summed across 4 arms x 4 forks = 64 — landing EXACTLY at the default
# budget (the check is strict `>`, so this still constructs). Proves a
# reasonably wide, seq-fielded variant is NOT mistaken for an
# array-amplified one.
# ---------------------------------------------------------------------------

type
  D2SeqTag = enum d2seqA, d2seqB, d2seqC, d2seqD
  SeqFieldedObj = object
    tag: int
    case kind: D2SeqTag
    of d2seqA: sa1, sa2: seq[int]
    of d2seqB: sb1, sb2: seq[int]
    of d2seqC: sc1, sc2: seq[int]
    of d2seqD: sd1, sd2: seq[int]

proc sutSeqArmBudget(b: byte, n: int) =
  let op = if b == 1'u8: d2seqA else: d2seqB
  let p = SeqFieldedObj(kind: op, tag: n)
  if p.tag == 5:
    symexTarget("d2_seq_budget_reached")

# ---------------------------------------------------------------------------
# D2-4 (RED pin, deeper nesting): a nested-TUPLE arm field exercising two
# levels of recursion (variant field -> tuple field -> array element). 2
# forks x 1 flat field = 2 (clears the old flat budget trivially). The
# field's type is `tuple[inner: array[40, int], extra: int]`: recursive
# cost = 40 (array) + 1 (extra) = 41 per field, x 2 forks = 82 > 64 —
# declines post-fix. Stash-verified pre-fix `sxSat` the same way as D2-1
# (see the fix-slice summary).
# ---------------------------------------------------------------------------

type
  D2NestTag = enum d2nA, d2nB
  NestedTupleObj = object
    tag: int
    case kind: D2NestTag
    of d2nA: nfA: tuple[inner: array[40, int], extra: int]
    of d2nB: nfB: tuple[inner: array[40, int], extra: int]

proc sutNestedTupleArmBudget(b: byte, n: int) =
  let op = if b == 1'u8: d2nA else: d2nB
  let p = NestedTupleObj(kind: op, tag: n)
  if p.tag == 5:
    symexTarget("d2_nested_tuple_budget_reached")

# ---------------------------------------------------------------------------
# D2-5: budget-override companion. The SAME shape as D2-1 (recursive cost
# 160, over the default 64) still constructs when
# `maxVariantConstructorFieldAllocs` is raised past 160 via the settings
# override surface (`withSymexSettings`, the same knob
# `tsymex_phase15_CR11_CR18_splitcap.nim` uses for `maxSplitParts`) —
# proving the recursive cost feeds the SAME configurable ceiling, not a
# hardcoded one.
# ---------------------------------------------------------------------------

const d2WiderBudget = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxVariantConstructorFieldAllocs = 200

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex round-6 D2 — recursive field-allocation budget (composite arm fields)":

  test "D2-1: array-typed arm fields (flat=4 clears old budget, recursive=160 exceeds it) declines":
    let res = symexFind(sutCompositeArmBudget, tLabel("d2_composite_budget_reached"))
    check res.status == sxUnknown
    check res.status != sxSat
    var hasClassified = false
    var msg = ""
    for e in res.errors:
      if e.kind == beBudgetExhausted and e.severity == sevError:
        hasClassified = true
        msg = e.msg
    check hasClassified
    check "tsymex_r6_d2_recursive_budget.nim" in msg
    check "CompositeWideObj" in msg
    check "maxVariantConstructorFieldAllocs" in msg

suite "symex round-6 D2 — scalar-fields companion keeps the exact prior verdict":

  test "D2-2: scalar int arm fields at the same flat count as D2-1 still construct":
    let res = symexFind(sutScalarArmBudget, tLabel("d2_scalar_budget_reached"))
    check res.status == sxSat
    check res.witness[1] == 5

suite "symex round-6 D2 — itSeq-fielded arms stay O(1), no over-decline":

  test "D2-3: seq[int]-fielded arms (recursive cost lands exactly at the default budget) still construct":
    let res = symexFind(sutSeqArmBudget, tLabel("d2_seq_budget_reached"))
    check res.status == sxSat
    check res.witness[1] == 5

suite "symex round-6 D2 — nested-tuple arm field exercises two-level recursion":

  test "D2-4: array nested inside a tuple inside an arm field (flat=2, recursive=82) declines":
    let res = symexFind(sutNestedTupleArmBudget, tLabel("d2_nested_tuple_budget_reached"))
    check res.status == sxUnknown
    check res.status != sxSat
    var hasClassified = false
    for e in res.errors:
      if e.kind == beBudgetExhausted and e.severity == sevError:
        hasClassified = true
    check hasClassified

suite "symex round-6 D2 — budget override still lifts the recursive ceiling":

  test "D2-5: raising maxVariantConstructorFieldAllocs past 160 lets the D2-1 shape construct":
    let res = symexFind(sutCompositeArmBudget, tLabel("d2_composite_budget_reached"), d2WiderBudget)
    check res.status == sxSat
    check res.witness[1] == 5

suite "symex round-6 D2 — cache-key wiring (unchanged field, still participates)":

  test "maxVariantConstructorFieldAllocs still participates in the settings cache key":
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.budget.maxVariantConstructorFieldAllocs = s0.budget.maxVariantConstructorFieldAllocs + 1
    check canonicalize(s0) != canonicalize(s1)

suite "symex round-6 D2 — walker version pin":

  test "walker version floor >= 99 (recursive variant-constructor field-allocation budget)":
    check parseInt(symexWalkerVersion) >= 99

## N39 (round-6 fix round 5) — closing a mis-scoped safety certification in
## the raw-raise CLASS (High): `allocateSym`'s five `category-2` markers
## (`runtime.nim` :1680/:1694/:1721/:2005/:2019 — the `itUninterp`
## `__ownership:`/`__unsupported:`/`__unsupported_witness:` raises and the
## `itTable`/`itSet` unsupported-shape raises) claimed "reached only during
## pre-walk parameter allocation, zero intervening `walkBlock` frames" —
## true for every PARAMETER-allocation caller, but FALSE for two WALK-TIME
## callers N36's own spot-check missed: `isVariantConstructSym` (fork-per-
## tag symbolic-discriminant variant CONSTRUCTION, allocates EVERY declared
## arm's fields in EVERY fork) and `lowerVariantLit` (variant LITERAL
## construction, allocates every INACTIVE arm's fields fresh).
## `classifyFieldType` (dsl_typebridge.nim) legitimately classifies a
## variant ARM field as one of these five unsupported shapes —
## `scopedDeclineFieldTy`'s Bug #2 scoped decline only special-cases
## `itSeq`, so nothing intercepts these five kinds before they reach
## `arm.fieldTypes`.
##
## ---- Probe outcome (stash method, both routes) --------------------------
## Route (b), `isVariantConstructSym` (symbolic-discriminant construction —
## `let k = if b == 1'u8: vkGood else: vkBad; let v = T(kind: k)`, no
## arm-specific field set, matching Nim's own non-constant-disc constructor
## restriction): CONFIRMED REACHABLE and CONFIRMED to reproduce the exact
## ADR-0023/SND-3 C-backend goto-exception hazard — a block-nested reach
## PRE-FIX gave `sxUnsat` with ZERO errors (WRONG, silently lost); the
## IDENTICAL shape without the block gave honest `sxUnknown`. Confirmed for
## BOTH the `itTable` and `itSet` unsupported shapes.
##
## Route (a), `lowerVariantLit` (variant LITERAL — the unsupported field
## lives on an arm NOT selected by the literal's tag, e.g.
## `T(kind: vkGood, x: a)` where `vkBad`'s field is the unsupported one):
## probed across EIGHT distinct nesting shapes (bare `for`+`block`, no
## block, a `while` loop, two nested `block`s, a `block` with the target
## AFTER more statements, and — matching ADR-0023's own tracer-bullet
## structure — the construction embedded directly inside a `while` GUARD
## expression) and never reproduced the loss; every shape already yielded
## honest `sxUnknown` pre-fix. Per the class description's own framing
## ("regardless of whether the probe confirms a live wrong verdict — the
## unguarded walk-time call is a certification error either way"), this
## call site is fixed anyway (same as N37's own precedent for
## un-independently-pinnable sites: the MECHANISM — a raw raise reachable
## from inside `lower()` while a loop's live `seq[Path]` may be on the
## stack — is identical regardless of whether a compiler/inlining quirk
## happens to keep it from manifesting in every shape tried).
##
## ---- Fix design -----------------------------------------------------------
## GUARD-BEFORE-CALL at both sites (preferred per the class description),
## NOT catch-after: the field's `IRType` is already fully available at both
## call sites (no `NimNode`/re-classification needed), via a new
## `unallocatableFieldIssue` predicate (`types.nim`) that mirrors
## `allocateSym`'s own dispatch kind-for-kind (same "update both together"
## discipline as the pre-existing `allocCostOf`), recursing through every
## composite kind `allocateSym` itself recurses through so an arbitrarily
## nested unsupported leaf is caught, not just a bare top-level field.
## `isVariantConstructSym` degrades via its own existing
## `w.sawUnknown`/`walkDegradeErrors`/`forkPathTainted` idiom, hoisted above
## the fork loops alongside its two pre-existing budget checks (every fork
## allocates every arm regardless of tag, so there is no finer-grained
## per-tag distinction to make anyway). `lowerVariantLit` degrades via the
## `loweringDegradeErrors`/`loweringDidDegrade` sink ADR-0023 established
## for exactly this "`lower()`-reachable, no `Path`/`WalkCtx` in scope"
## shape, substituting a bare fresh `svBool` for the declined field — sound
## because an INACTIVE arm's field is reachable ONLY through
## `isVariantField`'s out-of-arm `FieldDefect` fork (this function's own
## pre-existing doc comment already establishes this), so no live SAT path
## ever reads its value or inspects its kind (the same tolerance `tyOf`'s
## own "diagnostics only" `svVariant` arm already relies on).
##
## Walker bump 102->103: `isVariantConstructSym`'s half is a genuine
## verdict-surface change (empirically confirmed false `sxUnsat` -> honest
## `sxUnknown`), the same bar N36/N37 set. `lowerVariantLit`'s half ships in
## the same commit as certification-accuracy hardening (mechanism argument,
## no isolable RED->GREEN flip observed). See `symexWalkerVersion`'s own
## doc comment (`canonicalize.nim`) for the full writeup.
import std/[unittest, strutils, tables, sets]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# Shared SUT types
# =============================================================================

type
  VKind = enum vkGood, vkBad

  VBadTable = object
    ## `vkBad`'s field classifies to `itTable` with an unsupported value
    ## type (only `Table[string, int]` is backed by `allocateSym`).
    case kind: VKind
    of vkGood: x: int
    of vkBad: t: Table[string, string]

  VBadSet = object
    ## `vkBad`'s field classifies to `itSet` with an unsupported element
    ## type (only `HashSet[int]`/BV[64] is backed by `allocateSym`).
    case kind: VKind
    of vkGood: x: int
    of vkBad: s: HashSet[string]

  VGood = object
    ## Companion: every arm is fully backed (plain `int` fields) — proves
    ## the N39 guard does not touch ordinary, allocatable variant
    ## construction.
    case kind: VKind
    of vkGood: gx: int
    of vkBad: gy: int

  VSeqArm = object
    ## Companion: Bug #2's PRE-EXISTING scoped-decline path (an arm field
    ## whose `seq[T]` element type is structurally unbacked, e.g.
    ## `seq[(string, string)]`) — proves the N39 guard's `itTuple`/`itArray`/
    ## composite recursion does not re-flag a shape `scopedDeclineFieldTy`
    ## already handles upstream at classify time.
    case kind: VKind
    of vkGood: sx: int
    of vkBad: sq: seq[(string, string)]

# =============================================================================
# 1. isVariantConstructSym (route b, symbolic discriminant) — CONFIRMED
#    false-sxUnsat-under-block-nesting, fixed.
# =============================================================================

proc n39SymTableBlock(b: byte) =
  let k = if b == 1'u8: vkGood else: vkBad
  for i in 0 ..< 1:
    block:
      let v = VBadTable(kind: k)
      if v.kind == vkGood:
        symexTarget("n39_sym_table_block")

proc n39SymTableNoBlock(b: byte) =
  let k = if b == 1'u8: vkGood else: vkBad
  let v = VBadTable(kind: k)
  if v.kind == vkGood:
    symexTarget("n39_sym_table_noblock")

proc n39SymSetBlock(b: byte) =
  let k = if b == 1'u8: vkGood else: vkBad
  for i in 0 ..< 1:
    block:
      let v = VBadSet(kind: k)
      if v.kind == vkGood:
        symexTarget("n39_sym_set_block")

suite "symex N39 -- isVariantConstructSym: confirmed false-sxUnsat, fixed":

  test "N39-1: block-nested symbolic-disc construction reaching an unsupported Table arm field -- honest sxUnknown, never a false sxUnsat":
    let r = symexFind(n39SymTableBlock, tLabel("n39_sym_table_block"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seUnsupportedTableValType and
         "variant constructor field allocation unmodeled" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

  test "N39-1-noblock: same shape without the block -- already honest, unaffected by this slice's fix":
    let r = symexFind(n39SymTableNoBlock, tLabel("n39_sym_table_noblock"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seUnsupportedTableValType and
         "variant constructor field allocation unmodeled" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

  test "N39-2: block-nested symbolic-disc construction reaching an unsupported HashSet arm field -- honest sxUnknown, never a false sxUnsat":
    let r = symexFind(n39SymSetBlock, tLabel("n39_sym_set_block"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seUnsupportedSetCharInterop and
         "variant constructor field allocation unmodeled" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

# =============================================================================
# 2. lowerVariantLit (route a, literal construction, inactive arm) --
#    probed and never lost pre-fix; guarded anyway (certification accuracy).
# =============================================================================

proc n39LitTableBlock(a: int) =
  for i in 0 ..< 1:
    block:
      let v = VBadTable(kind: vkGood, x: a)
      if v.kind == vkGood and v.x == 42:
        symexTarget("n39_lit_table_block")

proc n39LitTableNoBlock(a: int) =
  let v = VBadTable(kind: vkGood, x: a)
  if v.kind == vkGood and v.x == 42:
    symexTarget("n39_lit_table_noblock")

proc n39LitSetBlock(a: int) =
  for i in 0 ..< 1:
    block:
      let v = VBadSet(kind: vkGood, x: a)
      if v.kind == vkGood and v.x == 42:
        symexTarget("n39_lit_set_block")

suite "symex N39 -- lowerVariantLit: probed clean pre-fix, guarded for certification accuracy":

  test "N39-3: block-nested variant LITERAL, unsupported Table field on the INACTIVE arm -- honest sxUnknown, both pre- and post-fix":
    let r = symexFind(n39LitTableBlock, tLabel("n39_lit_table_block"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seUnsupportedTableValType and
         "variant literal inactive-arm field" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

  test "N39-3-noblock: same shape without the block -- unaffected":
    let r = symexFind(n39LitTableNoBlock, tLabel("n39_lit_table_noblock"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seUnsupportedTableValType and
         "variant literal inactive-arm field" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

  test "N39-4: block-nested variant LITERAL, unsupported HashSet field on the INACTIVE arm -- honest sxUnknown":
    let r = symexFind(n39LitSetBlock, tLabel("n39_lit_set_block"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seUnsupportedSetCharInterop and
         "variant literal inactive-arm field" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

# =============================================================================
# 3. Companion -- normal (fully-backed) variant construction is unaffected,
#    both construction routes.
# =============================================================================

proc n39GoodLitSat(a: int) =
  let v = VGood(kind: vkGood, gx: a)
  if v.kind == vkGood and v.gx == 777:
    symexTarget("n39_good_lit_sat")

proc n39GoodSymSat(b: byte, n: int) =
  let k = if b == 1'u8: vkGood else: vkBad
  let v = VGood(kind: k)
  if v.kind == vkGood and n == 5:
    symexTarget("n39_good_sym_sat")

suite "symex N39 -- companion: fully-backed variant construction unaffected":

  test "N39-5: a variant LITERAL with every arm fully backed still reaches sxSat":
    let r = symexFind(n39GoodLitSat, tLabel("n39_good_lit_sat"))
    check r.status == sxSat

  test "N39-6: a symbolic-disc construction with every arm fully backed still reaches sxSat":
    let r = symexFind(n39GoodSymSat, tLabel("n39_good_sym_sat"))
    check r.status == sxSat

# =============================================================================
# 4. Companion -- Bug #2's pre-existing seq-field scoped-decline path is
#    unaffected by the N39 guard's composite recursion.
# =============================================================================

proc n39SeqArmLit(a: int) =
  let v = VSeqArm(kind: vkGood, sx: a)
  if v.kind == vkGood and v.sx == 42:
    symexTarget("n39_seqarm_lit")

suite "symex N39 -- companion: Bug #2 seq-field scoped-decline path unaffected":

  test "N39-7: a variant literal whose INACTIVE arm carries an unbacked-seq field (Bug #2's own scoped-decline shape) still reaches sxSat -- N39's guard does not double-decline it":
    let r = symexFind(n39SeqArmLit, tLabel("n39_seqarm_lit"))
    check r.status == sxSat

# =============================================================================
# Version pin
# =============================================================================

suite "symex N39 -- walker version pin":

  test "walker version floor >= 103 (N39: variant arm-field allocation guarded against unclassifiable types)":
    check parseInt(symexWalkerVersion) >= 103

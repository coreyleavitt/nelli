## Round-6 lows slice (fix round 9) -- two Low-severity review findings that
## share one root cause in `parseStmtInner`'s block arm
## (`src/nelli/smt/dsl_parser.nim`).
##
## N34 (Low, capability): a single-statement `block:` body is mis-itemized.
## The combined `of nnkStmtList, nnkStmtListExpr, nnkBlockStmt:` arm binds
## `inner = n[1]` for a block and then does `for c in inner`, assuming
## `inner` is always `nnkStmtList`-shaped. It is not: the typed AST does not
## always wrap a lone block-body statement in `nnkStmtList` -- a `block:`
## with exactly one statement can typecheck directly to that bare statement
## node. Iterating such a node with `for c in inner` walks the STATEMENT'S
## OWN CHILDREN (e.g. an `nnkAsgn`'s LHS/RHS) as if they were sibling
## top-level statements, each of which then lands the unrecognised-node-kind
## catch-all (`mkUnsupported("statement kind ... not in supported
## fragment")`) -- a consistent mis-parse/decline for every one-statement
## block, regardless of what that one statement is. A two-statement block
## body is never affected (multiple statements can only ever arrive already
## wrapped in a real `nnkStmtList`), which is what makes the asymmetry
## between the two pins below possible.
##
## Fixed by itemizing block/stmt-list bodies through a shared
## `stmtListItems` helper that treats a `nnkStmtList`/`nnkStmtListExpr` node
## as its children and any other node kind as a SINGLE statement -- applied
## uniformly so the same hazard can't resurface if another arm grows a
## similar body-itemization need later.
##
## N38 (Low): a block-wrapped case-object discriminator reassignment
## (`block: v.kind = dkB`) was landing a spurious UNCLASSIFIED `sxUnknown`
## even for a fully-backed arm, with zero degrade machinery involved --
## exactly the N34 mis-parse's signature (the reassignment is the block's
## lone statement, so its `nnkAsgn` LHS/RHS get walked as two bogus
## top-level statements instead of recognised as one discriminator
## reassignment). Resolves via the N34 fix alone; no dedicated production
## change. See tests/tsymex_r6_n13_reassign_seqarm.nim for the unwrapped
## (non-block) sibling shape this mirrors.
##
## VERDICT-AFFECTING: N34's fix can flip a spurious `sxUnknown` decline
## into a genuine `sxSat`/`sxUnsat` proof for any single-statement `block:`
## body (N38 is one concrete instance). `symexWalkerVersion` bumps 106->107.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# N34 -- single-statement `block:` body mis-parse, vs. a two-statement
# companion that already works. Both SUTs assign the SAME value to `v`
# inside a `block:` and then gate a target on observing that value --
# the only difference is whether the block body carries one statement or
# two (the second being an inert `discard`).
# =============================================================================

proc sutN34SingleStmtBlock(v: var int) =
  block:
    v = 42
  if v == 42:
    symexTarget("n34_single_stmt_block_v42")

proc sutN34TwoStmtBlock(v: var int) =
  block:
    v = 42
    discard 0
  if v == 42:
    symexTarget("n34_two_stmt_block_v42")

suite "symex round-6 N34 -- single-statement block:body mis-itemization":

  test "N34-1: single-statement block reassignment is visible post-block -> sxSat " &
       "(pre-fix RED: block's lone `v = 42` mis-itemized into two bogus top-level " &
       "statements, decline to sxUnknown)":
    let r = symexFind(sutN34SingleStmtBlock, tLabel("n34_single_stmt_block_v42"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

  test "N34-2 (companion, proves the asymmetry): the two-statement block version " &
       "already reaches its target -> sxSat, both before and after the fix":
    let r = symexFind(sutN34TwoStmtBlock, tLabel("n34_two_stmt_block_v42"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

# =============================================================================
# N38 -- block-wrapped case-object discriminator reassignment, fully-backed
# arms. Mirrors tsymex_r6_n13_reassign_seqarm.nim's unwrapped
# `v.kind = rkB` shape, but the reassignment is now the LONE statement of a
# `block:` -- the exact N34 hazard shape. Both arms here are fully backed
# (plain `int` fields), so a correct parse should yield a genuine sxSat/
# sxUnsat pair, never sxUnknown.
# =============================================================================

type
  DKind = enum dkA, dkB
  D = object
    case kind: DKind
    of dkA: a: int
    of dkB: b: int

proc reassignToDkB(v: var D) =
  block:
    v.kind = dkB

proc sutN38ReachedSat(v: var D) =
  reassignToDkB(v)
  if v.kind == dkB:
    symexTarget("n38_reassign_reached")

proc sutN38FieldZeroSat(v: var D) =
  reassignToDkB(v)
  if v.b == 0:
    symexTarget("n38_field_zero_sat")

proc sutN38FieldNonzeroUnreachable(v: var D) =
  reassignToDkB(v)
  if v.b != 0:
    symexTarget("n38_field_nonzero_unreachable")

suite "symex round-6 N38 -- block-wrapped discriminator reassignment, fully-backed arm":

  test "N38-1: the block-wrapped reassignment itself is observed post-call -> sxSat " &
       "(pre-fix RED: spurious sxUnknown, zero degrade machinery involved)":
    let r = symexFind(sutN38ReachedSat, tLabel("n38_reassign_reached"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

  test "N38-2a: the fully-backed field is zero after reassignment -> sxSat":
    let r = symexFind(sutN38FieldZeroSat, tLabel("n38_field_zero_sat"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

  test "N38-2b: soundness companion -- field != 0 after reassignment is " &
       "UNREACHABLE (sxUnsat), never a wrong verdict":
    let r = symexFind(sutN38FieldNonzeroUnreachable, tLabel("n38_field_nonzero_unreachable"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnsat

# =============================================================================
# Version pin
# =============================================================================

suite "symex round-6 lows (blockparse) -- walker version pin":

  test "walker version floor >= 107 (N34/N38: block lone-statement mis-parse fix, " &
       "verdict-affecting)":
    check parseInt(symexWalkerVersion) >= 107

## Symex Phase 2 — interval/range tracking + abstraction-soundness proofs.
##
## Per ADR-0001, the walker's default mode (`isOptimised`) abstracts
## fixed-width Nim integers to `Z3Int` *when a static range analysis
## proves the abstraction sound* — i.e. proves that the BV semantics
## and Int semantics agree over the variable's reachable values.
##
## This module is **pure** (no Z3 dependency). It defines `Interval`
## over `int64`, sound interval arithmetic, the BV-window
## containment predicate `fitsBVWindow`, and `tryEvalInterval`, which
## propagates intervals through an IR expression and returns `none`
## the moment it hits an operation that breaks abstraction (notably
## bit-twiddling on integer types).
##
## The current cycle uses only `Interval` itself + the "from-`range`-
## type" constructor (`fromTypeRange`). Cycles 5+ wire in the
## proof-and-promote machinery.

import std/options
import std/sets
import std/tables
import ./types

type
  RangeMap* = Table[string, Interval]

# `Interval`, `AbstractionEvidence`, `AbstractionEntry`, `AbstractionLog`
# live in `types.nim` — this module imports them and adds the pure
# arithmetic / containment / propagation surface on top.

# ---- Constructors -----------------------------------------------------------

proc interval*(lo, hi: int64): Interval =
  Interval(lo: lo, hi: hi)

proc isEmpty*(i: Interval): bool {.inline.} =
  i.lo > i.hi

proc `$`*(i: Interval): string =
  "[" & $i.lo & ".." & $i.hi & "]"

# ---- BV-window containment --------------------------------------------------
#
# For width W signed:   window = [-2^(W-1), 2^(W-1) - 1]
# For width W unsigned: window = [0,         2^W - 1]
#
# An Interval fits the BV window iff its lo/hi are within these
# bounds — which is exactly the condition under which the BV
# semantics and the unbounded-Int semantics coincide.

proc bvWindow*(width: int, signed: bool): Interval =
  ## Closed interval `[lo, hi]` containing all bit-patterns of the
  ## given width interpreted under the given signedness. For width 64
  ## the unsigned upper bound `2^64 - 1` doesn't fit `int64` — we
  ## clamp to `int64.high` and rely on the BV floor in the runtime
  ## for any value above that.
  if signed:
    if width >= 64:
      interval(low(int64), high(int64))
    else:
      let lo = -(1'i64 shl (width - 1))
      let hi =  (1'i64 shl (width - 1)) - 1
      interval(lo, hi)
  else:
    if width >= 64:
      # 2^64 - 1 doesn't fit int64; we cap at int64.high. This means
      # an Interval ranging up to int64.high abstracts soundly even
      # for uint64, but anything claiming to reach higher fails the
      # window check below.
      interval(0'i64, high(int64))
    else:
      interval(0'i64, (1'i64 shl width) - 1)

proc fitsBVWindow*(i: Interval, ty: IRType): bool =
  if ty.kind != itInt: return false
  if i.isEmpty: return false
  let w = bvWindow(ty.width, ty.signed)
  i.lo >= w.lo and i.hi <= w.hi

# ---- Interval arithmetic ----------------------------------------------------
#
# All operations are sound — the returned interval contains every
# possible result when operands range over their input intervals.

proc add*(a, b: Interval): Interval =
  interval(a.lo + b.lo, a.hi + b.hi)

proc sub*(a, b: Interval): Interval =
  interval(a.lo - b.hi, a.hi - b.lo)

proc mul*(a, b: Interval): Interval =
  let p1 = a.lo * b.lo
  let p2 = a.lo * b.hi
  let p3 = a.hi * b.lo
  let p4 = a.hi * b.hi
  interval(min(min(p1, p2), min(p3, p4)),
           max(max(p1, p2), max(p3, p4)))

proc neg*(a: Interval): Interval =
  interval(-a.hi, -a.lo)

# ---- IR-expr interval propagation ------------------------------------------

proc tryEvalInterval*(e: IRExpr, ranges: RangeMap): Option[Interval] =
  ## Return `some(ivl)` if `e` can be shown to evaluate within `ivl`
  ## under the given variable ranges, using only sound interval
  ## arithmetic and the `iekVar` / `iekIntLit` base cases.
  ##
  ## Returns `none` (forcing the walker to keep the BV encoding) when
  ## the expression involves an operation whose interval is unknown
  ## or whose semantics aren't captured by ordinary interval
  ## arithmetic — notably `shl`/`shr`/`and`/`or`/`xor` on integers.
  if e == nil: return none(Interval)
  case e.kind
  of iekIntLit:
    some(interval(e.ival, e.ival))
  of iekBoolLit:
    none(Interval)
  of iekVar:
    if ranges.hasKey(e.vname): some(ranges[e.vname]) else: none(Interval)
  of iekField, iekIndex, iekArrayLit, iekSeqLen, iekStrLit, iekContains:
    # Composite-typed / dynamic-container expressions aren't tracked
    # by the interval abstraction; the walker stays in BV form.
    none(Interval)
  of iekUnop:
    case e.uop
    of uNeg:
      let inner = tryEvalInterval(e.operand, ranges)
      if inner.isSome: some(neg(inner.get)) else: none(Interval)
    of uNot:
      none(Interval)
  of iekBinop:
    case e.bop
    of bShl, bShr, bAnd, bOr, bXor:
      # Bit-twiddling: no interval arithmetic rule that's both sound
      # and tight enough to be useful. ADR-0001 specifies BV here.
      none(Interval)
    of bDiv, bMod:
      # Sound bounds depend on whether the divisor's interval includes
      # zero, and on signedness. For Phase 2 we punt; users with
      # div/mod-heavy code stay in BV.
      none(Interval)
    of bEq, bNe, bLt, bLe, bGt, bGe:
      # Comparisons return Bool, not an integer.
      none(Interval)
    of bAdd:
      let l = tryEvalInterval(e.lhs, ranges)
      let r = tryEvalInterval(e.rhs, ranges)
      if l.isSome and r.isSome: some(add(l.get, r.get)) else: none(Interval)
    of bSub:
      let l = tryEvalInterval(e.lhs, ranges)
      let r = tryEvalInterval(e.rhs, ranges)
      if l.isSome and r.isSome: some(sub(l.get, r.get)) else: none(Interval)
    of bMul:
      let l = tryEvalInterval(e.lhs, ranges)
      let r = tryEvalInterval(e.rhs, ranges)
      if l.isSome and r.isSome: some(mul(l.get, r.get)) else: none(Interval)

# ---- Promotion ban scan ----------------------------------------------------
#
# ADR-0001 (and SYMEX_PLAN Phase 2 deliverables): variables whose
# def-use chain contains a bit-twiddling op (shl/shr/and/or/xor on
# integer operands) cannot be soundly abstracted to `Z3Int`. We
# walk the IR once before lowering and collect those variable names;
# `runSymex` consults the result when deciding whether to promote.

const BitTwiddlingOps* = {bShl, bShr, bAnd, bOr, bXor}

proc collectVarRefs(e: IRExpr, into: var HashSet[string]) =
  if e == nil: return
  case e.kind
  of iekVar:
    into.incl e.vname
  of iekBinop:
    collectVarRefs(e.lhs, into)
    collectVarRefs(e.rhs, into)
  of iekUnop:
    collectVarRefs(e.operand, into)
  of iekField:
    collectVarRefs(e.obj, into)
  of iekIndex:
    collectVarRefs(e.arr, into)
    collectVarRefs(e.idx, into)
  of iekArrayLit:
    for c in e.lelems:
      collectVarRefs(c, into)
  of iekSeqLen:
    collectVarRefs(e.lenObj, into)
  of iekStrLit:
    discard
  of iekContains:
    collectVarRefs(e.container, into)
    collectVarRefs(e.key, into)
  of iekIntLit, iekBoolLit:
    discard

proc collectBanFromExpr(e: IRExpr,
                        intVars: HashSet[string],
                        banned: var HashSet[string]) =
  if e == nil: return
  case e.kind
  of iekBinop:
    if e.bop in BitTwiddlingOps:
      var refs: HashSet[string]
      collectVarRefs(e.lhs, refs)
      collectVarRefs(e.rhs, refs)
      for v in refs:
        if v in intVars:
          banned.incl v
    collectBanFromExpr(e.lhs, intVars, banned)
    collectBanFromExpr(e.rhs, intVars, banned)
  of iekUnop:
    collectBanFromExpr(e.operand, intVars, banned)
  else:
    discard

proc collectBan*(s: IRStmt,
                 intVars: HashSet[string]): HashSet[string] =
  ## Walk `s` and return the set of int-typed variable names whose
  ## def-use chain hits a bit-twiddling op. The runtime consults
  ## this set before deciding to promote.
  result = initHashSet[string]()
  if s == nil: return
  case s.kind
  of isBlock:
    for c in s.stmts:
      result.incl collectBan(c, intVars)
  of isIf:
    for br in s.branches:
      collectBanFromExpr(br.cond, intVars, result)
      result.incl collectBan(br.body, intVars)
    if s.elseBody != nil:
      result.incl collectBan(s.elseBody, intVars)
  of isLet:
    collectBanFromExpr(s.lvalue, intVars, result)
  of isAssert:
    collectBanFromExpr(s.acond, intVars, result)
  of isCall:
    for a in s.cargs:
      collectBanFromExpr(a, intVars, result)
  of isIndex:
    collectBanFromExpr(s.ixArr, intVars, result)
    collectBanFromExpr(s.ixIdx, intVars, result)
  of isReturn:
    if s.retExpr != nil:
      collectBanFromExpr(s.retExpr, intVars, result)
  of isTargetLabel, isUnsupported:
    discard

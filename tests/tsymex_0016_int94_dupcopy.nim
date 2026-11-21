## RFC-0016 INT-94. The `=dup` a sink position runs on a seq of plain values
## is the value copy, not an unrolled element loop.
##
## PRC-47 models the compiler's `=dup` of a `seq[T]` as the loop it is
## natively: the element type's `=dup` run on each element in index order
## (`dsl_parser.dupSeqValue`), so a hook's effects happen once per element,
## and the walk k-unrolls that loop as it does any other. For an element
## type with no user hook anywhere in it (`isPlainValueType`: ints, bools,
## floats, strings, and seqs or arrays of those) the loop runs nothing an
## execution can observe, yet it was built all the same. A `seq[int]` loop
## variable added to a `seq[seq[int]]` (`filterIt` over one, the
## `tsymex_0016_k9cg_unbacked_p_filterit` probe) copied through it at every
## iteration: the paths multiplied by the unroll bound each time (about 12x
## a step, 25,509 searches at unroll 5), the walk spent its whole work cap
## (1G units, 160-260 s) before the label past the loop was reached, and
## the verdict was an untrusted `sxUnknown`; a path whose inner seq was
## longer than the bound was tainted `beBudgetExhausted` for a copy. Since
## walker 489 such a copy is the value (as the explicit `=dup(x)` call's
## arm reads it, RFC-0005 S8cb item 5): the probe is 94 searches and about
## a second, a trusted `sxSat`.
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc filterNested(o0: seq[seq[int]]; k: int) =
  ## The probe's shape: every path through `filterIt` is modelled, and the
  ## label after it is reached only once the k-unroll has built each path.
  var o = o0
  let m = o.filterIt(it.len > 0)
  if m.len >= 0: symexTarget("hit")

proc addLong(a0: seq[int]; k: int) =
  ## `a` is read after `r.add a`, so the add copies it: a `seq[int]`'s
  ## `=dup`, of a length the walk does not know. The label asks for one
  ## longer than the default unroll bound (5).
  let a = a0
  var r: seq[seq[int]] = @[]
  r.add a
  if a.len > 8 and r.len == 1 and r[0].len == a.len: symexTarget("hit")

proc mkCut(limit: uint): SymexSettings =
  result = pinSettingsConst
  result.budget.walkRLimit = limit

## 60M units, about 15 s at the calibrated 0.254 us a unit: a modest share
## of the default budget (1G), which the probe spent whole before walker
## 489. The walk is well under it (see the header).
const modest = mkCut(60_000_000)

suite "INT-94: a sink position's =dup of a seq of plain values is the value copy":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 490

  test "filterIt over a seq[seq[int]] parameter is a trusted sat within a modest budget":
    let r = pinFind(filterNested, tLabel("hit"), modest)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check r.trusted
    check not r.errors.named(beBudgetExhaustedPrune)

  test "a seq[int] longer than the unroll bound, copied at a sink position, is not tainted":
    check native(addLong(@[1, 2, 3, 4, 5, 6, 7, 8, 9], 0)) == "hit"
    let r = pinFind(addLong, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check r.trusted
    check not r.errors.named(beBudgetExhausted)

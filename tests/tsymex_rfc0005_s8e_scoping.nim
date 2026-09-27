## RFC-0005 (soundness channels) slice S8e -- names keyed by symbol, generic
## callees keep their types, witnesses name types by symbol. Walker
## 152 -> 153.
##
## Three defects, each a place where the symex front end identified
## something by its SPELLING where Nim identifies it by its SYMBOL:
##   (a) scoping: two distinct locals of one spelling -- an inner `var k`
##       that shadows an outer `k` in a block, an `if` arm, a loop body, a
##       for-variable, a closure body, an inlined iterator body -- shared ONE
##       env slot, so a write through either was read through both. A
##       silent substitution: a false `sxSat` or `sxUnsat`, `errors` empty.
##       The `case`-narrowing stack (ADR-0029) keyed its scrutinee by
##       `.repr`, which conflated the same two symbols.
##   (b) generic callees: `x in s` / `s.add x` over `type MySeq[T] =
##       seq[T]`, and a user generic whose body calls a helper, aborted the
##       whole compile ("node has no type"): the monomorphizer rebuilt every
##       node untyped, and the callee's formals were read from the generic
##       declaration, not the instance.
##   (c) witnesses: the emitter wrote `Table`, `HashSet`, a user object's,
##       enum's or distinct's name and an enum member's name as identifiers
##       in the CALLER's scope, where they may be undeclared or name a
##       different symbol (S8d's dropped non-generic user `OrderedTable`).
##   (d) the walker version floor.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
from ./s8e_user_types import s8eSeq, s8eTable, s8eSet, s8eOrdered, s8eEnum,
  s8eDistinct, s8eVariant, s8eVariantElse, s8eHolder, s8eDual, s8eNode,
  s8eRefPlain, s8eSeqNode, s8eSeqRefPlain

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true

# ---- (a) scoping ------------------------------------------------------------

proc s8eBlockNeg(x: int) =
  var k = 0
  block:
    var k = 5
    k = x
    discard k
  if k != 0:
    symexTarget("s8e_block_neg")

proc s8eBlockPos(x: int) =
  var k = x
  block:
    var k = 0
    discard k
  if k == 7:
    symexTarget("s8e_block_pos")

proc s8eIfNeg(x: int) =
  var k = 0
  if x > 0:
    var k = x
    discard k
  if k != 0:
    symexTarget("s8e_if_neg")

proc s8eLoopNeg(x: int) =
  var k = 0
  for i in 0 ..< 2:
    var k = x
    discard k
  if k != 0:
    symexTarget("s8e_loop_neg")

proc s8eLoopCtl(x: int) =
  ## The same loop with no shadow: what the loop alone yields.
  var k = 0
  for i in 0 ..< 2:
    discard i
  if k != 0:
    symexTarget("s8e_loop_ctl")

proc s8eWhileNeg(x: int) =
  var k = 0
  var i = 0
  while i < 2:
    var k = x
    discard k
    inc i
  if k != 0:
    symexTarget("s8e_while_neg")

proc s8eForVarNeg(x: int) =
  var k = x
  for k in 0 ..< 2:
    discard k
  if k != x:
    symexTarget("s8e_forvar_neg")

proc s8eParamPos(k: int) =
  block:
    var k = 0
    discard k
  if k == 9:
    symexTarget("s8e_param_pos")

proc s8eClosureBody(x: int) =
  var k = 0
  let f = proc(v: int): int =
    var k = v
    k
  if f(x) != x:
    symexTarget("s8e_closurebody_neg")
  if k != 0:
    symexTarget("s8e_closurebody_outer")

proc s8eLambdaBoth(x: int) =
  ## The lambda reads the captured outer `k`, then declares its own.
  var k = x
  let f = proc(): int =
    let a = k
    var k = 5
    if k == 5: a else: 0
  if f() != x:
    symexTarget("s8e_lambdaboth_neg")

proc s8eCapOuterNeg(x: int) =
  var k = 3
  let g = proc(): int = k
  block:
    var k = x
    discard k
    if g() != 3:
      symexTarget("s8e_capouter_neg")

proc s8eCapOuterMut(x: int) =
  ## The closure captures the outer `k`, which is then written; an inner
  ## `k` is written after it. The call reads the outer one as it stands
  ## (S9), which is the outer write, not the inner one.
  var k = 3
  let g = proc(): int = k
  k = 4
  block:
    var k = x
    k = k div 2
    discard k
  if g() != 4:
    symexTarget("s8e_capoutermut_neg")

proc s8eCapInner(x: int) =
  var k = x
  block:
    var k = 3
    let g = proc(): int = k
    if g() != 3:
      symexTarget("s8e_capinner_neg")
  k = k div 2
  if k == 5:
    symexTarget("s8e_capinner_pos")

iterator s8eIt(n: int): int =
  var k = n
  yield k

proc s8eIterNeg(x: int) =
  ## The inlined iterator's own `k` is not the caller's.
  var k = x
  for v in s8eIt(7):
    discard v
  if k != x:
    symexTarget("s8e_iter_neg")

type
  ShK = enum shA, shB
  Sh = object
    tag: int
    case kind: ShK
    of shA: discard
    of shB: discard

proc s8eNarrowShadow(a, b: ShK) =
  ## The `of shA` narrowing is about the OUTER `k`; the constructor's
  ## discriminant is the inner one, which may be `shB`.
  let k = a
  case k
  of shA:
    block:
      let k = b
      let v = Sh(tag: 1, kind: k)
      if v.kind == shB:
        symexTarget("s8e_narrow_pos")
  of shB: discard

suite "S8e (a) scoping: one env slot per symbol":
  test "block: the inner write does not reach the outer k -- sxUnsat":
    let r = symexFind(s8eBlockNeg, tLabel("s8e_block_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat
    checkUnsatOverTaintOnly(r)

  test "block: the inner k does not hide the outer k -- sxSat at 7":
    let r = symexFind(s8eBlockPos, tLabel("s8e_block_pos"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == 7

  test "if arm: sxUnsat":
    let r = symexFind(s8eIfNeg, tLabel("s8e_if_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat
    checkUnsatOverTaintOnly(r)

  test "loop body: never the conflated sxSat; the loop's own decline":
    let ctl = symexFind(s8eLoopCtl, tLabel("s8e_loop_ctl"))
    checkpoint("ctl " & $ctl.status & " " & show(ctl.errors))
    let r = symexFind(s8eLoopNeg, tLabel("s8e_loop_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status != sxSat
    check r.status == ctl.status

  test "while body: never the conflated sxSat":
    let r = symexFind(s8eWhileNeg, tLabel("s8e_while_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status != sxSat

  test "for-variable: never the conflated sxSat":
    let r = symexFind(s8eForVarNeg, tLabel("s8e_forvar_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status != sxSat

  test "param shadowed in a block: sxSat at 9":
    let r = symexFind(s8eParamPos, tLabel("s8e_param_pos"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == 9

  test "closure body local (control): sxUnsat both ways":
    let r1 = symexFind(s8eClosureBody, tLabel("s8e_closurebody_neg"))
    checkpoint($r1.status & " " & show(r1.errors))
    check r1.status == sxUnsat
    checkUnsatOverTaintOnly(r1)
    let r2 = symexFind(s8eClosureBody, tLabel("s8e_closurebody_outer"))
    checkpoint($r2.status & " " & show(r2.errors))
    check r2.status == sxUnsat
    checkUnsatOverTaintOnly(r2)

  test "a lambda that captures k and declares its own k: sxUnsat":
    let r = symexFind(s8eLambdaBoth, tLabel("s8e_lambdaboth_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat
    checkUnsatOverTaintOnly(r)

  test "captured outer k, inner shadow written: sxUnsat":
    let r = symexFind(s8eCapOuterNeg, tLabel("s8e_capouter_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat
    checkUnsatOverTaintOnly(r)

  test "captured outer k mutated, then an inner shadow written: sxUnsat":
    let r = symexFind(s8eCapOuterMut, tLabel("s8e_capoutermut_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat
    checkUnsatOverTaintOnly(r)

  test "captured inner k: sxUnsat; the outer k stays the param's":
    let r1 = symexFind(s8eCapInner, tLabel("s8e_capinner_neg"))
    checkpoint($r1.status & " " & show(r1.errors))
    check r1.status == sxUnsat
    checkUnsatOverTaintOnly(r1)
    let r2 = symexFind(s8eCapInner, tLabel("s8e_capinner_pos"))
    checkpoint($r2.status & " " & show(r2.errors))
    check r2.status == sxSat
    check r2.witness[0] div 2 == 5

  test "an inlined iterator's local is not the caller's: sxUnsat":
    let r = symexFind(s8eIterNeg, tLabel("s8e_iter_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat
    checkUnsatOverTaintOnly(r)

  test "case narrowing keys the scrutinee by symbol: sxSat at (shA, shB)":
    let r = symexFind(s8eNarrowShadow, tLabel("s8e_narrow_pos"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == shA
    check r.witness[1] == shB

# ---- (b) generic callees ----------------------------------------------------

type MySeq[T] = seq[T]

proc s8eAliasParamIn(s: MySeq[int], x: int) =
  if x in s:
    symexTarget("s8e_alias_param_in")

proc s8eAliasLocalIn(x: int) =
  let s: MySeq[int] = @[1, 2, 3]
  if x in s:
    symexTarget("s8e_alias_local_in")

proc s8eAliasLocalAdd(x: int) =
  var s: MySeq[int] = @[1]
  s.add x
  if s.len == 2 and s[1] == 5:
    symexTarget("s8e_alias_local_add")

proc s8eHelper(v: int): int = v + 1

proc s8eG1[T](a: seq[T], x: T): bool =
  a.len > 0 and a[0] == x

proc s8eG2[T](x: T): int =
  s8eHelper(x) * 2

proc s8eG3[T](a: seq[T]): int =
  a.len + s8eHelper(1)

proc s8eGen1(s: seq[int], x: int) =
  if s8eG1(s, x): symexTarget("s8e_gen1")

proc s8eGen2(x: int) =
  if s8eG2(x) == 8: symexTarget("s8e_gen2")

proc s8eGen3(s: seq[int]) =
  if s8eG3(s) == 5: symexTarget("s8e_gen3")

suite "S8e (b) generic callees keep their types":
  # Before S8e none of these compiled: the file aborted at macro expansion.
  test "a user alias of seq as a param: the S8d user-alias decline":
    let r = symexFind(s8eAliasParamIn, tLabel("s8e_alias_param_in"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedParamType)

  test "`x in s` over a local alias: a recorded decline":
    let r = symexFind(s8eAliasLocalIn, tLabel("s8e_alias_local_in"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check r.errors.len > 0

  test "`s.add x` over a local alias: a recorded decline":
    let r = symexFind(s8eAliasLocalAdd, tLabel("s8e_alias_local_add"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check r.errors.len > 0

  test "a user generic over seq[T]: modelled, sxSat":
    let r = symexFind(s8eGen1, tLabel("s8e_gen1"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len > 0 and r.witness[0][0] == r.witness[1]

  test "a user generic whose body calls a helper: modelled, sxSat at 3":
    let r = symexFind(s8eGen2, tLabel("s8e_gen2"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == 3

  test "a user generic over seq[T] that calls a helper: sxSat at len 3":
    let r = symexFind(s8eGen3, tLabel("s8e_gen3"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 3

# ---- (c) witnesses name types by symbol -------------------------------------

type
  Color = enum
    ## A LOCAL type spelled like `s8e_user_types.Color`, with other members.
    ## An emitter that writes `Color(...)` builds the witness as this type.
    lRed, lGreen, lBlue, lExtra

suite "S8e (c) the witness emitter names types by symbol":
  # This module imports only the SUT procs from `s8e_user_types`, and not
  # `std/tables` or `std/sets` directly. Before S8e it did not compile.
  test "seq[int]":
    let r = symexFind(s8eSeq, tLabel("s8e_w_seq"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 2 and r.witness[0][0] == 5

  test "Table[string, int]":
    let r = symexFind(s8eTable, tLabel("s8e_w_table"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check $r.witness[0] == """{"a": 3}"""

  test "HashSet[int]":
    let r = symexFind(s8eSet, tLabel("s8e_w_set"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check 4 in r.witness[0]

  test "a non-generic user OrderedTable beside std/tables.OrderedTable":
    let r = symexFind(s8eOrdered, tLabel("s8e_w_ordered"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].a == 7

  test "a user enum, beside a local enum of the same spelling":
    let r = symexFind(s8eEnum, tLabel("s8e_w_enum"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check $r.witness[0] == "cBlue"

  test "a user distinct":
    let r = symexFind(s8eDistinct, tLabel("s8e_w_distinct"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat

  test "a user variant: the tag is written through the disc type":
    let r = symexFind(s8eVariant, tLabel("s8e_w_variant"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check $r.witness[0] == "(kind: skSquare, side: 4)"

  test "a user variant with an else arm":
    let r = symexFind(s8eVariantElse, tLabel("s8e_w_variant_else"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check $r.witness[0] == "(tk: tkC, rest: 6)"

  test "a user object whose fields are a user enum and distinct":
    let r = symexFind(s8eHolder, tLabel("s8e_w_holder"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check $r.witness[0].c == "cGreen"

  test "a user multi-variant":
    let r = symexFind(s8eDual, tLabel("s8e_w_dual"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check $r.witness[0] == "(ax: axP, pv: 2, ay: ayS, sv: 8)"

  test "a user ref object with a recursive field":
    let r = symexFind(s8eNode, tLabel("s8e_w_node"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] != nil and r.witness[0].v == 2

  test "a ref to a user object: the cell is allocated through its symbol":
    let r = symexFind(s8eRefPlain, tLabel("s8e_w_refplain"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] != nil and r.witness[0].w == 6

  test "seq of a user ref-object alias":
    let r = symexFind(s8eSeqNode, tLabel("s8e_w_seqnode"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 2

  test "seq of ref to a user object":
    let r = symexFind(s8eSeqRefPlain, tLabel("s8e_w_seqrefplain"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0].len == 3

  test "the local Color is untouched":
    check $Color(2) == "lBlue"

# ---- (d) walker version -----------------------------------------------------

suite "S8e (d) walker version":
  test "floor pin":
    check parseInt(symexWalkerVersion) >= 153

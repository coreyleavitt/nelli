## RFC-0016 Wave 4 H1b (HRV-32): the `case` EXPRESSION arm of the parser
## (`hoistCaseExpr`) mines the same `of`-label tag set as the `case`
## STATEMENT arm (ADR-0029), through one shared helper. A variant
## constructor with a symbolic discriminant under `case op of wt0, wt1:` in
## expression position forks over {wt0, wt1}, not over every declared arm.
##
## RED (walker 370 and below): the wide 10-tag enum exceeded
## `maxVariantConstructorForks` (8) because the expression arm never pushed
## the narrowing, so both queries below were a classified `sxUnknown`.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
from ./s8cu_helpers import named

type
  WideTag = enum wt0, wt1, wt2, wt3, wt4, wt5, wt6, wt7, wt8, wt9
  WideObj = object
    tag: int
    case kind: WideTag
    of wt0: f0: int
    of wt1: f1: int
    of wt2: f2: int
    of wt3: f3: int
    of wt4: f4: int
    of wt5: f5: int
    of wt6: f6: int
    of wt7: f7: int
    of wt8: f8: int
    of wt9: f9: int

proc sutExprTag(b: byte, n: int) =
  let op = if b == 1'u8: wt0 else: wt1
  let r = case op
    of wt0, wt1: ord(WideObj(kind: op, tag: n).kind)
    else: 0
  if r == 1:
    symexTarget("expr_tag_wt1")

proc sutExprImpossibleTag(b: byte, n: int) =
  let op = if b == 1'u8: wt0 else: wt1
  let r = case op
    of wt0, wt1: ord(WideObj(kind: op, tag: n).kind)
    else: 0
  if r == 5:
    symexTarget("expr_tag_wt5")

proc sutExprPlainField(b: byte, n: int) =
  let op = if b == 1'u8: wt0 else: wt1
  let r = case op
    of wt0, wt1: WideObj(kind: op, tag: n).tag
    else: 0
  if r == 7:
    symexTarget("expr_plain_7")

# The unnarrowed shape stays a budget decline: a `case` expression whose
# label set does not narrow (the constructor sits in the else arm).
proc sutExprElseUnnarrowed(b: byte, n: int) =
  let op = if b == 1'u8: wt0 else: wt1
  let r = case b
    of 3'u8: 0
    else: WideObj(kind: op, tag: n).tag
  if r == 7:
    symexTarget("expr_else_7")

suite "RFC-0016 H1b HRV-32 - case-expression tag narrowing":

  test "walker version floor: the case-expression narrowing is 371 or later":
    check symexWalkerVersion.parseInt >= 371

  test "narrowed constructor under a case expression resolves: wt1 reachable":
    let res = symexFind(sutExprTag, tLabel("expr_tag_wt1"))
    check res.status == sxSat
    check res.witness[0] != 1'u8

  test "a tag outside the narrowed set is UNSAT (not an unknown decline)":
    let res = symexFind(sutExprImpossibleTag, tLabel("expr_tag_wt5"))
    check res.status == sxUnsat

  test "a plain field read through the narrowed constructor is SAT with witness":
    let res = symexFind(sutExprPlainField, tLabel("expr_plain_7"))
    check res.status == sxSat
    check res.witness[1] == 7

  test "no narrowing set from the labels: the budget decline is unchanged":
    let res = symexFind(sutExprElseUnnarrowed, tLabel("expr_else_7"))
    check res.status == sxUnknown
    check res.errors.named(beBudgetExhaustedUnmodelled)

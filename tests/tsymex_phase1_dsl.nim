## ADR-0002 validation: Layer 1 (`dsl_parser`) tested in isolation.
##
## These tests exercise the parser without invoking the walker or Z3:
## they feed Nim AST fixtures via macros and assert on the IR's
## canonical S-expression form. If a layer-boundary leak ever forces
## these tests to need walker or runtime state, that's an ADR-0002
## regression — the parser has stopped being independently testable.
##
## We use `macro` wrappers so the AST fixture is built at the call
## site as a plain `untyped` expression; the parser doesn't depend
## on semchecked types for the expression / non-let-section subset
## tested here.

import std/unittest
import std/macros
import std/strutils
import proptest/smt/types
import proptest/smt/dsl_parser

macro parseExprStr(code: untyped): string =
  newLit(render(parseExpr(code)))

macro parseStmtStr(code: untyped): string =
  newLit(render(parseStmt(code)))

suite "DSL Layer 1 — expression parser":
  test "integer literal":
    check parseExprStr(42) == "42"

  test "negative literal folds to int literal":
    # Nim's parser folds `-7` to a single nnkIntLit(-7); the parser
    # preserves that. Unary minus survives only on non-literal operands.
    check parseExprStr(-7) == "-7"
    check parseExprStr(-x) == "(uNeg x)"

  test "variable reference":
    check parseExprStr(x) == "x"

  test "infix comparison `>`":
    check parseExprStr(x > 5) == "(bGt x 5)"

  test "infix arithmetic":
    check parseExprStr(x + y * 2) == "(bAdd x (bMul y 2))"

  test "boolean conjunction":
    check parseExprStr(p and q) == "(bAnd p q)"

  test "boolean negation":
    check parseExprStr(not p) == "(uNot p)"

  test "nested mixed":
    check parseExprStr((x + 1) > 0 and y < 10) ==
      "(bAnd (bGt (bAdd x 1) 0) (bLt y 10))"

  test "div and mod":
    check parseExprStr(x div 3) == "(bDiv x 3)"
    check parseExprStr(x mod 7) == "(bMod x 7)"

suite "DSL Layer 1 — statement parser":
  test "lone if with single branch":
    let s = parseStmtStr(if x > 0: discard)
    check s == "if([(bGt x 0)=>{}])"

  test "if / else":
    let s = parseStmtStr(
      if x > 0: discard
      else:     discard)
    check s == "if([(bGt x 0)=>{}][else=>{}])"

  test "elif chain":
    let s = parseStmtStr(
      if x < 0:    discard
      elif x == 0: discard
      else:        discard)
    check s == "if([(bLt x 0)=>{}][(bEq x 0)=>{}][else=>{}])"

  test "return statement":
    check parseStmtStr(
      block:
        return) == "return"

  test "symexTarget recognised as a marker":
    check parseStmtStr(symexTarget("foo")) == "target(foo)"

  test "symexAssert lowers to an isAssert IR node":
    check parseStmtStr(symexAssert(x >= 0)) == "assert((bGe x 0))"

  test "unknown call becomes isUnsupported":
    let r = parseStmtStr(someUnknownProc(1, 2))
    check r.startsWith("unsupported(")

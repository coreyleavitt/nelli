## Phase 1 arithmetic / control-flow tests for the symex walker.
## Each test exercises one piece of the supported fragment:
## int params + arithmetic + comparison + `nnkIfStmt`. BV[W] encoding
## throughout — Phase 2 will add the abstraction layer.
import std/unittest
import proptest/symex

proc reachIfBig(x: int) =
  if x > 5:
    symexTarget("big")

proc unreachableTarget(x: int) =
  if x > 5 and x < 5:
    symexTarget("impossible")

suite "symex Phase 1 — arithmetic":
  test "tracer: reaches a labeled branch under int comparison":
    let r = symexFind(reachIfBig, tLabel("big"))
    check r.status == sxSat
    check r.witness[0] > 5

  test "sxUnsat for provably unreachable target":
    let r = symexFind(unreachableTarget, tLabel("impossible"))
    check r.status == sxUnsat

  test "else-branch path condition is the negation":
    proc twoWay(x: int) =
      if x > 5: symexTarget("hi")
      else:     symexTarget("lo")
    let r = symexFind(twoWay, tLabel("lo"))
    check r.status == sxSat
    check r.witness[0] <= 5

  test "nested if produces conjunction":
    proc nested(x: int, y: int) =
      if x > 0:
        if y > x:
          symexTarget("both-pos-and-ordered")
    let r = symexFind(nested, tLabel("both-pos-and-ordered"))
    check r.status == sxSat
    check r.witness[0] > 0
    check r.witness[1] > r.witness[0]

  test "return mid-body terminates that path":
    # Two if statements with the same guard. If `return` correctly
    # terminates the path, the only surviving path on the second `if`
    # has x <= 5, so its then-branch is UNSAT → target unreachable.
    # If `return` is ignored, path 1 continues with pc = [x > 5] and
    # the second if's then is trivially SAT.
    proc earlyExit(x: int) =
      if x > 5:
        return
      if x > 5:
        symexTarget("impossible-if-return-works")
    let r = symexFind(earlyExit, tLabel("impossible-if-return-works"))
    check r.status == sxUnsat

  test "statements after an if see the merged post-if path conditions":
    # Tests that the block's path-condition state propagates through
    # an `if` for the following statement. The target after the if is
    # reachable only when x > 0; if the block doesn't carry the
    # x > 0 constraint forward, witness extraction here would be
    # silently wrong.
    proc afterIf(x: int) =
      if x > 0:
        discard 1
      else:
        return
      symexTarget("only-positive")
    let r = symexFind(afterIf, tLabel("only-positive"))
    check r.status == sxSat
    check r.witness[0] > 0

  test "elif chain — middle branch's PC is `not prior ∧ own`":
    proc threeWay(x: int) =
      if x < 0:    symexTarget("neg")
      elif x == 0: symexTarget("zero")
      else:        symexTarget("pos")
    let zero = symexFind(threeWay, tLabel("zero"))
    check zero.status == sxSat
    check zero.witness[0] == 0
    let pos = symexFind(threeWay, tLabel("pos"))
    check pos.status == sxSat
    check pos.witness[0] > 0
    let neg = symexFind(threeWay, tLabel("neg"))
    check neg.status == sxSat
    check neg.witness[0] < 0

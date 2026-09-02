## RFC-0005 slice 1 — `case` in EXPRESSION position (the real B7-2 cause).
##
## RFC-0001's BLOCKER B7-2 was recorded as "case/else-raise sibling
## poisoning" and escalated as needing a branch-scoped-degrade ARCHITECTURE.
## Reading the parser says otherwise:
##
##   * `case` as a STATEMENT is fully supported — `parseStmt`'s `nnkCaseStmt`
##     arm lowers it to an if-elif chain (labels OR-chained, ranges, `else`).
##   * `case` as an EXPRESSION has no `parseExpr` arm, so it falls to the
##     catch-all and declines with `feUnsupportedExprKind`.
##
## The "poisoning" is a consequence, not a separate defect: the declining
## proc is a CALLEE, parsed whole-proc at registration time, BEFORE any path
## exists. A parse-time decline has no path to scope to, so it taints the
## whole query — including branches that never call it. That is why B7r2's
## path-scoping fixed its siblings (call-boundary, construction-follow) but
## left this one untouched.
##
## Fix shape: A-normalise at the boundary, per RFC-0002's doctrine and
## mirroring the `nnkStmtListExpr` arm's own comment ("the same
## A-normalisation channel every other expression-position side-effect in
## this file already uses") — synthesise a temp, emit the case in STATEMENT
## form into `preamble` with each arm assigning to it, return the temp. The
## `else: raise` arm needs nothing special: a raise terminates the path, so
## the temp is never read there.
##
## RED until the parser arm lands.

import std/[unittest, strutils]
import nelli/symex

type CaseExprTestError = object of CatchableError

suite "RFC-0005 s1 — case-expression: the disjoint-sibling target is reachable":

  test "s1-1: a callee using case-as-expression must not poison a DISJOINT branch":
    ## The exact B7-2 shape, minimised. `parseModeLike` is only ever called
    ## on the `wireOp == 1` branch; the target lives on `wireOp == 3` and is
    ## structurally unrelated. Pre-fix: sxUnknown (whole-query parse-time
    ## decline). Post-fix: the target is reachable.
    proc parseModeLike(s: string): int =
      case s
      of "octet": 1
      of "netascii": 2
      else: raise newException(CaseExprTestError, "unknown mode")

    proc sut(wireOp: int, modeStr: string, blockNum: int) =
      if wireOp == 1:
        let m = parseModeLike(modeStr)
        discard m
      elif wireOp == 3:
        if blockNum == 5:
          symexTarget("s1_sibling_reached")

    let r = symexFind(sut, tLabel("s1_sibling_reached"))
    check r.status == sxSat

  test "s1-2: the case-expression's own value is modelled, not just tolerated":
    ## Stronger than s1-1: the target is guarded BY the case-expression's
    ## result, so a fix that merely stops declining (e.g. returning an
    ## unconstrained dummy) is not enough — the arm value has to be real.
    proc classify(s: string): int =
      case s
      of "octet": 1
      of "netascii": 2
      else: 0

    proc sut(modeStr: string) =
      if classify(modeStr) == 2:
        symexTarget("s1_netascii_arm")

    let r = symexFind(sut, tLabel("s1_netascii_arm"))
    check r.status == sxSat

  test "s1-3: UNSAT companion — an arm value the case can never yield":
    ## Guards against a fix that makes the temp unconstrained: if the temp
    ## were free, `== 99` would be satisfiable and this would report sxSat.
    proc classify(s: string): int =
      case s
      of "octet": 1
      of "netascii": 2
      else: 0

    proc sut(modeStr: string) =
      if classify(modeStr) == 99:
        symexTarget("s1_impossible_arm")

    let r = symexFind(sut, tLabel("s1_impossible_arm"))
    check r.status == sxUnsat

suite "RFC-0005 s1 — B7-2's verbatim shape, runnable on Linux":

  test "s1-4: the ORIGINAL B7r2-2 SUT (scrutinee via `toLowerAscii`) reaches its sibling target":
    ## `tsymex_r6_b7r2_pathscope` holds B7-2's own pin but is one of the six
    ## suites that hang under Linux/podman, so it is only ever checked by the
    ## Windows CI leg. Carry the exact shape here too — including the
    ## `s.toLowerAscii` scrutinee the minimal s1-1 repro omits — so a
    ## regression is caught in the local loop instead of waiting for CI.
    proc parseModeLike(s: string): int =
      case s.toLowerAscii
      of "octet": 1
      of "netascii": 2
      else: raise newException(CaseExprTestError, "unknown transfer mode: " & s)

    proc sut(wireOp: int, modeStr: string, blockNum: int) =
      if wireOp == 1:
        let m = parseModeLike(modeStr)
        discard m
      elif wireOp == 3:
        if blockNum == 5:
          symexTarget("s1_verbatim_sibling_reached")

    let r = symexFind(sut, tLabel("s1_verbatim_sibling_reached"))
    check r.status == sxSat
    for e in r.errors:
      check not (e.kind == feUnsupportedExprKind and "nnkCaseStmt" in e.msg)

suite "RFC-0005 s1 — version floor":

  test "walker version floor >= 124 (case-expression A-normalisation)":
    check parseInt(symexWalkerVersion) >= 124

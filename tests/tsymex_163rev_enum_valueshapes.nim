## Issue #163 review round 2, findings R18/R19/R23. The round's structural
## fix extracts `dsl_typebridge.enumFieldOrdinals` as the SINGLE source of
## truth both `classifyType`'s enum arm and `dsl_parser.parseExpr`'s
## `nnkSym` arm now walk through -- see that proc's doc comment for the full
## field-shape inventory. This file pins the shapes review finding R18 named
## specifically, plus a non-regression check on R19/R23's degrade paths.
##
## R18 (Medium): both loops guarded "is this field's value an explicit
## ordinal" on `c[1].kind in nnkIntLit..nnkUInt64Lit`. A Nim enum field may
## also carry a TUPLE-constructor value (`a = (1, "alpha")`, the `(ordinal,
## displayName)` form used to give a field a custom `$` string) -- `c[1]` is
## then `nnkTupleConstr`, not an int literal, so both loops silently fell
## through to the auto-increment counter instead of the tuple's real
## ordinal. The two loops still AGREED with each other (no witness/domain
## mismatch), but both were simply wrong versus real Nim ordinals -- the
## same defect class R2/R15 exist to fix, for a value-node shape their guard
## did not recognise.
##
## Per house style (`tsymex_163rev_enum_ordinal.nim`), every symbolic
## expectation is paired with an ORACLE computed by real Nim execution
## (`ord()` calls below), and a reachable target's witness is REPLAYED --
## cast back to the enum type and checked to genuinely satisfy the gated
## comparison, not merely checked for `status == sxSat`.
##
## RED, confirmed pre-fix (this session, `git stash` of the three src/
## changes + rerun, then `git stash pop`): the classifier cross-check FAILED
## outright (`mixedInfo was (true, 0, 2, false)`, not `(true, 5, 7, false)`
## -- the enum's own real members 5/6/7 excluded from its declared range),
## and all three `Mixed` witness-replay tests FAILED: `symexFind` returned
## `r.witness[0]` 0/1/2 (the wrong, auto-increment-from-0 ordinals) instead
## of 5/6/7, and — since `Mixed`'s real declared range is `5..7` — casting
## that wrong witness back with `Mixed(r.witness[0])` raised an unhandled
## `RangeDefect` ("value out of range: 0 notin 5 .. 7") rather than merely
## comparing unequal. Post-fix, all three pass cleanly.
##
## No version-floor pin outside the dedicated suite below: R18 is a
## verdict-affecting change (a wrong domain and wrong embedded constants for
## a tuple-valued enum become right), so it must be covered by the round's
## single central `symexWalkerVersion` bump, same as R2/R15 before it.

import std/[unittest, macros]
import std/strutils
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/dsl_typebridge

## ---------------------------------------------------------------------------
## Cross-check helper (same shape as tsymex_163rev_enum_ordinal.nim): reuse
## the classifier's own typedesc-classifying macro so this file does not
## have to touch `dsl_typebridge.nim` to observe its output.

macro classifyEnumTypedesc(T: typedesc): (bool, int64, int64, bool) =
  var inst = T.getTypeInst
  if inst.kind == nnkBracketExpr and inst.len == 2 and
     inst[0].kind in {nnkSym, nnkIdent} and inst[0].strVal == "typeDesc":
    inst = inst[1]
  let cls = classifyType(inst)
  newTree(nnkTupleConstr, newLit(cls.ty.hasRange), newLit(cls.ty.rangeLo),
          newLit(cls.ty.rangeHi), newLit(cls.ty.signed))

## ---------------------------------------------------------------------------
## R18 primary case: an explicit tuple-constructor ordinal (`(5, "five")`)
## followed by two bare-string-name fields whose ordinal must continue the
## auto-increment FROM the tuple's explicit base (6, 7) -- not from 0. This
## single type exercises both halves of the fix: reading the tuple's
## ordinal, and correctly resuming implicit auto-increment after it.
##
## Oracle (confirmed by `scratchpad/probe_r18_mixed.nim` against this exact
## toolchain, not guessed): ord(mxA)=5, ord(mxB)=6, ord(mxC)=7.

type
  Mixed = enum
    mxA = (5, "five")
    mxB = "six"
    mxC = "seven"

const mixedInfo = classifyEnumTypedesc(Mixed)

proc checkA(x: Mixed) =
  if x == mxA:
    symexTarget("a")

proc checkB(x: Mixed) =
  if x == mxB:
    symexTarget("b")

proc checkC(x: Mixed) =
  if x == mxC:
    symexTarget("c")

suite "#163 review R18 -- tuple/string-valued enum fields get their real ordinal":

  test "the oracle -- Mixed's real ordinals are 5, 6, 7":
    check ord(mxA) == 5
    check ord(mxB) == 6
    check ord(mxC) == 7

  test "cross-check -- classifier domain is [5, 7], unsigned":
    ## RED (pre-fix): both loops' int-literal-only guard rejected mxA's
    ## `nnkTupleConstr` value, so the classifier fell back to the implicit
    ## counter and reported domain (true, 0, 2, false) -- excluding the
    ## enum's own real members 5/6/7 entirely from its declared range.
    check mixedInfo == (true, 5'i64, 7'i64, false)

  test "x == mxA is reachable, and the witness genuinely satisfies it":
    ## RED (pre-fix): sxSat, but the embedded RHS was 0 (the auto-increment
    ## fallback), not 5 (mxA's real ordinal) -- the returned witness casts
    ## back to mxA only because Mixed also happens to have SOME member at
    ## ordinal 0... it does not (Mixed's real domain starts at 5), so
    ## pre-fix this cast is undefined-shaped; the fixed assertion below is
    ## the meaningful one.
    let r = symexFind(checkA, tLabel("a"))
    check r.status == sxSat
    # Issue #163 item 1 (rev): the witness reader now emits a correctly-typed
    # `Mixed` value directly (see `IRType.enumName`), so `r.witness[0]` is
    # already `Mixed` rather than a raw ordinal -- compare via `ord()`
    # instead of a bare `int` equality.
    check ord(r.witness[0]) == 5
    check Mixed(r.witness[0]) == mxA

  test "x == mxB is reachable, and the witness genuinely satisfies it":
    ## RED (pre-fix): embedded RHS 1 (declaration-position/auto-increment
    ## off the wrong base), not 6 (mxB's real ordinal).
    let r = symexFind(checkB, tLabel("b"))
    check r.status == sxSat
    check ord(r.witness[0]) == 6
    check Mixed(r.witness[0]) == mxB

  test "x == mxC is reachable, and the witness genuinely satisfies it":
    ## RED (pre-fix): embedded RHS 2, not 7 (mxC's real ordinal).
    let r = symexFind(checkC, tLabel("c"))
    check r.status == sxSat
    check ord(r.witness[0]) == 7
    check Mixed(r.witness[0]) == mxC

## ---------------------------------------------------------------------------
## R18 secondary case: a bare string-name-only enum (`a = "alpha"`, no
## tuple) -- confirmed by probe (`scratchpad/probe_r18_stringonly.nim`) to
## assign ONLY the `$`-name, never an explicit ordinal, so real ordinals
## stay dense from 0. Included because the review finding explicitly named
## this shape ("check whether that assigns a string NAME with an implicit
## ordinal rather than an explicit value") -- pinning that this is NOT
## mistaken for an explicit-ordinal shape now that the tuple form is
## recognised (a wrong implementation might, e.g., try to parse the string
## as a number, or treat any `nnkEnumFieldDef` as ipso facto explicit).
## Dense-from-0 means this shape alone produces no RED (position happens to
## equal ordinal throughout) -- a same-position sanity check, same role as
## `tsymex_163rev_enum_ordinal.nim`'s `hoA` case.

type
  Signal = enum
    sgGreen = "go"
    sgYellow = "caution"
    sgRed = "stop"

const signalInfo = classifyEnumTypedesc(Signal)

proc checkGreen(x: Signal) =
  if x == sgGreen:
    symexTarget("green")

proc checkRed(x: Signal) =
  if x == sgRed:
    symexTarget("red")

suite "#163 review R18 -- bare string-name-only enum stays dense from 0":

  test "the oracle -- Signal's real ordinals are 0, 1, 2":
    check ord(sgGreen) == 0
    check ord(sgYellow) == 1
    check ord(sgRed) == 2
    check $sgGreen == "go"

  test "cross-check -- classifier domain is [0, 2], unsigned":
    check signalInfo == (true, 0'i64, 2'i64, false)

  test "x == sgGreen and x == sgRed are reachable with correct witnesses":
    let rGreen = symexFind(checkGreen, tLabel("green"))
    check rGreen.status == sxSat
    check Signal(rGreen.witness[0]) == sgGreen

    let rRed = symexFind(checkRed, tLabel("red"))
    check rRed.status == sxSat
    check Signal(rRed.witness[0]) == sgRed

## ---------------------------------------------------------------------------
## R19/R23 non-regression: neither finding has a live repro against this
## toolchain (R19's `getTypeInst` resolution and R23's `nnkSym`/
## `nnkEnumFieldDef`-only child kinds hold for every enum shape reachable
## through ordinary, non-generic, non-macro-generated source -- see
## `enumFieldOrdinals`'s doc comment). Their fixes are a compile-time
## `error()` (R23, unreachable per Nim's own grammar) and a classified
## `feEnumOrdinalUnresolved` parse-error degrade (R19) that no test in this
## corpus can trigger without hand-forging malformed macro AST. What IS
## testable is that ordinary enum resolution is UNCHANGED by their
## presence -- the suites above, plus the full `tsymex_163rev_enum_ordinal`
## suite (negative-ordinal, sparse/holed, and dense enums), already cover
## that; re-run here as an explicit statement of scope rather than
## duplicated tests.

suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 136 (the review round's single bump)":
    check parseInt(symexWalkerVersion) >= 136

## Chapulin round-3 natural-form probe follow-up (§0 clause (b)), walker
## v64. An UNMODELED infix operator in expression position — e.g. `a .. b`
## building an HSlice VALUE in a let/argument position, which the
## bracket-slice interceptors never see — used to abort the whole file's
## compilation at `binopForInfix`'s macro-time `error()` (observed on
## chapulin's real `parseTftpUri`). It now degrades CR-2a-style: a
## classified `feUnsupportedOp` parse error (sevError forces the whole-run
## verdict to sxUnknown), an `mkUnsupported` SND-1 taint, and a typed zero
## dummy so parsing continues. THIS FILE COMPILING is half the pin; the
## classified sxUnknown is the other half.
import std/[unittest, strutils, sequtils]
import proptest/symex
import proptest/smt/canonicalize
import proptest/smt/types

proc sliceValue(x: int) =
  if x > 0:
    let r = 1 .. x          # bare `..` infix — an HSlice VALUE, unmodeled
    discard r
    symexTarget("after-slice")

suite "symex re-test — unmodeled infix degrades instead of aborting compile":

  test "`a .. b` in expression position: classified sxUnknown (was a macro error)":
    let r = symexFind(sliceValue, tLabel("after-slice"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == feUnsupportedOp)

suite "symex re-test infix degrade — walker version pin":

  test "walker version floor >= 64":
    check parseInt(symexWalkerVersion) >= 64

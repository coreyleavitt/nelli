## RFC-0016 K2F-3 -- a push reaches a module first compiled by an
## `import ... {.all.}` under it.
##
## `check_options.importedNames` (the modules an import under a push leaks the
## push into) and `importPathOf` (the import graph) read an import's path as an
## identifier, a string, `a/b`, `./a`, `a as b` or a bracket, and dropped any
## other shape (`else: discard`, `else: includePathOf(n)` which answers ""). An
## `import ./m {.all.}` is a `nnkPragmaExpr`: the leak was not recorded, so
## `importedAll` read as compiled with overflow checks on. The walk raised an
## `OverflowDefect` where the native run wraps and reaches the label: a false
## sxRaised.
## Both now see through the pragma, and an unlisted shape fails closed (the
## module's options read as unknown). With int6 (walker 477) the import under
## the push is modelled exactly rather than declined: walked with checks off,
## its overflow ends the path as `ubSignedOverflow`.
##
## Own file: the import has to be this module's first of the fixture.
{.push overflowChecks: off.}
import ./k2f3_fix_importall {.all.}
{.pop.}
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc viaImportAll(v: int) =
  if v == high(int):
    let w = importedAll(v)
    if w < 0: symexTarget("hit")

suite "K2F-3: an import {.all.} under a push":
  test "native: the imported routine runs without the check":
    check native(viaImportAll(high(int))) == "hit"
  test "modelled exactly: the import is walked off, its overflow is undefined":
    # int6 (walker 477, compile-order replay) models an import made under a
    # push exactly, so it is no longer declined with `feOverflowCheckOption`.
    # The routine is walked with overflow checks off; its signed `+` at
    # `high(int)` is undefined in C, so the path ends there as
    # `ubSignedOverflow` (`sxUnknown`). It is never an `OverflowDefect`
    # (`sxRaised`): native runs the routine unchecked too. RED was sxRaised,
    # the leak not recorded.
    let r = symexFind(viaImportAll, tLabel("hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.status != sxRaised
    check not r.errors.named(feOverflowCheckOption)
    check r.errors.named(ubSignedOverflow)

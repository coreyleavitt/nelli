## RFC-0005 S8cu -- a push reaches a module first compiled by an `import` under it.
##
## S8cu declined both routines of the imported module (`feOverflowCheckOption`).
## RFC-0016 int6 (walker 477, compile-order replay) models the import exactly:
## the fixture is first compiled here, under `overflowChecks: off`, so its
## plain routine is walked unchecked (its overflow is `ubSignedOverflow`, as in
## `tsymex_0016_k2f3_importall`), and the routine under its own
## `{.push overflowChecks: on.}` is walked checked and raises `OverflowDefect`.
##
## Own file: the import has to be this module's first of the fixture.
{.push overflowChecks: off.}
import ./s8cu_fix_imported
{.pop.}
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_helpers

const declKey = cellKey(faGeneric, "s8cu_import")

proc viaImported(v: int) =
  if v == high(int):
    let w = importedPlain(v)
    if w < 0: symexTarget("hit")

proc viaImportedOn(v: int) =
  if v == high(int):
    let w = importedOn(v)
    if w < 0: symexTarget("hit")

proc notCallingIt(v: int) =
  if v == 7: symexTarget("hit")

suite "S8cu: an import under a push":

  test "the imported routine runs without the check: walked off, its overflow undefined":
    # int6 (walker 477): the import under the push is modelled exactly, no
    # longer declined with `feOverflowCheckOption`. Walked with overflow
    # checks off, its signed `+` at `high(int)` is undefined in C: the path
    # ends there as `ubSignedOverflow` (`sxUnknown`), never an
    # `OverflowDefect` (`sxRaised`), since native runs it unchecked too.
    check native(viaImported(high(int))) == "hit"
    let r = symexFind(viaImported, tLabel("hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.status != sxRaised
    check not r.errors.named(feOverflowCheckOption)
    check r.errors.named(ubSignedOverflow)

  test "a routine of its own under `on` keeps it: modelled per position, raises":
    # int6 (walker 477): the fixture's own `{.push overflowChecks: on.}` is
    # read on top of the state the import compiled it from, so the routine is
    # walked checked and its overflow raises, judged natively (`pinFind`).
    check native(viaImportedOn(high(int))) == "OverflowDefect"
    let r = pinFind(viaImportedOn, tLabel("hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxRaised
    check r.trusted
    check r.raisedTypeId == "OverflowDefect"

  test "the importer's own routine after the pop decides (control)":
    check native(notCallingIt(7)) == "hit"
    decides(notCallingIt, sxSat)

## RFC-0005 S8cu -- a push reaches a module first compiled by an `import` under it.
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

  test "the imported routine runs without the check, and declines":
    check native(viaImported(high(int))) == "hit"
    pinDecline(viaImported, declKey, feOverflowCheckOption)

  test "a routine of its own under `on` keeps it; not modelled per position":
    # Native: raises. The walk declines as well: past a leak it reads the module as
    # the importer left it, on top of what its own text says.
    check native(viaImportedOn(high(int))) == "OverflowDefect"
    pinDecline(viaImportedOn, declKey, feOverflowCheckOption)

  test "the importer's own routine after the pop decides (control)":
    check native(notCallingIt(7)) == "hit"
    decides(notCallingIt, sxSat)

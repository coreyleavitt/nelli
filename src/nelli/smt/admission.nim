## RFC-0016 §8.1 -- admission, first slice (K9a): the cell identity.
##
## A `CellKey` names one thing the universe ledger classifies: a scope and the
## rendered discriminant the code actually reads. Identity carries no file or
## line, so a refactor does not churn it. This module is Z3-free and imports
## nothing from the walker; the `Admit`/`Row`/`AxisTable` machinery lands in
## ADM-1 beside it.
##
## `cellKey` is the unchecked constructor. Each axis's introducing slice adds
## a checked one (`magic("DivU")` is a `static` lookup) and the pins retype to
## it with no change to `render`.
import std/options

type
  Scope* = enum                         ## what a cell belongs to
    axConstruct, axTypeClass, axTypeOp, axPragma, axMagic, axStdlibBody,
    axBuild, axReadOnly, axDefinedness,             # admission axes
    faCallShape, faExnMemory, faGeneric             # test-side pin families
  Axis* = range[axConstruct .. axDefinedness]
  CellKey* = object                     ## identity: (scope, rendered key)
    scope*: Scope
    key*: string

const scopePrefix*: array[Scope, string] = [
  axConstruct: "construct", axTypeClass: "typeclass", axTypeOp: "typeop",
  axPragma: "pragma", axMagic: "magic", axStdlibBody: "stdlib",
  axBuild: "build", axReadOnly: "readonly", axDefinedness: "defined",
  faCallShape: "family:callshape", faExnMemory: "family:exnmemory",
  faGeneric: "family:generic"]
  ## The text a scope renders as. No prefix followed by `:` is a prefix of
  ## another, so `parseCellKey` is unambiguous even when a key holds `:`.

func cellKey*(scope: Scope; key: static string): CellKey =
  ## The unchecked constructor: any non-empty static string names a cell.
  static: doAssert key.len > 0, "a CellKey needs a non-empty key"
  CellKey(scope: scope, key: key)

func render*(k: CellKey): string =
  ## The one canonical text form, `<scope>:<key>` (`magic:DivU`,
  ## `family:callshape/<shape>`). The pin record and the work list store it.
  scopePrefix[k.scope] & ":" & k.key

func parseCellKey*(s: string): Option[CellKey] =
  ## Inverse of `render`: `none` for a scope that does not exist or an empty
  ## key, so a typo in a rendered key fails instead of naming nothing.
  for sc in Scope:
    let p = scopePrefix[sc] & ":"
    if s.len > p.len and s[0 ..< p.len] == p:
      return some(CellKey(scope: sc, key: s[p.len .. ^1]))
  none(CellKey)

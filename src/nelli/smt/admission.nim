## RFC-0016 §8.1 -- admission, first slice (K9a): the cell identity.
##
## A `CellKey` names one thing the universe ledger classifies: a scope and the
## rendered discriminant the code actually reads. Identity carries no file or
## line, so a refactor does not churn it. This module is Z3-free and imports
## nothing from the walker. ADM-1 adds the generic machinery beside it:
## `Row`, `AxisTable` and `Admit`. An axis is a site enum, a `const`
## `AxisTable` and a verb that returns an `Admit`; the verb lives with the
## payload type it returns (`pcre_engine.admitPcreLib`,
## `dsl_parser.admitVarMagic`), because the payload types are not importable
## from here.
##
## `cellKey` is the unchecked constructor. Each axis's introducing slice adds
## a checked one (`magic("DivU")` is a `static` lookup) and the pins retype to
## it with no change to `render`.
import std/options
import ./errorkind

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

# ---------------------------------------------------------------------------
# ADM-1: rows, tables and the proof.
# ---------------------------------------------------------------------------

type
  Intent* = enum                        ## ledger only: declined for now vs stays
    iModel, iNever
  NeverReason* = enum                   ## ledger only; read when `iNever`
    nrTheory, nrBudget, nrPlatform, nrUnobservable, nrByDesign

  Row*[S: enum; P] = object
    ## One cell's answer. Callers never read a row: they ask the axis's verb
    ## for an `Admit`. An admitted row is admitted at the `sites` it names;
    ## at any other site it declines with `elsewhere` (a site that models
    ## the cell only partly, `feUnsupportedOp` at `ensureProcRegistered`).
    note: string
    case admitted: bool
    of true:
      payload: P
      sites: set[S]
      elsewhere: Option[SymexErrorKind]
    of false:
      kind: Option[SymexErrorKind]      ## `none`: the axis reports in its own
                                        ## vocabulary (PCRE's `psUnknown`)
      intent: Intent
      never: NeverReason

  AxisTable*[S: enum; P] = object
    ## Keys are strings: both first consumers key on text (a magic's name; a
    ## library's `version|engine`), so the RFC's `K` parameter is not needed.
    ## A seq searched linearly, not a `Table`: the tables are `const`, read
    ## in the macro VM, and have under twenty rows.
    axis: Axis
    rows: seq[tuple[key: string, row: Row[S, P]]]

  Admit*[P] = object
    ## A proof, constructible only here. `ok` is the answer; the rest says
    ## which cell it was about and, on a decline, what to report.
    ok: bool
    payload: P
    kind: Option[SymexErrorKind]
    reason: string
    cell: CellKey

func modelled*[S: enum; P](payload: P; sites: set[S]; note: string;
                           elsewhere = some(feUnadmitted)): Row[S, P] =
  ## An admitted row. `sites` must not be empty: a row admitted nowhere is a
  ## `refused` one.
  doAssert sites != {}, "a modelled row names at least one site"
  Row[S, P](admitted: true, note: note, payload: payload, sites: sites,
            elsewhere: elsewhere)

func refused*[S: enum; P](kind: Option[SymexErrorKind]; note: string;
                          intent = iModel;
                          never = nrByDesign): Row[S, P] =
  ## A declined row: `kind` is what a consumer reports, `note` why.
  Row[S, P](admitted: false, note: note, kind: kind, intent: intent,
            never: never)

func axisTable*[S: enum; P](axis: Axis;
    rows: openArray[tuple[key: string, row: Row[S, P]]]): AxisTable[S, P] =
  ## The one constructor. A duplicate or empty key does not compile into a
  ## `const`.
  result.axis = axis
  for r in rows:
    doAssert r.key.len > 0, "an AxisTable key is non-empty"
    for o in result.rows:
      doAssert o.key != r.key, "duplicate AxisTable key " & r.key
    result.rows.add r

func cellOf*[S: enum; P](t: AxisTable[S, P]; key: string): CellKey =
  CellKey(scope: t.axis, key: key)

func admit*[S: enum; P](t: AxisTable[S, P]; key: string; site: S;
    absent = some(feUnadmitted)): Admit[P] =
  ## The lookup. A key with no row is a decline of kind `absent`
  ## (`feUnadmitted`, or the axis's own: `none`); so is an admitted row at a
  ## site it does not name, and a refused row. Every decline names its cell.
  let cell = t.cellOf(key)
  let head = render(cell) & ": "
  for r in t.rows:
    if r.key != key: continue
    if r.row.admitted:
      if site in r.row.sites:
        return Admit[P](ok: true, payload: r.row.payload, cell: cell)
      return Admit[P](ok: false, payload: r.row.payload,
                      kind: r.row.elsewhere, cell: cell,
                      reason: head & r.row.note)
    return Admit[P](ok: false, kind: r.row.kind, cell: cell,
                    reason: head & r.row.note)
  Admit[P](ok: false, kind: absent, cell: cell,
           reason: head & "no row in the " & scopePrefix[t.axis] &
                   " table (absent is a decline)")

iterator keys*[S: enum; P](t: AxisTable[S, P]): string =
  for r in t.rows: yield r.key

iterator keysAt*[S: enum; P](t: AxisTable[S, P]; site: S): string =
  ## Every key whose row is admitted at `site`: what a generated dispatch
  ## compares its arms against (K4a-dispatch).
  for r in t.rows:
    if r.row.admitted and site in r.row.sites: yield r.key

func hasRow*[S: enum; P](t: AxisTable[S, P]; key: string): bool =
  for r in t.rows:
    if r.key == key: return true

iterator cells*[S: enum; P](t: AxisTable[S, P]):
    tuple[cell: CellKey, admitted: bool, intent: Intent] =
  ## What K1 reads: every row's identity and whether it models the cell.
  for r in t.rows:
    yield (t.cellOf(r.key), r.row.admitted,
           (if r.row.admitted: iModel else: r.row.intent))

func admitted*[P](a: Admit[P]): bool = a.ok
func cell*[P](a: Admit[P]): CellKey = a.cell
func payload*[P](a: Admit[P]): P =
  ## The row's payload. Defined for an admitted row, and for a row admitted
  ## at another site (a decline that still says what the cell is); not for
  ## an absent key.
  a.payload
func decline*[P](a: Admit[P]): (Option[SymexErrorKind], string) =
  ## The kind to report (`none`: the axis's own vocabulary) and the reason,
  ## which names the cell.
  doAssert not a.ok, "decline of an admitted cell"
  (a.kind, a.reason)

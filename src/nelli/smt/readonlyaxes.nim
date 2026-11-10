## RFC-0016 E3 (section 8.1) -- the read-only axis.
##
## One `AxisTable` over the ADM-1 machinery, keyed `<route>/<shape>` on the
## `readonly:` scope. K6 built one rule behind four parser predicates: "may this
## node write memory no variable of the routine names" (`mayWrite`), and the
## three routes that ask it of a body (`mayWriteRoot` for the `for` variable
## that holds a container's memory, `routeStoresThroughDeref` and
## `routeHookCopies` for a lifetime hook) plus the escape and aliasing
## questions that share its facts (`ptrUsesStayLocal`, `bindsViewWhole`). A cell
## here is one write SHAPE a route decides:
##
## * a modelled cell is a shape the route proves read-only (or a pointer that
##   stays local, a copy that is the plain one), so the walk decides it;
## * a refused cell is a shape the route cannot prove, so the walk declines
##   with the kind the route reports.
##
## The table is a ledger: the predicates are node-kind allowlists that are not
## asked per cell, so the rows are evidenced by the K6 corpus (each SUT pins its
## shape's cell through `pinExact` or `pinDecline`) rather than read by a
## consumer. `tsymex_0016_universe` joins them.
import std/options
import ./admission
import ./errorkind

type
  ReadOnlySite* = enum
    rsLentBody      ## the body of a `for` over a container, `mayWriteRoot`
    rsHookCopy      ## a lifetime hook's `=copy`, `routeHookCopies`
    rsHookStore     ## a lifetime hook's stores, `routeStoresThroughDeref`
    rsPtrFormal     ## a `ptr` formal's uses, `ptrUsesStayLocal`
    rsViewWhole     ## a callee holding a container's memory, `bindsViewWhole`
  ReadOnlyModel* = enum
    rmReadOnly      ## proved to write nothing shared
  ReadOnlyKey = tuple[key: string, row: Row[ReadOnlySite, ReadOnlyModel]]

func proved(site: ReadOnlySite; names: openArray[string]; why: string):
    seq[ReadOnlyKey] =
  for n in names:
    result.add (n, modelled[ReadOnlySite, ReadOnlyModel](
                  rmReadOnly, {site}, why))

func may(kind: SymexErrorKind; names: openArray[string]; why: string):
    seq[ReadOnlyKey] =
  for n in names:
    result.add (n, refused[ReadOnlySite, ReadOnlyModel](some(kind), why))

func readOnlyRows(): seq[ReadOnlyKey] =
  # --- lent/: the body of a `for` over a container (K6a, W-08) ---------------
  result.add proved(rsLentBody,
    ["lent/walked-pure", "lent/local-work", "lent/global-read",
     "lent/pragma-block"],
    "proved read-only: a walked pure callee, local scalar work, a read of " &
    "the container or of another global, a `doAssert`'s pragma block")
  result.add may(feUnsupportedOp,
    ["lent/deref-store", "lent/var-formal", "lent/stdlib-pointer-arg",
     "lent/cast-emit", "lent/walked-write", "lent/recursive-write",
     "lent/opaque-callee", "lent/recursive-pure"],
    "the body may write the container's memory through a pointer: a store, " &
    "a `var` formal fed a dereference, a stdlib routine given a pointer, " &
    "foreign code, a callee that writes, an opaque one, or a cycle (which " &
    "defaults to may-write)")
  result.add may(feUnsupportedOp, ["lent/proc-value"],
    "a proc value may write anything; the by-name scan declines it")
  # --- hookcopy/: a user `=copy` (K6b, W-09) ---------------------------------
  result.add proved(rsHookCopy,
    ["hookcopy/plain", "hookcopy/local-work", "hookcopy/walked-pure"],
    "the hook's top-level field copy is the plain copy, with work around it " &
    "that writes nothing shared")
  result.add may(feGlobalRouteUnproved,
    ["hookcopy/conditional", "hookcopy/early-return", "hookcopy/callee-write",
     "hookcopy/foreign-write", "hookcopy/loop"],
    "the hook's copy is not a top-level statement, or leaves the hook, or " &
    "something after it writes the destination: not the plain copy")
  # --- hookstore/: a hook storing through a ref or ptr (K6c, W-10) -----------
  result.add proved(rsHookStore, ["hookstore/plain", "hookstore/local-work"],
    "the hook stores nothing through a `ref` or a `ptr`")
  result.add may(feGlobalRouteUnproved,
    ["hookstore/direct-store", "hookstore/walked-store"],
    "the hook, or a walked callee of it, may store through a `ref` or a `ptr` " &
    "at a call the compiler inserts")
  # --- ptrformal/: a `ptr` formal's uses (K6c, W-10) -------------------------
  result.add proved(rsPtrFormal, ["ptrformal/local", "ptrformal/global-store"],
    "every use of the pointer stays local to the call; a pointer stored in a " &
    "global is an escape the walk decides")
  result.add may(feUnsupportedExprKind,
    ["ptrformal/field-addr", "ptrformal/var-return"],
    "the address of a pointee's field, or of a pointee passed `var` to a " &
    "callee returning its address, outlives the call: not decided")
  # --- viewwhole/: a callee holding a container's memory (K6c, W-10) ---------
  result.add proved(rsViewWhole, ["viewwhole/tuple-copy"],
    "a tuple built from the container is a copy of it, not a view")
  result.add may(feTableIterOrder, ["viewwhole/scalar-read"],
    "a scalar read out of the container is no view and the route lets it " &
    "through, but the pinned shape iterates `Table.mpairs`, whose order is " &
    "not modelled: the verdict is sat and untrusted")
  result.add may(feUnsupportedOp, ["viewwhole/var-copy", "viewwhole/lent-loop"],
    "a `var` copy of the whole, or a `lent` loop over it, holds the " &
    "container's memory")

func buildTable(): AxisTable[ReadOnlySite, ReadOnlyModel] =
  axisTable[ReadOnlySite, ReadOnlyModel](axReadOnly, readOnlyRows())

const readOnlyAxis* = buildTable()

func admitReadOnly*(key: string; site: ReadOnlySite): Admit[ReadOnlyModel] =
  ## Whether the shape `key` is proved read-only at `site`. An unknown key
  ## declines `feUnadmitted`.
  readOnlyAxis.admit(key, site)

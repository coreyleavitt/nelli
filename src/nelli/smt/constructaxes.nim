## RFC-0016 E2b (section 8.1) -- the construct axis, its pinned subset.
##
## The RFC's section 8.1 census plus the child-shape corpus (section 12, about
## 250 cells) is this axis's long-term content: every syntactic construct the
## walker lowers, and every shape a child of one takes. This table is its
## CURRENT, PINNED subset -- the `construct:*` keys that K8a, K8a-gen, K20, K7a
## and the W1 slices already file their records under -- so the axis has cells
## the universe test derives and the existing records evidence, instead of
## orphan records no table names. It grows toward the census by adding rows;
## a row with no record on a leg fails the universe join there.
##
## * a modelled cell is a construct the walk decides, pinned `pinExact` (or a
##   raise the native run reproduces);
## * a refused cell is a construct the walk declines (`pinDecline`), crashes
##   natively (`pinCrash`) or is cut by a cap (`pinCap`), with the kind its
##   pins record.
##
## Not asked per cell: these constructs have NO single decision point. A slice
## test `x in a..b` is lowered where the parser rewrites `contains` on a range,
## a conversion in `convertFloatWidth`, a handler's `as e` in the try lowering,
## a cap where the runtime counts the budget it halts on -- different parsers,
## walkers and counters. So the table is a ledger (as the readonly axis was
## before E3b), joined to its records by `tsymex_0016_universe`.
##
## Recorded but not cells, because no record can evidence them on a leg: the
## two `=trace`/`=destroy` hook keys are walker faults (`coerceIntLit`, P6) and
## a fault is not a decline, and `quit/afterTarget/assertCoveredBy` is a clean
## `sxSat` whose host ends at the splat (INT-22: a harness hazard, not a
## verdict); each stays a `skipCell` in `tsymex_0016_k20_probes*`.
import std/options
import ./admission
import ./errorkind

type
  ConstructSite* = enum
    csLowering      ## the construct as the walk lowers it
  ConstructModel* = enum
    cmDecided       ## the walk's verdict on this construct is what native does
  ConstructKey = tuple[key: string, row: Row[ConstructSite, ConstructModel]]

func decided(names: openArray[string]; why: string): seq[ConstructKey] =
  for n in names:
    result.add (n, modelled[ConstructSite, ConstructModel](
                  cmDecided, {csLowering}, why))

func declines(kind: Option[SymexErrorKind]; names: openArray[string];
              why: string): seq[ConstructKey] =
  for n in names:
    result.add (n, refused[ConstructSite, ConstructModel](kind, why))

func constructRows(): seq[ConstructKey] =
  result.add decided(
    ["k8a-gen/DivLit", "k8a-gen/Udiv", "k8a-gen/Ovf", "k8a-gen/Neg",
     "k8a-gen/F32", "k8a-gen/Except"],
    "K8a-gen (section 10): a generated program of the shape and its " &
    "metamorphic twins agree with the native run")
  result.add decided(
    ["except-as-label", "except-as-raise", "except-plain-label", "raise-let-value",
     "k8a1-plain", "k8a1-as", "k8a1-nested", "k8a1-module", "k8a1-iter"],
    "an `except T as e` handler, a plain one, a raise of a `let` value, and " &
    "the same handlers through a template, a nested try, a module-level " &
    "try and an iterator")
  result.add decided(
    ["nopanic-catch-defect", "nopanic-defect-not-escaping",
     "nopanic-finally-defect",
     "mitems/int16/assertionsOff"],
    "a build with panics or assertions off: a Defect is catchable, a " &
    "`finally` runs, an unchecked write is the native one")
  result.add decided(
    ["block/break/nested", "block/break/forLoopLabel", "stmtListExpr/ifCase",
     "drain/argOrder", "drain/tryNestedProc"],
    "control flow and evaluation order: a labelled break, a statement-list " &
    "expression, the argument drain order, a nested try in a proc")
  result.add decided(
    ["blockExpr/tail", "blockExpr/scoped", "blockExpr/labelled",
     "blockExpr/afterBreak"],
    "a `block` used as an expression (W3-z P14): lowered as a statement-list " &
    "expression in its own scope, labelled or not, and after a `break` out " &
    "of an earlier block statement")
  result.add declines(some(feUnsupportedExprKind), ["blockExpr/breakOut"],
    "a `break` out of a block expression leaves its value unevaluated, which " &
    "the lowering does not model (W3-z P14)")
  result.add decided(
    ["for/inlineIter/break", "for/inlineIter/continue",
     "for/inlineIter/labelledBreak"],
    "a `break`, `continue` or labelled `break` in the body of a `for` over " &
    "an inline iterator: it leaves the whole expansion, resumes after the " &
    "current `yield`, or leaves the labelled block (W3-z P13)")
  result.add decided(
    ["for/countup", "for/countdown"],
    "`for i in countup(a, b[, step])` / `countdown` over an `int`-like " &
    "counter, modelled by the `for` arm beside `..`: bounds and step read " &
    "once, a step below 1 raises `RangeDefect` (W3-z P15)")
  result.add decided(
    ["for/dotdot/boundOnce"],
    "a `..` / `..<` (or counting iterator) bound that is not a symbol is " &
    "evaluated once, before the loop (W3-z P17)")
  result.add decided(
    ["for/counter/unsigned", "for/counter/narrowSigned"],
    "a loop counter of `..`, `..<`, `countup` or `countdown` is held in its " &
    "own type: an unsigned one wraps, an `int8`/`int16`/`int32` one " &
    "overflows at its own width (W3-z P17, P18)")
  result.add decided(
    ["case/elif/chain", "case/elif/chainElse", "case/elif/expr",
     "case/elif/exprCond", "case/elif/hoisted", "case/elif/orderExpr", "case/elif/orderStmt",
     "case/elif/stmt"],
    "a `case` with `elif` branches, as a statement and as an expression")
  result.add decided(
    ["conv/float32<-float64", "conv/float64<-float32/arg",
     "conv/float64<-float32/var", "conv/float64<-int", "conv/int<-float64"],
    "a float width or int/float conversion, explicit or inserted by the " &
    "compiler (`convertFloatWidth`)")
  result.add decided(
    ["in/slice/char", "in/slice/enum", "in/slice/empty", "in/slice/enum/out", "in/slice/excl",
     "in/slice/excl/unsat", "in/slice/excl/var", "in/slice/excl/var/lowRaise",
     "in/slice/excl/var/u8", "in/slice/excl/var/u8/raise", "in/slice/int", "in/slice/int/unsat",
     "in/slice/int/upper", "in/slice/uint8", "in/slice/uint8/hi",
     "in/slice/varbounds", "notin/slice/char", "notin/slice/enum",
     "notin/slice/int", "notin/slice/int/unsat"],
    "`x in a..b` and `x notin a..b` over int, uint8, char and enum bounds, " &
    "closed and half-open, literal and variable")
  result.add declines(some(eeUnknownExnType),
    ["panic-raise-unknown", "raise-ref-exception", "raise-value-subtype"],
    "a raise whose exception type is not statically known (a `ref " &
    "Exception` value, a subtype of the declared type, a raised parameter)")
  result.add declines(some(feOpaqueCallUnmodelled), ["signals/handler"],
    "a signal handler is registered through a foreign call the walk cannot " &
    "model")
  result.add declines(some(feUncheckedDiscBytes), ["uncheckedAssign/diff"],
    "a discriminator written under an unchecked assignment reinterprets the " &
    "object's bytes")
  # --- cap/: a run cut by a budget (`pinCap`, K7a): the kind its one producing
  # site reports, which `capExpectation` (s8cu_helpers) states per member.
  result.add declines(some(beBudgetExhausted), ["cap/ckLoopUnwind"],
    "the while-loop k-unroll budget is exhausted")
  result.add declines(some(beBudgetExhaustedUnmodelled), ["cap/ckCallDepth"],
    "the call-inlining depth budget is exhausted")
  result.add declines(some(beBudgetExhaustedPrune),
    ["cap/ckFrontier", "cap/ckWalkWork"],
    "the path frontier or the walk work cap prunes the run")
  result.add declines(some(feUnsupportedOp), ["threads/createThread"],
    "`createThread` declines at the call by its stdlib `never` row")
  result.add declines(some(feUnsupportedOpHavoc), ["cap/ckTermWalkRead"],
    "an array read wider than the term walk's cap")
  result.add declines(some(feUnsupportedStmtKind), ["cap/ckTermWalkWrite"],
    "an array write wider than the term walk's cap")
  result.add declines(none(SymexErrorKind), ["panic-overflow-defect"],
    "an uncaught overflow Defect ends the process natively (`pinCrash`): " &
    "no verdict names it")

func buildTable(): AxisTable[ConstructSite, ConstructModel] =
  axisTable[ConstructSite, ConstructModel](axConstruct, constructRows())

const constructAxis* = buildTable()

func admitConstruct*(key: string): Admit[ConstructModel] =
  ## Whether the construct `key` is decided. An unknown key declines
  ## `feUnadmitted`.
  constructAxis.admit(key, csLowering)

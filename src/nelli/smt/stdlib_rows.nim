## RFC-0016 K4c (section 8.1) -- the stdlib-body axis: one row per stdlib
## routine, type or facet the walker treats specially, keyed by
## `<module>.<name>` (`math.floorDiv`, `system.+%`, `tables.OrderedTable`) or
## `<module>.<name>/<facet>` (`sets.HashSet/iterationOrder`). Z3-free; imports
## the admission machinery, the error kinds and the check-option vocabulary.
##
## What a row says, by site:
##   * `ssBodyWalk`: the routine is walked by its Nim body, and the row carries
##     its CHECK-OPTION DELTA: `exercises`, the checks the body's operations can
##     trip. A stdlib routine's options are not the SUT's: `math.nim` pushes
##     `checks: off` over nearly all of std/math (PRC-09), so a routine there
##     runs unchecked in a build that checks. The walker reads the module's
##     push (`check_options.routineChecks`) and the row together:
##       - an option the push turns off that the body does not exercise changes
##         nothing, and is no deviation;
##       - `overflowChecks` (which Nim's zero-divisor check belongs to) that the
##         body exercises is modelled: the body is walked under the unchecked
##         arithmetic (`asUnchecked`, signed overflow and `x div 0` are
##         `ArithTrap`s), the same model a `--overflowChecks:off` build gets;
##       - any other option the push turns off AND the body exercises, and any
##         routine with no row, declines (`feCheckOption`) as before.
##     The row is read only for a routine whose options deviate from the model:
##     a routine with no deviation is walked, row or no row.
##   * `ssCallSwitch`, `ssInfix`: the unsigned operators (`+%` ...) are `system`
##     routines over `cast[uint]`, not magics. A hand-written arm models them
##     (`parseUnsignedOp`); the arm is dispatched through `dispatchMagic`, which
##     checks it against this table (K4a-dispatch moved them here).
##   * `ssType`: the type bridge's catch-all for a stdlib generic object
##     (W-47). A row names the heads that decline; any other stdlib generic
##     object is the table's absent case, with the same kind.
##   * `ssFacet`: a property of a stdlib routine the walker cannot model,
##     refused `iNever` with the reason (STY-02, STY-06, AUD-11). The site that
##     declines because of it names the cell.
import std/options
import ./admission
import ./errorkind
import ./buildprofile

type
  StdlibSite* = enum
    ssBodyWalk    ## `parseCalleeImpl`: the routine is walked by its body
    ssCallSwitch  ## the stdlib call switch (`dispatchMagic` site)
    ssInfix       ## the unsigned operators spelled infix (`dispatchMagic` site)
    ssType        ## `classifyType`'s catch-all for a stdlib generic object
    ssFacet       ## a property the walker declines; the declining site names it

  StdlibBody* = object
    exercises*: set[CheckOption]
      ## The checks the routine's body can trip (its check-option delta).
      ## Empty for a row that is not walked by body.

  StdlibRow = tuple[key: string, row: Row[StdlibSite, StdlibBody]]

func walked(key, note: string; exercises: set[CheckOption]): StdlibRow =
  (key, modelled[StdlibSite, StdlibBody](StdlibBody(exercises: exercises),
                                          {ssBodyWalk}, note,
                                          elsewhere = some(feUnsupportedOp)))

func unsignedOp(key, note: string): StdlibRow =
  (key, modelled[StdlibSite, StdlibBody](StdlibBody(), {ssCallSwitch, ssInfix},
                                          note,
                                          elsewhere = some(feUnsupportedOp)))

func declinedType(key, note: string): StdlibRow =
  (key, refused[StdlibSite, StdlibBody](some(feUnsupportedParamType), note))

func neverFacet(key, note: string; why: NeverReason;
                kind = feUnsupportedOp): StdlibRow =
  (key, refused[StdlibSite, StdlibBody](some(kind), note, intent = iNever,
                                         never = why))

const ovf = {coOverflow}

const stdlibAxis* = axisTable[StdlibSite, StdlibBody](axStdlibBody, [
  # PRC-09. std/math pushes `checks: off` from math.nim:157. Each body below
  # is integer arithmetic: the only check it can trip is `overflowChecks`
  # (the signed `-`, `+`, `div`, `mod` and `dec`, and the zero divisor).
  walked("math.isPowerOfTwo",
    "math.nim:324: `(x > 0) and ((x and (x - 1)) == 0)`; `x - 1` is the only " &
    "signed operation", ovf),
  walked("math.floorDiv",
    "math.nim:860: `x div y`, `x mod y`, `result.dec 1`: overflow and the " &
    "zero divisor", ovf),
  walked("math.floorMod",
    "math.nim:880: `x mod y`, `result += y`: overflow and the zero divisor",
    ovf),
  walked("math.euclDiv",
    "math.nim:897: `x div y`, `x mod y`, `dec`/`inc result`: overflow and " &
    "the zero divisor", ovf),

  # K4a-dispatch noted these are `system` routines, not magics. Their arm is
  # unchanged (`parseUnsignedOp`); the rows moved here from `magicAxis`.
  unsignedOp("system.+%",
    "`+%` (system/arithmetics.nim): a `system` routine over `cast[uint]`; " &
    "add on the operands as unsigned (S8cb, `parseUnsignedOp`)"),
  unsignedOp("system.-%",
    "`-%` (system/arithmetics.nim): a `system` routine over `cast[uint]`; " &
    "subtract on the operands as unsigned (S8cb, `parseUnsignedOp`)"),
  unsignedOp("system.*%",
    "`*%` (system/arithmetics.nim): a `system` routine over `cast[uint]`; " &
    "multiply on the operands as unsigned (S8cb, `parseUnsignedOp`)"),
  unsignedOp("system./%",
    "`/%` (system/arithmetics.nim): a `system` routine over `cast[uint]`; " &
    "divide on the operands as unsigned (S8cb, `parseUnsignedOp`)"),
  unsignedOp("system.%%",
    "`%%` (system/arithmetics.nim): a `system` routine over `cast[uint]`; " &
    "remainder on the operands as unsigned (S8cb, `parseUnsignedOp`)"),
  unsignedOp("system.<%",
    "`<%` (system/arithmetics.nim): a `system` routine over `cast[uint]`; " &
    "less-than on the operands as unsigned (S8cb, `parseUnsignedOp`)"),
  unsignedOp("system.<=%",
    "`<=%` (system/arithmetics.nim): a `system` routine over `cast[uint]`; " &
    "less-or-equal on the operands as unsigned (S8cb, `parseUnsignedOp`)"),

  # W-47 (B-11, HRV-62). The stdlib generic objects the type bridge declines,
  # by row instead of by the bare catch-all. Open precision (`iModel`).
  declinedType("options.Option",
    "a stdlib generic object: its fields are not read (`userGenericObjectImpl` " &
    "refuses a stdlib declaration)"),
  declinedType("tables.OrderedTable",
    "a stdlib generic object: its hash-table layout is not modelled"),
  declinedType("tables.CountTable",
    "a stdlib generic object: its hash-table layout is not modelled"),
  declinedType("deques.Deque",
    "a stdlib generic object: its ring buffer is not modelled"),

  # STY-02 (C-13): iteration order is the hash order, which depends on the
  # build (Nim version, `-d:nimStringHash2`, `-d:nimPreviewHashRef`).
  neverFacet("tables.Table/iterationOrder",
    "native order is hash order, build-sensitive; the walker enumerates one " &
    "order, stamps `feTableIterOrder` and is trusted only after in-process " &
    "replay", nrPlatform, feTableIterOrder),
  neverFacet("sets.HashSet/iterationOrder",
    "native order is hash order, build-sensitive; iteration over a HashSet " &
    "declines", nrPlatform, feUnsupportedStmtKind),

  # AUD-11 (S8au, S8aw): the `L`-against-`indexof` link covers native terms
  # only; `find`/`rfind` no longer emit `seq.last_indexof` or `str.indexof`.
  # A coverage note, not a decline: `rfind` is decided (pinned exact).
  neverFacet("strutils.rfind/indexofLink",
    "the S8aw link between `L` and `indexof` covers native terms only; the " &
    "walker emits neither `seq.last_indexof` nor `str.indexof` for `rfind` " &
    "and `find`; a coverage note, no wrong verdict", nrByDesign),

  # STY-06: what the walker cannot model of the stdlib, one `never` cell each.
  neverFacet("algorithm.sort/symbolicLength",
    "sorting a symbolic-length sequence has no closed form in the theory " &
    "(HRV-105); `sort`'s `order = Ascending` formal also declines as a " &
    "generated hook", nrTheory),
  neverFacet("typedthreads.createThread/concurrency",
    "concurrency inside the SUT: a second thread's interleaving is not a " &
    "path the walker enumerates (HRV-105); `createThread` is a walker fault " &
    "today (W-19b)", nrTheory),
  neverFacet("unicode.toLower/fullCaseFold",
    "full Unicode case folding is not modelled (HRV-105); the string model " &
    "is byte-faithful (Cluster S)", nrTheory)])

proc admitStdlibBody*(key: string; site: StdlibSite;
                      absent = some(feUnadmitted)): Admit[StdlibBody] =
  ## The stdlib-body axis, for every key. `absent` is what a key with no row
  ## declines with.
  stdlibAxis.admit(key, site, absent)

proc facetNote*(key: string): string =
  ## The reason text of a refused facet row, which names its cell
  ## (`stdlib:sets.HashSet/iterationOrder: ...`): what a decline appends.
  admitStdlibBody(key, ssFacet).decline[1]

const stdlibDispatchSites* = {ssCallSwitch, ssInfix}
  ## The sites whose `case` goes through `dispatchMagic`.

func unsignedOpKey*(arm: string): string = "system." & arm
  ## The row key of a `dispatchMagic` arm that names a `system` routine.

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
import ./stdlib_ledger

type
  StdlibSite* = enum
    ssBodyWalk    ## `parseCalleeImpl`: the routine is walked by its body
    ssCallSwitch  ## the stdlib call switch (`dispatchMagic` site)
    ssInfix       ## the unsigned operators spelled infix (`dispatchMagic` site)
    ssType        ## `classifyType`'s catch-all for a stdlib generic object
    ssFacet       ## a property the walker declines; the declining site names it
    ssFloatCall   ## a float-first `std/math` call, intercepted by name and
                  ## lowered by `lowerMathCall` (never walked by body)
    ssNameCall    ## an integer `std/math` call intercepted by name and
                  ## lowered by a hand-written arm (`parseCeilDiv`), never
                  ## walked by body

  StdlibBody* = object
    exercises*: set[CheckOption]
      ## The checks the routine's body can trip (its check-option delta).
      ## Empty for a row that is not walked by body.
    deltaKnown*: bool
      ## `exercises` was worked out for this body. A ledger row (the corpus's
      ## walked routines, `stdlib_ledger`) says only that the body is walked
      ## where no option deviates; under a push it keeps declining.

  StdlibRow = tuple[key: string, row: Row[StdlibSite, StdlibBody]]

func walked(key, note: string; exercises: set[CheckOption]): StdlibRow =
  (key, modelled[StdlibSite, StdlibBody](
    StdlibBody(exercises: exercises, deltaKnown: true), {ssBodyWalk}, note,
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

func floatModelled(name, note: string): StdlibRow =
  ("math." & name, modelled[StdlibSite, StdlibBody](StdlibBody(),
    {ssFloatCall}, note, elsewhere = some(feUnsupportedOp)))

func floatDeclined(names: openArray[string]; note: string): seq[StdlibRow] =
  ## One declined row per routine of a family, all with the same reason.
  for n in names:
    result.add ("math." & n, refused[StdlibSite, StdlibBody](
      some(feUnsupportedOpAborted), note))

func loweredByName(key, note: string): StdlibRow =
  (key, modelled[StdlibSite, StdlibBody](StdlibBody(), {ssNameCall}, note,
                                          elsewhere = some(feUnsupportedOp)))

func checkDeclined(key, note: string): StdlibRow =
  (key, refused[StdlibSite, StdlibBody](some(feCheckOption), note))

const ovf = {coOverflow}

const explicitRows: seq[StdlibRow] = @[
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
    "is byte-faithful (Cluster S)", nrTheory)]

# PRC-09 (RFC section 8.1). std/math pushes `checks: off` from math.nim:157 to
# its `{.pop.}` at math.nim:1116. Every routine of that region has a row. The
# integer routines are walked by body and carry their delta (above). A float
# routine is never walked by body: `mathInterception` (dsl_parser) lowers a
# call with a float first argument by name (`lowerMathCall`), so the push
# changes nothing for it; the row says whether that lowering models it.
const mathRows: seq[StdlibRow] = block:
  var r: seq[StdlibRow] = @[
    walked("math.nextPowerOfTwo",
      "math.nim:339: `x - 1`, shifts, `result += 1 + ord(x <= 0)`: overflow " &
      "(`low(int) - 1`)", ovf),
    walked("math.euclMod",
      "math.nim:912: `x mod y`, `result += abs(y)`: overflow (`abs`) and the " &
      "zero divisor", ovf),
    (key: "math.divmod", row: refused[StdlibSite, StdlibBody](
      some(feOpaqueCallUnmodelled),
      "math.nim:832: a tuple-returning generic that writes `result[0]` and " &
      "`result[1]`: the walker does not inline it (an opaque call), whatever " &
      "the push")),
    walked("math.sgn",
      "math.nim:1102: `ord(T(0) < x) - ord(x < T(0))`: the difference of two " &
      "booleans' ordinals cannot overflow", {}),
    loweredByName("math.ceilDiv",
      "math.nim:925: `((x.UT + (y.UT - 1)) div y.UT).T`, a same-width " &
      "reinterpretation and wrapping unsigned arithmetic, lowered by name " &
      "(`parseCeilDiv`), exact at every width inside its precondition; its " &
      "asserts follow `assertions` where the generic is first instantiated, " &
      "not the push, so a path outside the precondition declines " &
      "`feCheckOption`"),
    floatModelled("abs", "clears the sign bit (fp.abs), exact"),
    floatModelled("min", "fp.min, exact"),
    floatModelled("max", "fp.max, exact"),
    floatModelled("toFloat32", "a float64 -> float32 conversion, fp.to_fp in " &
      "round-nearest-even (K2b); not a std/math routine, the lowering's name"),
    floatModelled("toFloat64", "a float32 -> float64 conversion, fp.to_fp, " &
      "exact (K2b); not a std/math routine, the lowering's name"),
    floatModelled("sqrt", "IEEE sqrt (fp.sqrt, RNE), exact"),
    floatModelled("floor", "roundToIntegral toward negative, exact"),
    floatModelled("ceil", "roundToIntegral toward positive, exact"),
    floatModelled("trunc", "roundToIntegral toward zero, exact"),
    floatModelled("round",
      "roundToIntegral to nearest, ties away from zero (C `round`); the " &
      "one-argument overload only"),
    floatModelled("signbit", "the sign bit, exact"),
    floatModelled("isNaN", "fp.isNaN, exact"),
    floatModelled("copySign", "the sign of the second operand on the " &
      "magnitude of the first, exact"),
    floatModelled("classify", "FloatClass from the FP predicates, exact"),
    ("math.round/places", refused[StdlibSite, StdlibBody](
      some(feUnsupportedOpAborted),
      "`round(x, places)` is `round(x * 10^places) / 10^places` through " &
      "`pow`, which is not modelled")),
  ]
  r.add floatDeclined(["cbrt", "ln", "log10", "log2", "exp", "sin", "cos",
      "tan", "sinh", "cosh", "tanh", "arcsin", "arccos", "arctan", "arctan2",
      "arcsinh", "arccosh", "arctanh", "hypot", "pow", "erf", "erfc", "gamma",
      "lgamma"],
    "a libm function (importc): no SMT-LIB floating-point primitive models " &
    "it, so its result is not computed")
  r.add floatDeclined(["log", "cot", "sec", "csc", "coth", "sech", "csch",
      "arccot", "arcsec", "arccsc", "arccoth", "arcsech", "arccsch"],
    "a reciprocal or composition of libm functions the walker does not model")
  for name in ["isInf", "isFinite", "isNormal"]:
    r.add neverFacet("math." & name,
      "std/math on this toolchain (Nim 2.2.10) has no `" & name & "`, so no " &
      "stdlib call can name it (`compiles(" & name & "(x))` is false after " &
      "`import std/math`; the cell's native fact). A SUT routine of that name " &
      "is a user routine, which the parser walks as its own body before any " &
      "by-name lowering (`isUserCallee`); the name is not a lowering's",
      nrPlatform, feUnsupportedOpAborted)
  r.add neverFacet("math.nextafter",
    "std/math on this toolchain (Nim 2.2.10) has no `nextafter`, so no SUT " &
    "can name it (`compiles(nextafter(x, y))` is false; the cell's native " &
    "fact). The name stays recognised (`mathFpDeferredOps`) and declined: " &
    "SMT-LIB's FP theory has no next-representable-value primitive either",
    nrPlatform, feUnsupportedOpAborted)
  r.add floatDeclined(["frexp", "splitDecimal", "degToRad", "radToDeg",
      "almostEqual", "mod"],
    "a float-first call is lowered by name (`lowerMathCall`), which has no " &
    "arm for it, and its body is not walked")
  r

const stdlibAxis* = axisTable[StdlibSite, StdlibBody](axStdlibBody,
                                                      explicitRows & mathRows)

func ledgerRows(): seq[StdlibRow] =
  for k in ledgerKeys:
    if not stdlibAxis.hasRow(k):
      result.add (k, modelled[StdlibSite, StdlibBody](StdlibBody(), {ssBodyWalk},
        "in the corpus ledger (`stdlib_ledger`): walked by its body wherever " &
        "no check option deviates; its check-option delta is not worked out",
        elsewhere = some(feUnsupportedOp)))

const ledgerAxis = axisTable[StdlibSite, StdlibBody](axStdlibBody, ledgerRows())
  ## The routines the corpus walked (RFC section 8.1: the axis is seeded from a
  ## `feStdlibBodyWalked` ledger). Not part of `stdlibAxis`, whose rows are the
  ## universe's cells: a ledger row is admitted at `ssBodyWalk` only, and
  ## declines the moment a check option deviates (`deltaKnown` is false).

proc admitStdlibBody*(key: string; site: StdlibSite;
                      absent = some(feUnadmitted)): Admit[StdlibBody] =
  ## The stdlib-body axis, for every key: an explicit row first, then the
  ## ledger. `absent` is what a key in neither declines with (absent is a
  ## decline).
  if not stdlibAxis.hasRow(key) and ledgerAxis.hasRow(key):
    return ledgerAxis.admit(key, site, absent)
  stdlibAxis.admit(key, site, absent)

func hasStdlibRow*(key: string): bool =
  ## `key` is an explicit row of the axis (the ledger's rows are not).
  stdlibAxis.hasRow(key)

func floatCallKey*(op: string; nargs: int): string =
  ## The row of a float-first `std/math` call: `round(x, places)` is a facet.
  if op == "round" and nargs == 2: "math.round/places" else: "math." & op

proc admitFloatCall*(op: string; nargs: int): Admit[StdlibBody] =
  ## ADM-IR. The stdlib-body axis at `ssFloatCall` for `op`: the proof
  ## `mkMathCall` takes. A name with no row is a decline of the kind a
  ## declined float row carries (`feUnsupportedOpAborted`), as the lowering
  ## reported it before the rows covered every name it models.
  admitStdlibBody(floatCallKey(op, nargs), ssFloatCall,
                  absent = some(feUnsupportedOpAborted))

proc floatCallDecline*(op: string; nargs: int): string =
  ## PRC-09. Why a float-first call of `std/math`'s `op` declines: the reason
  ## of its row (naming the cell), or "" when it is admitted at `ssFloatCall`
  ## or has no row (`mod` on floats asks this from `lower`).
  let key = floatCallKey(op, nargs)
  if stdlibAxis.hasRow(key):
    let adm = admitStdlibBody(key, ssFloatCall)
    if not adm.admitted: return adm.decline[1]

proc facetNote*(key: string): string =
  ## The reason text of a refused facet row, which names its cell
  ## (`stdlib:sets.HashSet/iterationOrder: ...`): what a decline appends.
  admitStdlibBody(key, ssFacet).decline[1]

const callDeclines*: array[2, tuple[routine, facet: string]] = [
  ## The routines whose CALL declines by a `never` facet's name, before the
  ## body is registered (`ensureProcRegistered`): STY-06's full Unicode case
  ## fold and concurrency. A walked body here would either not end
  ## (`toLower`: a binary search over the case tables) or fault the walker
  ## (`createThread`, W-19b).
  ("unicode.toLower", "unicode.toLower/fullCaseFold"),
  ("typedthreads.createThread", "typedthreads.createThread/concurrency")]

static:
  for d in callDeclines:
    doAssert stdlibAxis.hasRow(d.facet), "callDeclines names a missing facet " & d.facet

proc admitNameCall*(routineKey: string): Admit[StdlibBody] =
  ## RFC-0016 PRC-09. The stdlib-body axis at `ssNameCall`: the proof an
  ## integer `std/math` call lowered by name takes.
  admitStdlibBody(routineKey, ssNameCall, absent = some(feUnsupportedOp))

func callDeclineFacet*(routineKey: string): string =
  ## The facet whose row declines a call of `routineKey`, or "".
  for d in callDeclines:
    if d.routine == routineKey: return d.facet

const stdlibDispatchSites* = {ssCallSwitch, ssInfix}
  ## The sites whose `case` goes through `dispatchMagic`.

func unsignedOpKey*(arm: string): string = "system." & arm
  ## The row key of a `dispatchMagic` arm that names a `system` routine.

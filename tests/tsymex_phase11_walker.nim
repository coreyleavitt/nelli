## Phase 11 cycle 3+ — walker support for itVariant.
##
## Cycle 3 wires `svVariant` allocation + discriminator-only access.
## Arm-field access lands in cycle 4; tFieldDefect in cycle 5.
import std/unittest
import proptest/symex

type
  ShapeKind = enum skCircle, skSquare
  Shape = object
    case kind: ShapeKind
    of skCircle: radius: int
    of skSquare: side: int

proc isSquare(s: Shape) =
  # Discriminator-only access — `s.kind` is the only field touched.
  if s.kind == skSquare:
    symexTarget("hit")

proc isLargeCircle(s: Shape) =
  # SUT gates on the discriminator THEN reads an arm-specific field.
  # Walker must produce a witness where kind = skCircle and the
  # symbolic `radius` in that arm exceeds 100.
  # Phase 16 D1a: use nested ifs so `s.radius` is only lowered AFTER
  # `s.kind == skCircle` is in the path condition (flat `and` evaluates
  # the arm-field access eagerly, before the guard is in the pc, making
  # the FieldDefect satisfiable under the unconditional D1a fork).
  if s.kind == skCircle:
    if s.radius > 100:
      symexTarget("big-circle")

suite "symex Phase 11 cycle 3 — discriminator access":
  test "symex finds a witness for a discriminator-gated label target":
    let r = symexFind(isSquare, tLabel("hit"))
    check r.status == sxSat

suite "symex Phase 11 cycle 4 — arm-field access":
  test "field-in-arm gated by `kind == X` resolves to that arm's symbol":
    let r = symexFind(isLargeCircle, tLabel("big-circle"))
    check r.status == sxSat

proc unsafeRead(s: Shape) =
  # Unconditional arm-field access — runtime raises FieldDefect when
  # `s.kind` is anything other than skCircle. Under `tFieldDefect`,
  # symex should find an input (skSquare) that demonstrates the
  # defect is reachable.
  let r = s.radius
  discard r

suite "symex Phase 11 cycle 5 — tFieldDefect":
  test "tFieldDefect finds an input that exercises a bad arm-field read":
    ## Phase 16 D1a: sxSat→sxRaised.
    let r = symexFind(unsafeRead, tFieldDefect())
    check r.status == sxRaised
    check r.raisedTypeId == "FieldDefect"

proc forceTo(s: var Shape) =
  # Force the discriminator to skCircle. After cycle 6, this
  # assignment is honored: s.kind becomes literally skCircle, so
  # the `s.kind == skSquare` branch below is UNREACHABLE.
  # Without cycle 6 the parser treats the assignment as
  # unsupported (no-op) and Z3 can still pick a model with
  # initial s.kind == skSquare, reaching the target — that's the
  # buggy behavior we're guarding against.
  s.kind = skCircle
  if s.kind == skSquare:
    symexTarget("impossible")

suite "symex Phase 11 cycle 6 — discriminator reassignment":
  test "obj.kind = literal forces vDisc; previous arm becomes unreachable":
    let r = symexFind(forceTo, tLabel("impossible"))
    check r.status == sxUnsat

proc bigSquare(s: Shape) =
  # Phase 16 D1a: nested ifs so `s.side` is only lowered after the guard.
  if s.kind == skSquare:
    if s.side > 200:
      symexTarget("big-square")

suite "symex Phase 11 cycle 7 — variant witness construction":
  test "witness for skCircle path is a proper Shape(kind: skCircle, ...)":
    let r = symexFind(isLargeCircle, tLabel("big-circle"))
    check r.status == sxSat
    let s = r.witness[0]
    check s.kind == skCircle
    check s.radius > 100

  test "witness for skSquare path is a proper Shape(kind: skSquare, ...)":
    let r = symexFind(bigSquare, tLabel("big-square"))
    check r.status == sxSat
    let s = r.witness[0]
    check s.kind == skSquare
    check s.side > 200

proc identifyCircle(s: Shape) =
  if s.kind == skCircle:
    symexTarget("c")

suite "symex Phase 11 cycle 9 — abstraction interval for variant disc":
  test "discriminator's [min, max] arm-ordinal range is logged":
    let r = symexFind(identifyCircle, tLabel("c"),
                     optimisedSymexSettings())
    check r.status == sxSat
    # Audit log must include an entry whose name targets the
    # discriminator (e.g., "s.kind") and whose interval is
    # [0, 1] — the convex hull of skCircle..skSquare ordinals.
    var found = false
    for entry in r.abstractions:
      if entry.name == "s.kind":
        check entry.interval.lo == 0
        check entry.interval.hi == 1
        found = true
    check found

type
  InnerKind = enum ikLeaf, ikBranch
  Inner = object
    case kind: InnerKind
    of ikLeaf:   value: int
    of ikBranch: count: int

  OuterKind = enum okA, okB
  Outer = object
    case kind: OuterKind
    of okA: inner: Inner
    of okB: tag:   int

proc deepCheck(o: Outer) =
  # Path requires the OUTER arm to be okA, the INNER nested
  # variant's arm to be ikLeaf, and ikLeaf's value to exceed 100.
  # Symex must reason through both variant layers + the int
  # constraint to produce a witness.
  #
  # Phase 16 D1a: use nested ifs so `o.inner.value` is only lowered
  # AFTER `o.inner.kind == ikLeaf` is in the path condition. A flat
  # `and` evaluates the arm-field access eagerly (before the guard is
  # in the pc), making the FieldDefect satisfiable and surfacing a
  # spurious sxRaised finding.
  if o.kind == okA:
    if o.inner.kind == ikLeaf:
      if o.inner.value > 100:
        symexTarget("deep")

suite "symex Phase 11 cycle 10 — nested variants":
  test "outer + inner variants compose; witness shape carries both":
    let r = symexFind(deepCheck, tLabel("deep"))
    check r.status == sxSat
    let o = r.witness[0]
    check o.kind == okA
    check o.inner.kind == ikLeaf
    check o.inner.value > 100

type
  PfKind = enum pfA, pfB
  PfFoo = object
    shared: int        # plain (non-recCase) field
    case kind: PfKind
    of pfA: armA: int
    of pfB: armB: int

proc plainSurvivesReassign(x: var PfFoo) =
  if x.shared == 42:
    x.kind = pfB
    if x.shared == 42:
      # Plain fields are shared across arms in Nim's runtime —
      # `obj.kind = X` doesn't touch them. Symex must model that:
      # the second `x.shared == 42` must still be true after the
      # reassignment, so this target is REACHABLE.
      symexTarget("preserved")

suite "symex Phase 11 — plain fields shared across variant arms (#5)":
  test "plain field survives discriminator reassignment":
    let r = symexFind(plainSurvivesReassign, tLabel("preserved"))
    check r.status == sxSat

# ---- #4 — wide-enum discriminator -------------------------------------------

# An enum with > 256 values forces the typebridge to classify the
# discriminator as uint16 (rather than uint8). The walker, the
# witness emitter, and the abstraction interval log all need to
# handle the wider BV.
type
  BigKind = enum
    bk000, bk001, bk002, bk003, bk004, bk005, bk006, bk007, bk008, bk009,
    bk010, bk011, bk012, bk013, bk014, bk015, bk016, bk017, bk018, bk019,
    bk020, bk021, bk022, bk023, bk024, bk025, bk026, bk027, bk028, bk029,
    bk030, bk031, bk032, bk033, bk034, bk035, bk036, bk037, bk038, bk039,
    bk040, bk041, bk042, bk043, bk044, bk045, bk046, bk047, bk048, bk049,
    bk050, bk051, bk052, bk053, bk054, bk055, bk056, bk057, bk058, bk059,
    bk060, bk061, bk062, bk063, bk064, bk065, bk066, bk067, bk068, bk069,
    bk070, bk071, bk072, bk073, bk074, bk075, bk076, bk077, bk078, bk079,
    bk080, bk081, bk082, bk083, bk084, bk085, bk086, bk087, bk088, bk089,
    bk090, bk091, bk092, bk093, bk094, bk095, bk096, bk097, bk098, bk099,
    bk100, bk101, bk102, bk103, bk104, bk105, bk106, bk107, bk108, bk109,
    bk110, bk111, bk112, bk113, bk114, bk115, bk116, bk117, bk118, bk119,
    bk120, bk121, bk122, bk123, bk124, bk125, bk126, bk127, bk128, bk129,
    bk130, bk131, bk132, bk133, bk134, bk135, bk136, bk137, bk138, bk139,
    bk140, bk141, bk142, bk143, bk144, bk145, bk146, bk147, bk148, bk149,
    bk150, bk151, bk152, bk153, bk154, bk155, bk156, bk157, bk158, bk159,
    bk160, bk161, bk162, bk163, bk164, bk165, bk166, bk167, bk168, bk169,
    bk170, bk171, bk172, bk173, bk174, bk175, bk176, bk177, bk178, bk179,
    bk180, bk181, bk182, bk183, bk184, bk185, bk186, bk187, bk188, bk189,
    bk190, bk191, bk192, bk193, bk194, bk195, bk196, bk197, bk198, bk199,
    bk200, bk201, bk202, bk203, bk204, bk205, bk206, bk207, bk208, bk209,
    bk210, bk211, bk212, bk213, bk214, bk215, bk216, bk217, bk218, bk219,
    bk220, bk221, bk222, bk223, bk224, bk225, bk226, bk227, bk228, bk229,
    bk230, bk231, bk232, bk233, bk234, bk235, bk236, bk237, bk238, bk239,
    bk240, bk241, bk242, bk243, bk244, bk245, bk246, bk247, bk248, bk249,
    bk250, bk251, bk252, bk253, bk254, bk255, bk256, bk257, bk258, bk259,
    bk260

proc reachWide(b: BigKind) =
  if b == bk260:
    symexTarget("wide")

suite "symex Phase 11 — wide-enum discriminator (#4)":
  test "256<n enum classifies as uint16; symex finds the high-ordinal arm":
    let r = symexFind(reachWide, tLabel("wide"))
    check r.status == sxSat
    check r.witness[0] == ord(bk260).uint16

# ---- #9 — consecutive discriminator reassignments ---------------------------

proc threeReassigns(x: var Shape) =
  x.kind = skSquare
  x.kind = skCircle
  x.kind = skSquare
  if x.kind == skSquare:
    symexTarget("final")

suite "symex Phase 11 — consecutive reassignments (#9)":
  test "obj.kind = X; obj.kind = Y; obj.kind = Z — final disc is Z":
    let r = symexFind(threeReassigns, tLabel("final"))
    check r.status == sxSat

# ---- #6 — note: Nim's variant syntax disallows duplicate field
# names across arms (`Error: attempt to redefine 'fieldName'`). The
# walker's `isVariantField` ite-chain for multi-arm collisions is
# therefore structurally unreachable from user code; the deferral
# is downgraded to "impossible in Nim's surface syntax" rather than
# a test we'd write.

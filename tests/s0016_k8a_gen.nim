## RFC-0016 K8a-gen (§10): the differential generator for one construct family.
##
## Family: integer arithmetic and exception-handler shapes, the construct
## shapes of §5.0's W-01 (`except T as e`), W-04 (float32/float64 round trip),
## W-05 (`mod`/`div` by a literal divisor at `low`), W-06 (unsigned `div`/`mod`)
## and the checks-ON half of W-07 (signed overflow and negation). Everything
## else in §5.0 (W-02 cursor, W-03 panics, W-07 checks-off) needs a global,
## a build flag or a different config and is a later family (K8b).
##
## `genPrograms(seed, count)` is pure and compile-time evaluable: a seeded list
## of `Prog` descriptions. `render` turns one into Nim source, plain or under a
## metamorphic twin (§10: dead code under a provably false guard, commutative
## reorder, extract-to-proc, wrap-in-template, `let` -> `var`, predicate
## double-negation, handler swap). `genBatch` is a macro that emits every
## program and twin as a proc in the calling module plus `runBatch_<tag>()`,
## which runs each through `symexFind` and `pinExactImpl`'s native
## differential and returns one `GenOutcome` per proc. `findings` then adds the
## twin check (a trusted twin verdict must equal the original's). A decline is
## never a finding.
import std/[macros, random, strutils, sequtils, tables]
import nelli
import nelli/symex
import ./s8cu_helpers
export sequtils

type
  Shape* = enum
    shDivLit    ## W-05: `a div|mod LIT`, LIT in {-1, 1, 2, 3, 7, ...}
    shUdiv      ## W-06: guarded unsigned `a div|mod b`
    shOvf       ## W-07 (checks on): `a + - * rhs`, signed (traps) or unsigned (wraps)
    shNeg       ## W-07: `-a` and `abs(a)`, trap at `low`
    shF32       ## W-04: `float64(float32(a))`
    shExcept    ## W-01: `except T as e:` with the label in a handler

  LitKind* = enum lkNum, lkLow, lkHigh
  Lit* = object
    kind*: LitKind
    n*: int

  Twin* = enum
    twNone, twDead, twComm, twExtract, twTemplate, twVar, twNegPred,
    twHandlerSwap

  Prog* = object
    id*: int
    shape*: Shape
    ty*: string
    op*: string       ## "div" "mod" "+" "-" "*" "neg" "abs"
    lit*: Lit         ## the literal operand (divisor / rhs / except bound)
    useB*: bool       ## shOvf: rhs is `b` rather than `lit`
    cmp*: string      ## predicate comparison
    k*: Lit           ## predicate constant
    predA*: bool      ## predicate compares with `a` rather than `k`
    # shExcept
    cmp2*: string
    lit2*: Lit
    asE*, asE2*: bool ## `except T as e` binding
    hitA*, hitB*: bool

  OutKind* = enum okExact, okDecline, okDisagree

  GenOutcome* = object
    progId*: int
    variant*: string   ## "orig" or the twin's name
    shape*: Shape
    kind*: OutKind
    exhaustive*: bool  ## the native domain was every input
    status*: string
    trusted*: bool
    raised*: string
    msg*: string
    annotations*: int

const
  signedTs = ["int", "int8", "int16", "int32", "int64"]
  unsignedTs = ["uint", "uint8", "uint16", "uint32", "uint64"]
  cmps = ["==", "!=", "<", ">", "<=", ">="]
  smallNums = [-7, -1, 0, 1, 2, 3, 7]
  posNums = [1, 2, 3, 7]

func isSigned(ty: string): bool = not ty.startsWith("uint")

func flip(c: string): string =
  case c
  of "<": ">"
  of ">": "<"
  of "<=": ">="
  of ">=": "<="
  else: c

func render*(l: Lit; ty: string): string =
  case l.kind
  of lkNum: ty & "(" & $l.n & ")"
  of lkLow: "low(" & ty & ")"
  of lkHigh: "high(" & ty & ")"

func rtype(p: Prog): string = (if p.shape == shF32: "float64" else: p.ty)

func domainSrc(p: Prog): string =
  ## The native domain, as a `Domain[T]` expression. 8-bit types are
  ## exhaustive; the rest are §10's boundary set plus the shape's edges.
  let t = p.ty
  if t in ["int8", "uint8"]:
    return "exhaustive(toSeq(low(" & t & ")..high(" & t & ")))"
  var vs: seq[string]
  if isSigned(t):
    vs = @["low(" & t & ")", "low(" & t & ")+1", t & "(-1)", t & "(0)",
           t & "(1)", t & "(7)", "high(" & t & ")-1", "high(" & t & ")"]
  else:
    vs = @[t & "(0)", t & "(1)", t & "(7)", "high(" & t & ")-1",
           "high(" & t & ")"]
  if p.shape == shF32 and t in ["int32", "int64", "int"]:
    # float32 stops representing every integer above 2^24
    vs.add [t & "(16777216)", t & "(16777217)", t & "(-16777217)"]
  if p.shape == shDivLit and p.lit.kind == lkNum:
    vs.add t & "(" & $(p.lit.n) & ")"
  "sampled([" & vs.join(", ") & "])"

func core(p: Prog; swap: bool): string =
  let t = p.ty
  case p.shape
  of shDivLit:
    "(a " & p.op & " " & render(p.lit, t) & ")"
  of shUdiv:
    "(if b != " & t & "(0): a " & p.op & " b else: " & t & "(0))"
  of shOvf:
    let rhs = if p.useB: "b" else: render(p.lit, t)
    if swap and p.op in ["+", "*"]: "(" & rhs & " " & p.op & " a)"
    else: "(a " & p.op & " " & rhs & ")"
  of shNeg:
    if p.op == "neg": "(-a)" else: "abs(a)"
  of shF32:
    "float64(float32(a))"
  of shExcept: ""

func pred(p: Prog; swap: bool): string =
  let rhs =
    if p.predA: (if p.shape == shF32: "float64(a)" else: "a")
    else:
      if p.shape == shF32: "float64(" & render(p.k, p.ty) & ")"
      else: render(p.k, p.ty)
  if swap: rhs & " " & flip(p.cmp) & " r"
  else: "r " & p.cmp & " " & rhs

func hitStmt(b: bool): string = (if b: "symexTarget(\"hit\")" else: "discard")

func exceptStmt(p: Prog; swapHandlers: bool; ind: string): string =
  let t = p.ty
  let eA = if p.asE: " as e" else: ""
  let eB = if p.asE2: " as e" else: ""
  let hA = ind & "except ValueError" & eA & ":\n" & ind & "  " &
    hitStmt(p.hitA) & "\n"
  let hB = ind & "except IOError" & eB & ":\n" & ind & "  " &
    hitStmt(p.hitB) & "\n"
  ind & "try:\n" &
    ind & "  if a " & p.cmp & " " & render(p.lit, t) &
      ": raise newException(ValueError, \"x\")\n" &
    ind & "  if b " & p.cmp2 & " " & render(p.lit2, t) &
      ": raise newException(IOError, \"y\")\n" &
    (if swapHandlers: hB & hA else: hA & hB)

func applicable*(p: Prog): seq[Twin] =
  if p.shape == shExcept:
    # K8A-1 (fixed in ec719a37): the template twin of an `as e` handler once
    # stopped the compile in routeScan; it now runs for every handler shape.
    @[twDead, twExtract, twTemplate, twHandlerSwap]
  else:
    @[twDead, twComm, twExtract, twTemplate, twVar, twNegPred]

func twinName*(tw: Twin): string =
  if tw == twNone: "orig" else: ($tw)[2 .. ^1]

func procName*(tag: string; p: Prog; tw: Twin): string =
  "g" & tag & "_" & $p.id & "_" & twinName(tw)

func render*(p: Prog; name: string; tw: Twin): string =
  ## The SUT proc (and any helper the twin extracts) as Nim source.
  let t = p.ty
  let sig = "(a, b: " & t & ")"
  if p.shape == shExcept:
    case tw
    of twNone, twHandlerSwap:
      return "proc " & name & sig & " =\n" &
        exceptStmt(p, tw == twHandlerSwap, "  ")
    of twDead:
      return "proc " & name & sig & " =\n" & exceptStmt(p, false, "  ") &
        "  if a < a: symexTarget(\"hit\")\n"
    of twExtract:
      return "proc " & name & "_ex" & sig & " =\n" &
        exceptStmt(p, false, "  ") &
        "proc " & name & sig & " =\n  " & name & "_ex(a, b)\n"
    of twTemplate:
      return "proc " & name & sig & " =\n  template w() =\n" &
        exceptStmt(p, false, "    ") & "  w()\n"
    else: doAssert false, "twin not applicable to shExcept"
  let rt = p.rtype
  let swap = tw == twComm
  let c = core(p, swap)
  let pr = pred(p, swap)
  var s = ""
  case tw
  of twExtract:
    s.add "proc " & name & "_ex" & sig & ": " & rt & " = " & c & "\n"
    s.add "proc " & name & sig & " =\n  let r = " & name & "_ex(a, b)\n"
  of twTemplate:
    s.add "proc " & name & sig & " =\n  template w(): " & rt & " = " & c & "\n"
    s.add "  let r = w()\n"
  of twVar:
    s.add "proc " & name & sig & " =\n  var r = " & c & "\n"
  else:
    s.add "proc " & name & sig & " =\n  let r = " & c & "\n"
  if tw == twDead:
    s.add "  if a < a: symexTarget(\"hit\")\n"
  if tw == twNegPred:
    s.add "  if not (" & pr & "): discard\n  else: symexTarget(\"hit\")\n"
  else:
    s.add "  if " & pr & ": symexTarget(\"hit\")\n"
  s

func render*(p: Prog): string = render(p, "g_" & $p.id, twNone)

# --- generation --------------------------------------------------------------

proc pick[T](r: var Rand; xs: openArray[T]): T = xs[r.rand(xs.high)]

proc genLit(r: var Rand; nums: openArray[int]): Lit =
  case r.rand(5)
  of 0: Lit(kind: lkLow)
  of 1: Lit(kind: lkHigh)
  else: Lit(kind: lkNum, n: r.pick(nums))

proc genProg*(r: var Rand; id: int): Prog =
  result.id = id
  # stratified: any six consecutive ids cover every shape
  result.shape = Shape(id mod (ord(high(Shape)) + 1))
  result.cmp = r.pick(cmps)
  result.cmp2 = r.pick(cmps)
  let nonNeg = @[0, 1, 2, 3, 7]
  case result.shape
  of shDivLit:
    result.ty = r.pick(@signedTs & @unsignedTs)
    result.op = r.pick(["div", "mod"])
    # a literal divisor is never zero (a zero literal traps natively: UB)
    result.lit = Lit(kind: lkNum, n: r.pick(
      if isSigned(result.ty): @[-7, -1, -1, 1, 2, 3, 7] else: @posNums))
    result.k = r.genLit(if isSigned(result.ty): @smallNums else: nonNeg)
  of shUdiv:
    result.ty = r.pick(unsignedTs)
    result.op = r.pick(["div", "mod"])
    result.k = r.genLit(nonNeg)
  of shOvf:
    result.ty = r.pick(@signedTs & @unsignedTs)
    result.op = r.pick(["+", "-", "*"])
    result.useB = r.rand(1) == 0
    result.lit = r.genLit(if isSigned(result.ty): @smallNums else: nonNeg)
    result.k = r.genLit(if isSigned(result.ty): @smallNums else: nonNeg)
  of shNeg:
    result.ty = r.pick(signedTs)
    result.op = r.pick(["neg", "abs"])
    result.k = r.genLit(@smallNums)
  of shF32:
    result.ty = r.pick(["int32", "int64", "int", "int16"])
    result.k = r.genLit(@smallNums)
  of shExcept:
    result.ty = r.pick(signedTs)
    result.lit = r.genLit(@smallNums)
    result.lit2 = r.genLit(@smallNums)
    result.asE = r.rand(1) == 0
    result.asE2 = r.rand(1) == 0
    result.hitA = r.rand(2) != 0
    result.hitB = r.rand(2) == 0
    if not (result.hitA or result.hitB): result.hitA = true
  result.predA = result.shape in {shOvf, shF32} and r.rand(2) == 0

proc genPrograms*(seed, count: int): seq[Prog] =
  ## Program `i` of seed `s` is the same program for any `count > i`.
  var r = initRand(seed)
  for i in 0 ..< count: result.add genProg(r, i)

# --- the emitted check -------------------------------------------------------

template captureRes*(call, o, plant): untyped =
  ## Runs the claim once, records the walker's verdict in `o`, and, when
  ## `plant`, returns a deliberately wrong one (the RED check of §10: the
  ## harness must catch a lying walker, with seed and program).
  block:
    var r = call
    o.status = $r.status
    o.trusted = r.trusted
    o.annotations = r.annotationViolations.len
    if r.status == sxRaised: o.raised = r.raisedTypeId
    if plant and r.trusted:
      {.cast(uncheckedAssign).}:
        if r.status == sxSat:
          r.status = sxUnsat
        elif r.status == sxUnsat:
          r.status = sxSat
          r.witness = default(typeof(r.witness))
    r

macro genBatch*(progs: static seq[Prog]; plant: static bool;
                tag: static string): untyped =
  var src = ""
  var runs = ""
  for p in progs:
    var tws = @[twNone]
    tws.add applicable(p)
    for tw in tws:
      let name = procName(tag, p, tw)
      src.add render(p, name, tw)
      let dom = domainSrc(p)
      let ex = p.ty in ["int8", "uint8"]
      runs.add "  o = GenOutcome(progId: " & $p.id & ", variant: \"" &
        twinName(tw) & "\", shape: " & $p.shape & ", exhaustive: " & $ex &
        ")\n" &
        "  try:\n" &
        "    discard pinExactImpl(" & name &
        ", claimed(captureRes(symexFind(" & name & ", tLabel(\"hit\"), " &
        "pinSettingsConst), o, " & $plant & "), \"symexFind\"), " &
        "cellKey(axConstruct, \"k8a-gen/" & ($p.shape)[2 .. ^1] & "\"), " &
        "tLabel(\"hit\"), " & dom & ", \"tsymex_0016_k8a_gen.nim\")\n" &
        "    o.kind = okExact\n" &
        "  except PinFailure as e:\n" &
        "    o.msg = e.msg\n" &
        "    o.kind = if o.trusted and o.status != \"sxUnknown\": okDisagree " &
        "else: okDecline\n" &
        "  result.add o\n"
  src.add "proc runBatch_" & tag & "*(): seq[GenOutcome] =\n  var o: GenOutcome\n"
  src.add runs
  when defined(k8aDump): echo "K8ADUMP-BEGIN ", tag, "\n", src, "K8ADUMP-END"
  parseStmt(src)

# --- findings ----------------------------------------------------------------

proc progOf(progs: seq[Prog]; id: int): Prog =
  for p in progs:
    if p.id == id: return p
  raise newException(KeyError, "no program " & $id)

func describeVerdict(o: GenOutcome): string =
  o.status & (if o.raised.len > 0: "(" & o.raised & ")" else: "")

proc findings*(progs: seq[Prog]; outs: seq[GenOutcome]; seed: int): seq[string] =
  ## Every disagreement, as a report naming the seed, the program id, the
  ## variant and the source: (1) the native differential failed on a trusted
  ## verdict; (2) a trusted twin's verdict differs from a trusted original's;
  ## (3) the walker recorded an annotation violation.
  var orig = initTable[int, GenOutcome]()
  for o in outs:
    if o.variant == "orig": orig[o.progId] = o
  for o in outs:
    let p = progOf(progs, o.progId)
    let head = "seed=" & $seed & " prog=" & $o.progId & " variant=" &
      o.variant & " shape=" & $o.shape & "\n"
    var tw = twNone
    for t in Twin:
      if twinName(t) == o.variant: tw = t
    if o.kind == okDisagree:
      result.add head & "native differential: " & o.msg & "\n" &
        render(p, procName("x", p, tw), tw)
    if o.annotations > 0:
      result.add head & "annotationViolations: " & $o.annotations
    if o.variant != "orig" and o.trusted and orig[o.progId].trusted and
       describeVerdict(o) != describeVerdict(orig[o.progId]):
      result.add head & "metamorphic: original " &
        describeVerdict(orig[o.progId]) & " vs twin " & describeVerdict(o) &
        "\n--- original\n" & render(p, procName("x", p, twNone), twNone) &
        "--- twin\n" & render(p, procName("x", p, tw), tw)

type Distribution* = object
  exact*, sampledExact*, declined*, disagree*: int
  byShape*: array[Shape, int]

proc distribution*(outs: seq[GenOutcome]): Distribution =
  for o in outs:
    inc result.byShape[o.shape]
    case o.kind
    of okExact:
      if o.status == "sxUnsat" and not o.exhaustive: inc result.sampledExact
      else: inc result.exact
    of okDecline: inc result.declined
    of okDisagree: inc result.disagree

proc declineSummary*(outs: seq[GenOutcome]): string =
  ## Declines by shape and reason, for the precision rate (never a finding).
  var counts = initCountTable[string]()
  for o in outs:
    if o.kind == okDecline:
      let i = o.msg.find("errors:")
      counts.inc $o.shape & " " & (if i >= 0: o.msg[i .. min(o.msg.high, i + 90)]
                                    else: o.msg[0 .. min(o.msg.high, 90)])
  for k, v in counts: result.add "  " & $v & "x " & k & "\n"

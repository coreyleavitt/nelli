## RFC-0016 K8a-gen (§10): the differential generator for one construct family.
##
## Family: integer arithmetic and exception-handler shapes, the construct
## shapes of §5.0's W-01 (`except T as e`), W-04 (float32/float64 round trip),
## W-05 (`mod`/`div` by a literal divisor at `low`), W-06 (unsigned `div`/`mod`)
## and the checks-ON half of W-07 (signed overflow and negation). Everything
## else in §5.0 (W-02 cursor, W-03 panics, W-07 checks-off) needs a global,
## a build flag or a different config and is a later family (K8b).
##
## `genPrograms(seed, count, first)` is pure and compile-time evaluable: a seeded list
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
import ./s0016_k8b_pairs
import ./s0016_k8b_snippets
export sequtils, s0016_k8b_pairs, s0016_k8b_snippets

type
  Shape* = enum
    shDivLit    ## W-05: `a div|mod LIT`, LIT in {-1, 1, 2, 3, 7, ...}
    shUdiv      ## W-06: guarded unsigned `a div|mod b`
    shOvf       ## W-07 (checks on): `a + - * rhs`, signed (traps) or unsigned (wraps)
    shNeg       ## W-07: `-a` and `abs(a)`, trap at `low`
    shF32       ## W-04: `float64(float32(a))`
    shExcept    ## W-01: `except T as e:` with the label in a handler
    # RFC-0016 K8b: the test-side pin families. A program of one of these
    # carries its dimension values in `fam` (tests/s0016_k8b_pairs.nim).
    shCallShape ## faCallShape: callee kind x parameter mode x call site
    shExnMem    ## faExnMemory: memory location x write point x handler x raise route
    shGeneric   ## faGeneric: generic form x type argument x un-instantiated sibling
    # RFC-0016 K8b (INT-56): an admission axis's exact rows, several per
    # program, each through its fragment (tests/s0016_k8b_snippets.nim).
    shAxis      ## `axis` and `rows` name the axis and its rows

  LitKind* = enum lkNum, lkLow, lkHigh
  Lit* = object
    kind*: LitKind
    n*: int

  Twin* = enum
    twNone, twDead, twComm, twExtract, twTemplate, twVar, twNegPred,
    twHandlerSwap,
    twHoist   ## K8b: the call evaluated into a temporary first (evaluation order)
    twRoute   ## K8b: every memory write routed through a `var` parameter
    twMono    ## K8b: the generic call replaced by its hand-instantiated proc
    twUninst  ## K8b: an un-instantiated generic added beside the SUT (AUD-07)

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
    only*: seq[string]  ## K8a-sink: narrows the native domain to these element
                        ## expressions (empty = the type's own domain)
    fam*: seq[int]      ## K8b: one value index per family dimension
    axis*: Scope        ## shAxis: the admission axis
    rows*: seq[string]  ## shAxis: the axis rows (keys) the program exercises

  Case* = object
    ## One program under one variant: the unit the sink's reducer shrinks.
    prog*: Prog
    tw*: Twin

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
  anchorBase* = 1_000_000  ## first id of `anchorPrograms`
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

func domainElems*(p: Prog): string =
  ## The native domain's values, as a `seq`/array expression (no helper
  ## needed, so a runner built against an older engine can enumerate it).
  ## 8-bit types are exhaustive; the rest are §10's boundary set plus the
  ## shape's edges.
  let t = p.ty
  if p.only.len > 0: return "[" & p.only.join(", ") & "]"
  if t in ["int8", "uint8"]:
    return "toSeq(low(" & t & ")..high(" & t & "))"
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
  "[" & vs.join(", ") & "]"

func domainList*(p: Prog): seq[string] =
  ## `domainElems` as one expression per element (the reducer's unit).
  if p.only.len > 0: return p.only
  if p.ty in ["int8", "uint8"]:
    let lo = if p.ty == "int8": -128 else: 0
    let hi = if p.ty == "int8": 127 else: 255
    for n in lo .. hi: result.add p.ty & "(" & $n & ")"
    return
  let e = domainElems(p)
  e[1 .. ^2].split(", ")

func domainSrc(p: Prog): string =
  ## The native domain, as a `Domain[T]` expression.
  if p.ty in ["int8", "uint8"] and p.only.len == 0: "exhaustive(" & domainElems(p) & ")"
  else: "sampled(" & domainElems(p) & ")"

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
  of shExcept, shCallShape, shExnMem, shGeneric, shAxis: ""

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

# --- RFC-0016 K8b: the test-side pin families ---------------------------------
#
# A family program is two `int8` inputs, exhaustive natively (65536 points),
# and a predicate `<value> <cmp> K` over `int`. Its shape is the dimension
# values in `fam` (tests/s0016_k8b_pairs.nim `famDims`); every value of a
# dimension computes the same function by a different construct, so the
# family's relations are verdict-preserving by construction.

func familyOf*(sh: Shape): Scope =
  case sh
  of shCallShape: faCallShape
  of shExnMem: faExnMemory
  of shGeneric: faGeneric
  else: axConstruct

func shapeCell*(sh: Shape): CellKey =
  ## The cell a generated program's pin is filed under: the construct axis's
  ## `k8a-gen/<Shape>` for a K8a shape, the family's `k8b-gen/<Shape>` for a
  ## K8b one.
  let k = ($sh)[2 .. ^1]
  if sh in {shCallShape, shExnMem, shGeneric}:
    CellKey(scope: familyOf(sh), key: "k8b-gen/" & k)
  else: CellKey(scope: axConstruct, key: "k8a-gen/" & k)

func pinCellOf*(p: Prog): CellKey =
  ## The cell a generated program's pin record names: `shapeCell`, or for an
  ## axis program `<axis>:k8b-gen/Axis`, a cell no table derives (an orphan K1
  ## lists and does not judge), so a packed program never stands as one
  ## row's pin.
  if p.shape == shAxis: CellKey(scope: p.axis, key: "k8b-gen/Axis")
  else: shapeCell(p.shape)

func cellSrc(c: CellKey): string =
  "CellKey(scope: " & $c.scope & ", key: \"" & c.key & "\")"

func indent(s, ind: string): string =
  for l in s.splitLines:
    if l.len > 0: result.add ind & l & "\n"

func bodyProc(name, sig, body: string; tw: Twin; top = ""): string =
  ## The SUT around a body (lines at two-space indent): plain, or extracted
  ## into a helper the SUT calls (`twExtract`); `top` is emitted first.
  result = top
  if tw == twExtract:
    result.add "proc " & name & "_ex" & sig & " =\n" & body
    result.add "proc " & name & sig & " =\n  " & name & "_ex(a, b)\n"
  else:
    result.add "proc " & name & sig & " =\n" & body

func deadLine(tw: Twin): string =
  (if tw == twDead: "  if a < a: symexTarget(\"hit\")\n" else: "")

func famPred(p: Prog; v: string): string =
  "  if " & v & " " & p.cmp & " " & $p.k.n & ": symexTarget(\"hit\")\n"

# faCallShape: callee {proc, func, template, closure, nested} x mode {value,
# varParam, openArray} x site {let, arg, cond, arith, assign}. Each callee
# computes `2x+1` (value), `x += 3; 2x-1` (varParam) or `2*xs[0]+xs[1]`.
func calleeDecl(head: string; stmts: seq[string]; last: string;
                asFunc: bool): string =
  result = head & " =\n"
  for s in stmts: result.add "  " & s & "\n"
  result.add "  " & (if asFunc: "result = " else: "") & last & "\n"

func renderCallShape(p: Prog; name: string; tw: Twin): string =
  let callee = p.fam[0]
  let mode = p.fam[1]
  let site = p.fam[2]
  let fn = name & "_f"
  let one = if callee == 3: "bias" else: "1"   # a closure captures `bias`
  let params = ["(x: int)", "(x: var int)", "(xs: openArray[int])"][mode]
  let tparams = ["(x: untyped)", "(x: untyped)", "(xs: untyped)"][mode]
  let stmts = if mode == 1: @["x = x + 3"] else: @[]
  let last = ["x * 2 + " & one, "x * 2 - " & one,
              "xs[0] * 2 + xs[1] * " & one][mode]
  var top, local: string
  case callee
  of 0: top = calleeDecl("proc " & fn & params & ": int", stmts, last, false)
  of 1: top = calleeDecl("func " & fn & params & ": int", stmts, last, true)
  of 2: top = calleeDecl("template " & fn & tparams & ": int", stmts, last, false)
  else: local = indent(calleeDecl("proc " & fn & params & ": int", stmts, last,
                                  false), "  ")
  let args = ["t", "t", "[t, int(b)]"][mode]
  let call0 = fn & "(" & args & ")"
  var body = "  var t = int(a)\n"
  if callee == 3: body.add "  var bias = 1\n"
  body.add local
  var call = call0
  if tw == twTemplate:
    body.add "  template w(): int = " & call0 & "\n"
    call = "w()"
  if tw == twHoist:
    body.add "  let c = " & call & "\n"
    call = "c"
  let lv = if tw == twVar: "var" else: "let"
  case site
  of 0: body.add "  " & lv & " r = " & call & "\n"
  of 1: body.add "  " & lv & " r = max(" & call & ", -1000)\n"
  of 2: body.add "  " & lv & " r = (if " & call & " > int(b): 1 else: 0)\n"
  of 3: body.add "  " & lv & " r = int(b) + " & call & "\n"
  else: body.add "  var r = 0\n  r = " & call & "\n"
  body.add deadLine(tw)
  body.add famPred(p, "r - t")
  bodyProc(name, "(a, b: int8)", body, tw, top)

# faExnMemory: memory {local, seqElem, objField, refField, arrayElem} x write
# point {beforeRaise, handler, finally} x handler {except ValueError, bare
# except, try/finally inside an outer except} x raise {direct, viaCall}.
func renderExnMem(p: Prog; name: string; tw: Twin): string =
  let mem = p.fam[0]
  let at = p.fam[1]
  let handler = p.fam[2]
  let via = p.fam[3]
  var top = ""
  case mem
  of 2: top.add "type " & name & "_Obj = object\n  f: int\n"
  of 3: top.add "type " & name & "_Ref = ref object\n  f: int\n"
  else: discard
  if via == 1:
    top.add "proc " & name & "_raise(x: int) =\n  if x " & p.cmp2 & " " &
      $p.lit2.n & ": raise newException(ValueError, \"x\")\n"
  if tw == twRoute:
    top.add "proc " & name & "_set(x: var int; v: int) = x = v\n"
  let m = ["m", "s[1]", "o.f", "o.f", "s[1]"][mem]
  let decl = ["var m = 1", "var s = @[0, 1, 0]", "var o = " & name & "_Obj(f: 1)",
              "let o = " & name & "_Ref(f: 1)", "var s = [0, 1, 0]"][mem]
  let route = tw == twRoute
  template wr(e: string): string =
    (if route: name & "_set(" & m & ", " & e & ")" else: m & " = " & e)
  let raiseS = if via == 1: name & "_raise(int(a))"
               else: "if int(a) " & p.cmp2 & " " & $p.lit2.n &
                     ": raise newException(ValueError, \"x\")"
  var tryBody = ""
  if at == 0: tryBody.add wr(m & " * 3") & "\n"
  tryBody.add raiseS & "\n" & wr(m & " + int(b)") & "\n"
  let hw = if at == 1: wr(m & " + 100") else: "discard"
  let fw = if at == 2: wr(m & " + 10") else: "discard"
  var tr = ""
  if handler == 2:
    tr = "try:\n  try:\n" & indent(tryBody, "    ") & "  finally:\n    " & fw &
      "\nexcept ValueError:\n  " & hw & "\n"
  else:
    tr = "try:\n" & indent(tryBody, "  ") &
      (if handler == 0: "except ValueError:\n" else: "except:\n") & "  " & hw &
      "\nfinally:\n  " & fw & "\n"
  var body = "  " & decl & "\n"
  if tw == twTemplate:
    body.add "  template w() =\n" & indent(tr, "    ") & "  w()\n"
  else:
    body.add indent(tr, "  ")
  body.add deadLine(tw)
  body.add famPred(p, m)
  bodyProc(name, "(a, b: int8)", body, tw, top)

# faGeneric: form {plain, static param, `when T is`, nested instance,
# proc-typed formal} x type argument {int, int16, int64, distinct int} x
# un-instantiated generic {none, a sibling never instantiated, one referenced
# only under `when false`} (AUD-07). Each form computes `2x+1` in T.
func renderGeneric(p: Prog; name: string; tw: Twin): string =
  let form = p.fam[0]
  let targ = p.fam[1]
  let un = p.fam[2]
  let g = name & "_g"
  let ty = ["int", "int16", "int64", name & "_Dist"][targ]
  var top = ""
  if targ == 3:
    top.add "type " & ty & " = distinct int\n" &
      "proc `+`(x, y: " & ty & "): " & ty & " {.borrow.}\n" &
      "proc `*`(x, y: " & ty & "): " & ty & " {.borrow.}\n"
  if un > 0: top.add "proc " & name & "_u[T](x: T): T = x div T(0)\n"
  if tw == twUninst: top.add "proc " & name & "_v[T](x: T): T = x div T(0)\n"
  case form
  of 0: top.add "proc " & g & "[T](x: T): T = x * T(2) + T(1)\n"
  of 1: top.add "proc " & g & "[N: static int; T](x: T): T = x * T(N) + T(1)\n"
  of 2: top.add "proc " & g & "[T](x: T): T =\n  when T is int16: x * T(2) + T(1)\n" &
          "  else: x + x + T(1)\n"
  of 3:
    top.add "proc " & g & "2[T](x: T): T = x * T(2)\n"
    top.add "proc " & g & "[T](x: T): T = " & g & "2(x) + T(1)\n"
  else:
    top.add "proc " & name & "_h(y: " & ty & "): " & ty & " = y * " & ty & "(2)\n"
    top.add "proc " & g & "[T](x: T; f: proc (y: T): T {.nimcall.}): T = f(x) + T(1)\n"
  let x = ty & "(int(a))"
  var call = case form
    of 1: g & "[2, " & ty & "](" & x & ")"
    of 4: g & "(" & x & ", " & name & "_h)"
    else: g & "(" & x & ")"
  if tw == twMono:
    let mb = case form
      of 2: (if targ == 1: "x * " & ty & "(2) + " & ty & "(1)"
             else: "x + x + " & ty & "(1)")
      of 4: name & "_h(x) + " & ty & "(1)"
      else: "x * " & ty & "(2) + " & ty & "(1)"
    top.add "proc " & name & "_m(x: " & ty & "): " & ty & " = " & mb & "\n"
    call = name & "_m(" & x & ")"
  var body = ""
  if un == 2: body.add "  when false: discard " & name & "_u(a)\n"
  if tw == twUninst: body.add "  when false: discard " & name & "_v(a)\n"
  body.add "  " & (if tw == twVar: "var" else: "let") & " r = int(" & call &
    ") + int(b)\n"
  body.add deadLine(tw)
  body.add famPred(p, "r")
  bodyProc(name, "(a, b: int8)", body, tw, top)

# shAxis: each row's fragment in turn, its value added to an accumulator the
# predicate reads. `twComm` reverses the fragments' order (they share no
# state), which only a program with no raising fragment may do.
func axisFrag(s, name: string; i: int): string =
  s.replace("N_", name & "_" & $i & "_").replace("V_", "v" & $i & "_")

func renderAxis(p: Prog; name: string; tw: Twin): string =
  var top = ""
  var frags: seq[string]
  for i, key in p.rows:
    let sn = snippetOf(AxisScope(p.axis), key)
    if sn.top.len > 0: top.add axisFrag(sn.top, name, i) & "\n"
    var f = ""
    if sn.pre.len > 0: f.add "  " & axisFrag(sn.pre, name, i) & "\n"
    f.add "  acc = acc + (" & axisFrag(sn.expr, name, i) & ")\n"
    frags.add f
  if tw == twComm:
    var r: seq[string]
    for i in countdown(frags.high, 0): r.add frags[i]
    frags = r
  var inner = "  var acc = 0\n"
  for f in frags: inner.add f
  inner.add deadLine(tw)
  inner.add famPred(p, "acc")
  var body = "  let t = int(a)\n  let u = int(b)\n"
  if tw == twTemplate:
    body.add "  template w() =\n" & indent(inner, "  ") & "  w()\n"
  else:
    body.add inner
  bodyProc(name, "(a, b: int8)", body, tw, top)

func axisRaises*(p: Prog): bool =
  for key in p.rows:
    if snippetOf(AxisScope(p.axis), key).raises: return true

func applicable*(p: Prog): seq[Twin] =
  case p.shape
  of shAxis:
    return (if axisRaises(p): @[twDead, twExtract, twTemplate]
            else: @[twDead, twExtract, twTemplate, twComm])
  of shCallShape:
    # `let r` -> `var r` needs a `let` (the assign site already has a `var`)
    return (if p.fam[2] == 4: @[twDead, twExtract, twTemplate, twHoist]
            else: @[twDead, twExtract, twTemplate, twVar, twHoist])
  of shExnMem: return @[twDead, twExtract, twTemplate, twRoute]
  of shGeneric: return @[twDead, twExtract, twVar, twMono, twUninst]
  else: discard
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
  case p.shape
  of shCallShape: return renderCallShape(p, name, tw)
  of shExnMem: return renderExnMem(p, name, tw)
  of shGeneric: return renderGeneric(p, name, tw)
  of shAxis: return renderAxis(p, name, tw)
  else: discard
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
  # stratified: any six consecutive ids cover every construct shape (the
  # K8b family shapes have their own stream, `genFamily`)
  result.shape = Shape(id mod (ord(shExcept) + 1))
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
  of shCallShape, shExnMem, shGeneric, shAxis:
    doAssert false, "a family or axis shape comes from genFamily or genAxis"
  result.predA = result.shape in {shOvf, shF32} and r.rand(2) == 0

proc genPrograms*(seed, count: int; first = 0): seq[Prog] =
  ## Program `i` of seed `s` is the same program for any `count > i`, and for
  ## any `first <= i`: this returns programs `[first, first + count)` of the
  ## seed's stream, each carrying its absolute id. The stream is sequential, so
  ## the skipped prefix is generated and dropped (cheap: no source, no walk).
  var r = initRand(seed)
  for i in 0 ..< first + count:
    let p = genProg(r, i)
    if i >= first: result.add p

const famK = [-7, -1, 0, 1, 2, 3, 7, 11, 13, 101, 103]

proc genFamily*(fam: FamilyScope; seed, count: int; first = 0): seq[Prog] =
  ## Programs `[first, first + count)` of the family's seeded stream: the
  ## dimension values from `coverChoices` (a greedy pairwise cover), the
  ## predicate and raise condition drawn from the same seed. Ids are absolute.
  let chs = coverChoices(fam, seed, first + count)
  var r = initRand(seed xor 0x5EED)
  let sh = case fam
    of faCallShape: shCallShape
    of faExnMemory: shExnMem
    of faGeneric: shGeneric
  for i in 0 ..< first + count:
    var p = Prog(id: i, shape: sh, ty: "int8", fam: chs[i])
    p.cmp = r.pick(cmps)
    p.k = Lit(kind: lkNum, n: r.pick(famK))
    p.cmp2 = r.pick(cmps)
    p.lit2 = Lit(kind: lkNum, n: r.pick(smallNums))
    if i >= first: result.add p

proc axisOrder*(axis: AxisScope; seed: int): seq[string] =
  ## The axis's fragment keys in a seeded order: which rows share a program.
  for s in axisSnippets[axis]: result.add s.key
  var r = initRand(seed)
  r.shuffle(result)

proc genAxis*(axis: AxisScope; seed, count, per: int; first = 0): seq[Prog] =
  ## Programs `[first, first + count)` of the axis's seeded stream: program
  ## `i` exercises the `per` rows at `i * per` of `axisOrder` (wrapping, so
  ## a stream longer than the rows gives each row a second program). A
  ## fragment that raises gets a program of its own rows only when `per` is
  ## 1; otherwise it shares one, and the program takes no reordering relation.
  ## Ids are absolute.
  let order = axisOrder(axis, seed)
  doAssert order.len > 0, "an axis with no fragment has no stream"
  var r = initRand(seed xor 0xA815)
  for i in 0 ..< first + count:
    var p = Prog(id: i, shape: shAxis, ty: "int8", axis: axis)
    for j in 0 ..< min(per, order.len):
      p.rows.add order[(i * per + j) mod order.len]
    p.cmp = r.pick(cmps)
    p.k = Lit(kind: lkNum, n: r.pick(famK))
    if i >= first: result.add p

func anchorPrograms*(): seq[Prog] =
  ## One hand-seeded instance per shape whose seeded stream may reach no sat
  ## witness in a small batch (`mod`/`div` by a literal, guarded unsigned
  ## `div`): each is sat by construction (`a mod 2 == 0`; `a div b == 1`), so
  ## the smoke ships an exact `construct:k8a-gen/<Shape>` record for every
  ## shape whatever the seed or count. Ids sit above any stream's.
  @[Prog(id: anchorBase, shape: shDivLit, ty: "int", op: "mod",
         lit: Lit(kind: lkNum, n: 2), cmp: "==", k: Lit(kind: lkNum, n: 0)),
    Prog(id: anchorBase + 1, shape: shUdiv, ty: "uint", op: "div",
         cmp: "==", k: Lit(kind: lkNum, n: 1))]

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

proc emitCases*(cases: seq[Case]; plant: bool; tag: string): NimNode =
  ## Emits each case as a proc plus `runBatch_<tag>()`, one `GenOutcome` per
  ## case (the case's program id and variant name key it).
  var src = ""
  var runs = ""
  for c in cases:
    let p = c.prog
    let tw = c.tw
    let name = procName(tag, p, tw)
    src.add render(p, name, tw)
    let dom = domainSrc(p)
    let ex = p.ty in ["int8", "uint8"] and p.only.len == 0
    runs.add "  o = GenOutcome(progId: " & $p.id & ", variant: \"" &
      twinName(tw) & "\", shape: " & $p.shape & ", exhaustive: " & $ex &
      ")\n" &
      "  try:\n" &
      "    discard pinExactImpl(" & name &
      ", claimed(captureRes(symexFind(" & name & ", tLabel(\"hit\"), " &
      "pinSettingsConst), o, " & $plant & "), \"symexFind\"), " &
      cellSrc(pinCellOf(p)) & ", " &
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

macro genCases*(cases: static seq[Case]; plant: static bool;
                tag: static string): untyped =
  emitCases(cases, plant, tag)

macro genBatch*(progs: static seq[Prog]; plant: static bool;
                tag: static string): untyped =
  var cases: seq[Case]
  for p in progs:
    cases.add Case(prog: p, tw: twNone)
    for tw in applicable(p): cases.add Case(prog: p, tw: tw)
  emitCases(cases, plant, tag)

func familyCases*(progs: seq[Prog]): seq[Case] =
  ## K8b: each family program with ONE of its relations, rotating through
  ## `applicable` by program id, so a batch of `n` programs exercises every
  ## relation about `n / relations` times at a third of the compile cost of
  ## all of them (a compile is about a second per proc). `genBatch` runs all.
  for p in progs:
    result.add Case(prog: p, tw: twNone)
    let rs = applicable(p)
    result.add Case(prog: p, tw: rs[p.id mod rs.len])

macro genFamilyBatch*(progs: static seq[Prog]; tag: static string): untyped =
  emitCases(familyCases(progs), false, tag)

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

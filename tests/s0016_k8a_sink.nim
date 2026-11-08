## RFC-0016 K8a-sink (§10): the pure half of the triage sink. A disagreement
## from the K8a generator is REDUCED at the generator's structural level,
## KEYED by the universe cell its shape belongs to plus the build row plus the
## verdict pair, and rendered as an `rfc-0016-intake` issue body.
## `scripts/k8a-sink.sh` is the filing half (dedup against open issues, `gh`);
## `tests/s0016_k8a_reduce.nim` is the real oracle (one compile per round).
##
## REDUCTION. A `Case` is a program under one twin. `candidates` lists every
## single-step simplification, most aggressive first:
##   1. drop the twin (the program alone still disagrees);
##   2. shrink the native domain: each half of it, then (when small) each
##      single element, so a domain narrows to the failing value;
##   3. simplify the shape one field at a time: type to the 8-bit type of its
##      signedness, op to the first of its family, literals to 0 or 1,
##      comparisons to `==`, `b` operand and `a` predicate off, handler
##      bindings off, one handler hit off.
## `reduce` asks the oracle about a whole round of candidates at once (a real
## oracle compiles them in one batch), takes the first that still disagrees
## and repeats from it. Every candidate is strictly smaller under `measure`
## (a lexicographic order), so it terminates.
##
## KEY. `dedupKey` = `<cell>|<row>|<verdict pair>`: the same cell disagreeing
## in the same way on the same build row on many seeds is one issue.
import std/[strutils]
import ./s0016_k8a_gen

type
  Oracle* = proc (cs: seq[Case]): seq[string] {.closure.}
    ## One entry per candidate: "" = no disagreement, else the first finding.

  Reduced* = object
    c*: Case
    msg*: string
    rounds*: int
    steps*: int

func isSignedTy(t: string): bool = not t.startsWith("uint")

func simplestLit(p: Prog): Lit =
  Lit(kind: lkNum, n: (if p.shape == shDivLit: 1 else: 0))

func zeroLit(): Lit = Lit(kind: lkNum, n: 0)

func complexity(p: Prog): int =
  ## How many fields are off their simplest value.
  if p.ty notin ["int8", "uint8"]: inc result
  case p.shape
  of shDivLit, shUdiv, shOvf, shNeg, shF32:
    if p.op notin ["", "div", "+", "neg"]: inc result
    if p.shape in {shDivLit, shOvf} and p.lit != simplestLit(p): inc result
    if p.useB: inc result
    if p.k != zeroLit(): inc result
    if p.cmp notin ["", "=="]: inc result
    if p.predA: inc result
  of shExcept:
    if p.lit != zeroLit(): inc result
    if p.lit2 != zeroLit(): inc result
    if p.cmp notin ["", "=="]: inc result
    if p.cmp2 notin ["", "=="]: inc result
    if p.asE: inc result
    if p.asE2: inc result
    if p.hitA and p.hitB: inc result

func measure*(c: Case): (int, int, int) =
  ((if c.tw == twNone: 0 else: 1), complexity(c.prog),
   domainList(c.prog).len)

func withProg(c: Case; p: Prog): Case = Case(prog: p, tw: c.tw)

func candidates*(c: Case): seq[Case] =
  let p = c.prog
  var raw: seq[Case]
  # 1. drop the twin
  if c.tw != twNone: raw.add Case(prog: p, tw: twNone)
  # 2. shrink the domain
  let dom = domainList(p)
  if dom.len > 1:
    let h = dom.len div 2
    var a = p
    a.only = dom[0 ..< h]
    var b = p
    b.only = dom[h .. ^1]
    raw.add withProg(c, a)
    raw.add withProg(c, b)
    if dom.len <= 12:
      for e in dom:
        var s = p
        s.only = @[e]
        raw.add withProg(c, s)
  # 3. simplify the shape, one field at a time
  template tweak(body: untyped) =
    block:
      var q {.inject.} = p
      body
      raw.add withProg(c, q)
  if p.ty notin ["int8", "uint8"] and p.shape != shF32:
    tweak:
      q.ty = (if isSignedTy(p.ty): "int8" else: "uint8")
      q.only = @[]
  if p.op notin ["", "div", "+", "neg"]:
    tweak:
      q.op = case p.shape
        of shOvf: "+"
        of shNeg: "neg"
        else: "div"
  if p.shape in {shDivLit, shOvf} and p.lit != simplestLit(p):
    tweak: q.lit = simplestLit(p)
  if p.shape == shExcept:
    if p.lit != zeroLit(): tweak: q.lit = zeroLit()
    if p.lit2 != zeroLit(): tweak: q.lit2 = zeroLit()
    if p.cmp2 notin ["", "=="]: tweak: q.cmp2 = "=="
    if p.asE: tweak: q.asE = false
    if p.asE2: tweak: q.asE2 = false
    if p.hitA and p.hitB:
      tweak: q.hitB = false
      tweak: q.hitA = false
  else:
    if p.useB: tweak: q.useB = false
    if p.k != zeroLit(): tweak: q.k = zeroLit()
    if p.predA: tweak: q.predA = false
  if p.cmp notin ["", "=="]: tweak: q.cmp = "=="
  let m0 = measure(c)
  for r in raw:
    if measure(r) < m0 and (r.tw == twNone or r.tw in applicable(r.prog)) and
       r notin result:
      result.add r

func roundCases*(cs: seq[Case]): seq[Case] =
  ## What one oracle round runs: candidate i becomes program id i, and a twin
  ## candidate also runs its original (the metamorphic check needs both).
  for i, c in cs:
    var p = c.prog
    p.id = i
    result.add Case(prog: p, tw: twNone)
    if c.tw != twNone: result.add Case(prog: p, tw: c.tw)

proc reduce*(start: Case; startMsg: string; oracle: Oracle;
             maxRounds = 64): Reduced =
  ## Greedy fixpoint: the first candidate of a round that still disagrees
  ## replaces the case; the oracle re-checks the disagreement at every step.
  result = Reduced(c: start, msg: startMsg)
  while result.rounds < maxRounds:
    inc result.rounds
    let cs = candidates(result.c)
    if cs.len == 0: break
    let msgs = oracle(cs)
    var hit = -1
    for i in 0 ..< cs.len:
      if i < msgs.len and msgs[i].len > 0:
        hit = i
        break
    if hit < 0: break
    result.c = cs[hit]
    result.msg = msgs[hit]
    inc result.steps

# --- text form of a case (the reducer rounds pass it through a -d: define) ----

func enc(l: Lit): string = $ord(l.kind) & ":" & $l.n

func dec(s: string): Lit =
  let ps = s.split(':')
  Lit(kind: LitKind(parseInt(ps[0])), n: parseInt(ps[1]))

func encodeCase*(c: Case): string =
  let p = c.prog
  @["id=" & $p.id, "shape=" & $ord(p.shape), "ty=" & p.ty, "op=" & p.op,
    "lit=" & enc(p.lit), "useB=" & $ord(p.useB), "cmp=" & p.cmp,
    "k=" & enc(p.k), "predA=" & $ord(p.predA), "cmp2=" & p.cmp2,
    "lit2=" & enc(p.lit2), "asE=" & $ord(p.asE), "asE2=" & $ord(p.asE2),
    "hitA=" & $ord(p.hitA), "hitB=" & $ord(p.hitB),
    "tw=" & $ord(c.tw), "only=" & p.only.join("~")].join(";")

func decodeCase*(s: string): Case =
  for kv in s.split(';'):
    let i = kv.find('=')
    let k = kv[0 ..< i]
    let v = kv[i + 1 .. ^1]
    case k
    of "id": result.prog.id = parseInt(v)
    of "shape": result.prog.shape = Shape(parseInt(v))
    of "ty": result.prog.ty = v
    of "op": result.prog.op = v
    of "lit": result.prog.lit = dec(v)
    of "useB": result.prog.useB = v == "1"
    of "cmp": result.prog.cmp = v
    of "k": result.prog.k = dec(v)
    of "predA": result.prog.predA = v == "1"
    of "cmp2": result.prog.cmp2 = v
    of "lit2": result.prog.lit2 = dec(v)
    of "asE": result.prog.asE = v == "1"
    of "asE2": result.prog.asE2 = v == "1"
    of "hitA": result.prog.hitA = v == "1"
    of "hitB": result.prog.hitB = v == "1"
    of "tw": result.tw = Twin(parseInt(v))
    of "only": result.prog.only = (if v.len == 0: @[] else: v.split('~'))
    else: discard

# --- keying -------------------------------------------------------------------

func cellOf*(shape: Shape): string =
  ## The universe cell a generated shape belongs to: the construct cell the
  ## K8a-gen pins are filed under (`pinExactImpl`'s key), `construct:k8a-gen/<shape>`.
  "construct:k8a-gen/" & ($shape)[2 .. ^1]

func verdictPair*(finding: string): string =
  ## The disagreeing pair, read off a `findings` entry: `<walker>|<native>`
  ## for a native differential, `meta:<orig>|<twin>` for a metamorphic one.
  ## scripts/k8a-sink.sh `pair` is the shell twin of this function (the
  ## sink's test runs both on the same fixtures).
  let m = finding.find("metamorphic: original ")
  if m >= 0:
    let rest = finding[m + len("metamorphic: original ") .. ^1]
    let v = rest.find(" vs twin ")
    let o = rest[0 ..< v]
    let t = rest[v + len(" vs twin ") .. ^1].splitLines()[0]
    return "meta:" & o & "|" & t
  let w = finding.find("walker says ")
  if w >= 0:
    var st = ""
    for ch in finding[w + len("walker says ") .. ^1]:
      if ch in {' ', '('}: break
      st.add ch
    if "does not hit natively" in finding: return st & "|native-miss"
    if "hits it natively" in finding: return st & "|native-hit"
    return st & "|native-mismatch"
  if "annotationViolations" in finding: return "annotation|-"
  "other|-"

func dedupKey*(shape: Shape; row, pair: string): string =
  cellOf(shape) & "|" & row & "|" & pair

func keyMarker*(key: string): string = "<!-- k8a-sink-key: " & key & " -->"

func issueTitle*(shape: Shape; row, pair: string): string =
  "k8a differential: " & cellOf(shape) & " on " & row & " (" & pair & ")"

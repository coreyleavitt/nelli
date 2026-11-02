## RFC-0005 S8cd item 4: the SUTs and pins `tsymex_rfc0005_s8cd_setorder_*`
## instantiate per set size. Included, not a suite of its own.

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template reached(fn: typed, lbl: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feReplayRefuted)

template dead(fn: typed, lbl: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnsat

template orderSuts(T: typedesc; A, B, C, X, tg: untyped) =
  ## Each proc starts `s = {A}`, `k = A`; `ch` writes `s = {B, C}`, `k = B`.
  proc `unionNested tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): set[T] =
      s = {B}
      {C}
    let r = (s + {X}) + ch()
    if A in r and j == 1: symexTarget(astToStr(tg) & "_u_early")
    if B in r and j == 1: symexTarget(astToStr(tg) & "_u_late")
  proc `compareTemp tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): bool =
      s = {B, C}
      true
    proc b2(a, b: bool): bool = a
    if b2(s <= {A}, ch()) and j == 1: symexTarget(astToStr(tg) & "_le_early")
    s = {A}
    if not b2(s <= {A}, ch()) and j == 1: symexTarget(astToStr(tg) & "_le_late")
  proc `eqLazy tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): bool =
      s = {B, C}
      true
    proc b2(a, b: bool): bool = a
    if b2(s == {A}, ch()) and j == 1: symexTarget(astToStr(tg) & "_eq_early")
    s = {A}
    if not b2(s == {A}, ch()) and j == 1: symexTarget(astToStr(tg) & "_eq_late")
  proc `inLazy tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): bool =
      s = {B, C}
      true
    proc b2(a, b: bool): bool = a
    if b2(A in s, ch()) and j == 1: symexTarget(astToStr(tg) & "_in_early")
    s = {A}
    if not b2(A in s, ch()) and j == 1: symexTarget(astToStr(tg) & "_in_late")
  proc `inLit tg`(j: int) =
    # A literal's elements are compared inline, not built (`k` read late).
    var k = A
    proc ch(): bool =
      k = B
      true
    proc b2(a, b: bool): bool = a
    if b2(A in {k, X}, ch()) and j == 1: symexTarget(astToStr(tg) & "_il_early")
    k = A
    if not b2(A in {k, X}, ch()) and j == 1: symexTarget(astToStr(tg) & "_il_late")
  proc `cardInner tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): int =
      s = {B, C}
      1
    proc i2(a, b: int): int = a
    if i2(card(s + {X}), ch()) == 2 and j == 1: symexTarget(astToStr(tg) & "_card_early")
    s = {A}
    if i2(card(s + {X}), ch()) == 3 and j == 1: symexTarget(astToStr(tg) & "_card_late")
  proc `cardBare tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): int =
      s = {B, C}
      1
    proc i2(a, b: int): int = a
    if i2(card(s), ch()) == 1 and j == 1: symexTarget(astToStr(tg) & "_cb_early")
    s = {A}
    if i2(card(s), ch()) == 2 and j == 1: symexTarget(astToStr(tg) & "_cb_late")
  proc `ctorEager tg`(j: int) =
    var k = A
    proc ch(): bool =
      k = B
      true
    proc f2(a: set[T]; b: bool): set[T] = a
    let r = f2({k}, ch())
    if A in r and j == 1: symexTarget(astToStr(tg) & "_ct_early")
    if B in r and j == 1: symexTarget(astToStr(tg) & "_ct_late")
  proc `elemEagerSetLazy tg`(j: int) =
    var s: set[T] = {A}
    var k = A
    proc ch(): bool =
      s = {B, C}
      k = B
      true
    proc f2(a: set[T]; b: bool): set[T] = a
    let r = f2(s + {k}, ch())
    if A in r and j == 1: symexTarget(astToStr(tg) & "_es_a")
    if B in r and j == 1: symexTarget(astToStr(tg) & "_es_b")
    if C in r and j == 1: symexTarget(astToStr(tg) & "_es_c")

template orderPins(tag: static string; big: static bool;
                   unionN, compareT, eqL, inL, inLt, cardI, cardB, ctor, es: untyped) =
  test "nim: " & tag:
    symexCaptureBegin()
    unionN(1); compareT(1); eqL(1); inL(1); inLt(1); cardI(1); cardB(1); ctor(1); es(1)
    let hit = symexCaptureEnd()
    check (tag & "_u_early" in hit) == big
    check (tag & "_u_late" in hit) == not big
    check (tag & "_le_early" in hit) == big
    check (tag & "_le_late" in hit) == not big
    check tag & "_eq_early" notin hit
    check tag & "_eq_late" in hit
    check tag & "_in_early" notin hit
    check tag & "_in_late" in hit
    check tag & "_il_early" notin hit
    check tag & "_il_late" in hit
    check (tag & "_card_early" in hit) == big
    check (tag & "_card_late" in hit) == not big
    check tag & "_cb_early" notin hit
    check tag & "_cb_late" in hit
    check tag & "_ct_early" in hit
    check tag & "_ct_late" notin hit
    check (tag & "_es_a" in hit) == true
    check (tag & "_es_b" in hit) == not big
    check (tag & "_es_c" in hit) == not big

  test "walker agrees: " & tag:
    template early(c: bool; fn: typed; lbl: string) =
      if c: reached(fn, lbl) else: dead(fn, lbl)
    early(big, unionN, tag & "_u_early")
    early(not big, unionN, tag & "_u_late")
    early(big, compareT, tag & "_le_early")
    early(not big, compareT, tag & "_le_late")
    early(false, eqL, tag & "_eq_early")
    early(true, eqL, tag & "_eq_late")
    early(false, inL, tag & "_in_early")
    early(true, inL, tag & "_in_late")
    early(false, inLt, tag & "_il_early")
    early(true, inLt, tag & "_il_late")
    early(big, cardI, tag & "_card_early")
    early(not big, cardI, tag & "_card_late")
    early(false, cardB, tag & "_cb_early")
    early(true, cardB, tag & "_cb_late")
    early(true, ctor, tag & "_ct_early")
    early(false, ctor, tag & "_ct_late")
    early(true, es, tag & "_es_a")
    early(not big, es, tag & "_es_b")
    early(not big, es, tag & "_es_c")


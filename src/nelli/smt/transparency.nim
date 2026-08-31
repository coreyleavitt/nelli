## RFC-fuzzer-nextgen G6 — combinator transparency descriptor + composition
## algebra (RFC §G-concolic, "Strategy-combinator transparency is the yield
## ceiling" — see `docs/rfc/0003-fuzzer-nextgen.md` ~lines 875-925).
##
## G1b/G2/G3 wired the concolic bridge with a MINIMAL draw->param classifier:
## a direct draw is transparent, anything behind a combinator concretizes.
## Since `map`/`filter` are the most common combinators, that severs the
## symbolic link at the first one written — `integers().map(f)` already
## opaques. This module is the fix's PURE half: a per-combinator
## **transparency descriptor** plus a **composition algebra** (`∘`) so a
## chain like `.map(f).map(g).filter(p)` still resolves to one COMPOSED
## descriptor from draw to branch, not just a single combinator's own.
##
## Zero Z3 dependency by design (mirrors `fuzzmacro.nim`'s own AST-capture
## module and `fuzz.nim`'s Z3-free stance) — this module is pure data +
## pure functions, usable both at macro-expansion time (`fuzzmacro.nim`
## walks the captured strategy AST and classifies each combinator through
## it) and in ordinary test code (the algebra is exercised directly, no
## walker/Z3 involved). `smt/runtime.nim` never imports this module: the
## macro flattens a *finished* descriptor into the primitive fields of a
## `ConcolicParamBinding` (drawIndex/coefficients/conjunct list) at
## expansion time, so the Z3-facing runtime only ever sees plain
## int64/enum data, not this module's ref-based tree.
##
## ---- The `∘` direction (PINNED) -------------------------------------------
##
## `compose(first, second)` means: apply `first`'s transform, THEN
## `second`'s — i.e. **left-to-right pipeline order**, matching the order a
## chain is WRITTEN: `s.map(f).map(g)` classifies as
## `compose(descriptorOf(f), descriptorOf(g))`. This is the OPPOSITE of
## standard mathematical composition notation (`g∘f` normally means "f
## first"); we still call the operator `∘` per the RFC's own naming, but
## always mean the pipeline direction. Every doc comment/rule below is
## stated in this direction; `tests/tsymex_g6_algebra.nim`'s "direction
## consistent for a 3+ combinator chain" case is the concrete pin.
##
## ---- The 6 categories -------------------------------------------------
##
## - `dkIdentity`   — transparent passthrough: value IS the root draw.
## - `dkAffine`     — value = a*root + b (map with an affine body).
## - `dkPredicated` — a transparent `base` (identity/affine/span-composite)
##   PLUS a list of extra Z3 conjuncts (`filter`'s accept-path) — every
##   conjunct is maintained ROOT-RELATIVE (see below), never relative to
##   some intermediate pipeline stage, so it can be asserted directly
##   against the root draw variable at Z3-build time with no further
##   substitution needed by the runtime.
## - `dkSpanComposite` — a statically-enumerable UNION of independently
##   classified strategies (`oneOf`/`frequency`-shaped combinators). The
##   descriptor set is closed over it in the narrow sense that `compose` has
##   a total case for every `(dkSpanComposite, second.kind)` pair — it never
##   falls through undefined — but "closed" here does NOT mean every cell is
##   a DERIVED rule. `span-composite ∘ {affine, predicated}` distribute per
##   the RFC's own span rule (genuinely derived, hand-traced). `span-composite
##   ∘ {span-composite, branching}` are conservative STUBS: `dOpaque()`
##   unconditionally, not a derivation, because the RFC gives no rule for a
##   `oneOf(...).flatMap(...)`-shaped chain and this slice's classifier
##   cannot produce a `dkSpanComposite` to reach them with anyway (see
##   `spanCompositeStubHits` below — the tripwire that keeps that fact from
##   going unnoticed once a future classifier CAN reach them). This slice's
##   AST classifier does not yet PRODUCE a `dkSpanComposite` at all (out of
##   scope per the RFC's own "Classification from the captured AST" list,
##   which names only `map`/`filter`/`flatMap`) — a future classifier slice
##   is its producer.
## - `dkOpaque`     — nothing is known; concretize downstream, as today.
## - `dkBranching`  — enumerable `flatMap`: the next strategy is chosen from
##   the prior draw's value over a small, statically-enumerable case set
##   (`cases`); each case pairs a guard (`PredicateSpec`, checked against
##   the DISCRIMINATOR draw) with the descriptor of what that case
##   produces (a SEPARATE, later draw — not a further transform of the
##   discriminator's own root).
##
## ---- Root-relative predicates ------------------------------------------
##
## A `PredicateSpec` is always `(a*root + b) op lit`, where `root` is the
## SAME underlying draw the whole descriptor traces back to. When a filter
## is classified in isolation its predicate is initially expressed relative
## to ITS OWN input (whatever flows in at that point in the chain); folding
## it into an accumulated descriptor via `compose` re-expresses it relative
## to the chain's root by substituting the accumulated base's own (a, b)
## through it — pure algebraic expansion, never a division, so comparison
## direction never needs flipping.

import std/sequtils

type
  DescriptorKind* = enum
    dkIdentity
    dkAffine
    dkPredicated
    dkSpanComposite
    dkOpaque
    dkBranching

  PredOp* = enum
    poEq, poNe, poLt, poLe, poGt, poGe

  PredicateSpec* = object
    ## `(a*root + b) op lit` — see the module doc's "root-relative
    ## predicates" section. `a == 1, b == 0` is the common case (the
    ## predicate is checked directly against an unmodified draw).
    a*, b*: int64
    op*: PredOp
    lit*: int64

  TransparencyDescriptor* = ref object
    case kind*: DescriptorKind
    of dkIdentity: discard
    of dkAffine:
      a*, b*: int64                            ## value = a*root + b
    of dkPredicated:
      base*: TransparencyDescriptor            ## dkIdentity/dkAffine/dkSpanComposite
      conjuncts*: seq[PredicateSpec]           ## root-relative, ANDed
    of dkSpanComposite:
      spans*: seq[TransparencyDescriptor]      ## one per enumerable span
    of dkOpaque: discard
    of dkBranching:
      cases*: seq[BranchingCase]

  BranchingCase* = object
    guard*: PredicateSpec       ## checked against the DISCRIMINATOR draw
    then*: TransparencyDescriptor ## what THAT case produces (own draw(s))

# ---- constructors -----------------------------------------------------------

proc dIdentity*(): TransparencyDescriptor =
  TransparencyDescriptor(kind: dkIdentity)

proc dAffine*(a, b: int64): TransparencyDescriptor =
  TransparencyDescriptor(kind: dkAffine, a: a, b: b)

proc dPredicated*(base: TransparencyDescriptor,
                  conjuncts: seq[PredicateSpec]): TransparencyDescriptor =
  TransparencyDescriptor(kind: dkPredicated, base: base, conjuncts: conjuncts)

proc dSpanComposite*(spans: seq[TransparencyDescriptor]): TransparencyDescriptor =
  TransparencyDescriptor(kind: dkSpanComposite, spans: spans)

proc dOpaque*(): TransparencyDescriptor =
  TransparencyDescriptor(kind: dkOpaque)

proc dBranching*(cases: seq[BranchingCase]): TransparencyDescriptor =
  TransparencyDescriptor(kind: dkBranching, cases: cases)

# ---- R36 tripwire: the two conservatively-stubbed composition cells --------

var spanCompositeStubHits* = 0
  ## RFC-fuzzer-nextgen R36 (code review, LOW): incremented every time
  ## `compose` actually falls into one of the two STUBBED cells
  ## (`dkSpanComposite ∘ dkSpanComposite`, `dkSpanComposite ∘ dkBranching` —
  ## see the module doc's "closed" callout above). Both cells are inert
  ## today only because no classifier in this slice ever PRODUCES a
  ## `dkSpanComposite` descriptor for `compose` to be called with — there is
  ## no real code path that can increment this counter yet. Its entire
  ## purpose is to survive that becoming false: once a future span
  ## classifier lands, a real `.oneOf(...).oneOf(...)` or
  ## `.oneOf(...).flatMap(...)` chain would silently degrade to `dOpaque()`
  ## (a correct-but-conservative approximation, never unsound) with nothing
  ## to notice that the "derived rule" half of the algebra's promise no
  ## longer covers every chain it is asked about. A caller integrating that
  ## future classifier should check this counter (or call
  ## `resetSpanCompositeStubHits()` at a suite/campaign boundary and
  ## re-check) and treat a nonzero result as a prompt to either derive the
  ## real rule or make the approximation an explicit, tested decision —
  ## rather than an emergency: this counter deliberately does not raise or
  ## abort, since `dOpaque()` here is a documented-safe degradation, not a
  ## bug, and a hot composition path is exactly the wrong place for a
  ## surprise exception or log line on every hit.

proc resetSpanCompositeStubHits*() =
  ## Test/harness support: zero the tripwire counter, e.g. between test
  ## cases that each want to assert their OWN hit/no-hit outcome independent
  ## of what ran before them in the same process.
  spanCompositeStubHits = 0

# ---- predicate substitution --------------------------------------------------

proc substituteAffine*(p: PredicateSpec, a, b: int64): PredicateSpec =
  ## Re-express `p` (currently relative to some value `v`) relative to
  ## `v`'s OWN root, given `v = a*root + b`. Pure algebraic expansion:
  ## `(p.a*v + p.b) op p.lit` == `(p.a*a)*root + (p.a*b + p.b) op p.lit` —
  ## substitution, never division, so `p.op` never flips.
  PredicateSpec(a: p.a * a, b: p.a * b + p.b, op: p.op, lit: p.lit)

proc evalPredicate*(p: PredicateSpec, rootVal: int64): bool =
  ## Pure (non-Z3) evaluation — used for concrete branch-selection
  ## (`dkBranching` resolution against a recorded trace value) and by the
  ## algebra's own tests.
  let v = p.a * rootVal + p.b
  case p.op
  of poEq: v == p.lit
  of poNe: v != p.lit
  of poLt: v <  p.lit
  of poLe: v <= p.lit
  of poGt: v >  p.lit
  of poGe: v >= p.lit

# ---- composition algebra -----------------------------------------------------

proc compose*(first, second: TransparencyDescriptor): TransparencyDescriptor

proc composeBase(base: TransparencyDescriptor,
                  second: TransparencyDescriptor): TransparencyDescriptor =
  ## `predicated`'s `base` is restricted to {identity, affine,
  ## span-composite} (never itself predicated/opaque/branching — a filter's
  ## conjuncts always fold into the OUTER `conjuncts` seq, never nest a
  ## second predicated layer). Composing it forward reuses the same total
  ## `compose` — `base`'s kind is always one `compose` already handles.
  compose(base, second)

proc compose*(first, second: TransparencyDescriptor): TransparencyDescriptor =
  # ---- identity: neutral element both directions ----
  if first.kind == dkIdentity: return second
  if second.kind == dkIdentity: return first
  # ---- opaque: absorbing both directions ----
  if first.kind == dkOpaque or second.kind == dkOpaque: return dOpaque()

  result = case first.kind
  of dkIdentity, dkOpaque: dOpaque()  # unreachable (handled above)

  of dkAffine:
    case second.kind
    of dkIdentity, dkOpaque: return dOpaque()  # unreachable
    of dkAffine:
      # affine ∘ affine = affine, coefficients composed pipeline-order:
      # y1 = a1*x+b1 ; y2 = a2*y1+b2 = (a2*a1)*x + (a2*b1+b2)
      dAffine(second.a * first.a, second.a * first.b + second.b)
    of dkPredicated:
      # affine ∘ predicated: the filter's conjuncts were classified
      # relative to ITS OWN input (== this affine's output) — re-express
      # them relative to root via the affine substitution, and carry the
      # conjunct forward per "predicated ∘ t = t (conjunct carried)",
      # mirrored for the affine-then-predicated direction.
      dPredicated(composeBase(first, second.base),
                  second.conjuncts.mapIt(substituteAffine(it, first.a, first.b)))
    of dkSpanComposite:
      dSpanComposite(second.spans.mapIt(compose(first, it)))
    of dkBranching:
      # .map(f).flatMap(g): g's guards were classified relative to f's
      # output — re-express them relative to root; each case's OWN
      # continuation is untouched (a separate, later draw).
      dBranching(second.cases.mapIt(
        BranchingCase(guard: substituteAffine(it.guard, first.a, first.b),
                       then: it.then)))

  of dkPredicated:
    case second.kind
    of dkIdentity, dkOpaque: return dOpaque()  # unreachable
    of dkAffine:
      # predicated ∘ affine = affine (conjunct carried, unchanged — the
      # affine runs AFTER the filter's condition already fired against a
      # root-relative value, so re-anchoring is a no-op for the conjunct).
      dPredicated(composeBase(first.base, second), first.conjuncts)
    of dkPredicated:
      # predicated ∘ predicated: conjoin BOTH — the second's own
      # conjuncts are relative to ITS input (== first's base's output),
      # substituted through first.base the same way affine∘predicated
      # does when first.base is affine; identity/span-composite bases
      # need no numeric adjustment (identity: a=1,b=0 no-op; span-
      # composite: distribute per span, approximated below).
      let carried =
        case first.base.kind
        of dkAffine: second.conjuncts.mapIt(substituteAffine(it, first.base.a, first.base.b))
        else: second.conjuncts  # identity, or span-composite (conservative: unchanged)
      dPredicated(composeBase(first.base, second.base), first.conjuncts & carried)
    of dkSpanComposite:
      dSpanComposite(second.spans.mapIt(compose(first, it)))
    of dkBranching:
      # .filter(p).flatMap(g): fold per-case, carrying first's conjuncts
      # forward is not representable in a single-PredicateSpec guard, so
      # (documented, sound-by-RFC's-own-stance: a wasted candidate at
      # worst, Track E re-verifies) we approximate by composing through
      # the filter's `base` only, same as the affine case.
      dBranching(second.cases.mapIt(
        (if first.base.kind == dkAffine:
           BranchingCase(guard: substituteAffine(it.guard, first.base.a, first.base.b), then: it.then)
         else:
           it)))

  of dkSpanComposite:
    case second.kind
    of dkIdentity, dkOpaque: return dOpaque()  # unreachable
    of dkAffine, dkPredicated:
      # span-composite ∘ t (t transparent/predicated): distribute t across
      # every span — "select span i, then apply t to whatever span i
      # produced" (the RFC's own "span rule").
      dSpanComposite(first.spans.mapIt(compose(it, second)))
    of dkSpanComposite, dkBranching:
      # STUBBED, not derived — see the module doc's "closed" callout and
      # `spanCompositeStubHits`'s own doc above. Not given a precise rule by
      # the RFC (nor reachable from a real `.oneOf(...).oneOf(...)`/
      # `.oneOf(...).flatMap(...)`-shaped chain in THIS slice's scope, since
      # no classifier here produces a `dkSpanComposite` at all) —
      # conservative absorbing default, keeps the table total and the
      # approximation sound (never unsound), but a real hit once a future
      # span classifier lands is a hit against a STUB, not a proven rule —
      # counted so that fact cannot go silently unnoticed.
      #
      # `when nimvm`: this module doubles as MACRO-EXPANSION-TIME code (see
      # the module doc's own opening paragraph — `fuzzmacro.nim` walks a
      # captured strategy AST and calls `compose` from inside compile-time
      # macro code, i.e. the NimVM). A plain top-level `var` mutation is not
      # something the VM can evaluate at compile time (`cannot evaluate at
      # compile time: spanCompositeStubHits` — caught by
      # `tests/tfuzzconcolicbridge_g6_affine.nim`'s real `fuzz(...)` call
      # site, which forces `compose` through the VM). The tripwire only
      # needs to observe genuine RUNTIME hits anyway — a hit during macro
      # expansion is still a hit against an unclassifiable-today cell, but
      # there is no live campaign runtime path through the VM for the
      # counter's own doc comment ("check this counter... once a classifier
      # ships") to ever consult; skip the increment there rather than fail
      # the compile-time path outright.
      when nimvm:
        discard
      else:
        inc spanCompositeStubHits
      dOpaque()

  of dkBranching:
    # branching ∘ anything: distribute the continuation across every
    # case — "per the enumerable rule" (RFC). Each case's OWN `then`
    # composes with `second` exactly like a plain chain-fold would.
    dBranching(first.cases.mapIt(BranchingCase(guard: it.guard, then: compose(it.then, second))))

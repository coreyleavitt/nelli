import std/[unittest, strutils]
import proptest

# Bug B / REQUIRESINIT_VARIANT_BINDING (Trigger 2): a requiresInit *variant*
# whose DEFAULT discriminator branch (`ok = false`) carries a required field
# (`e`). Its `default`/`reset` is invalid — unlike trequiresinit's `Ev`, whose
# default branch is empty — so the engine's `Option[T]` storage sites used to
# fail to instantiate. The `Opt[T]` boxing makes it bindable.
type Res[T, E] {.requiresInit.} = object
  case ok: bool
  of true:  v: T
  of false: e: E

proc resStrat(): Strategy[Res[int, string]] =
  integers(0, 9).map(proc(x: int): Res[int, string] =
    Res[int, string](ok: true, v: x))

proc errStrat(): Strategy[Res[int, string]] =
  strings().map(proc(s: string): Res[int, string] =
    Res[int, string](ok: false, e: s))

proc eitherStrat(): Strategy[Res[int, string]] =
  # oneOf shrinks by choosing among sub-strategies; its mute/branch
  # machinery + the engine's explicit-examples seq used to instantiate
  # seq[Res].setLen → shrink → reset(Res), which trips strict-effects
  # (RootEffect) under --threads:on. Boxing the example storage fixes it.
  oneOf(@[resStrat(), errStrat()])

suite "DSL: requiresInit variant (non-empty default branch)":
  property "binds via given (passing property)":
    given r in resStrat()
    ensure r.ok

  test "oneOf over the variant runs under threads (passing)":
    let r = forAll(eitherStrat(), proc(x: Res[int, string]) =
      ensure x.ok or not x.ok)
    check r.outcome == otPassed

  property "given binds oneOf over the variant (DSL accumulator path)":
    # Exercises the `given` macro's Examples[T] accumulator over a oneOf
    # strategy — the exact nopal shape that tripped strict-effects.
    given r in eitherStrat()
    ensure r.ok or not r.ok

  test "falsification through oneOf reports the counterexample":
    # Only the ok-branch can violate v < 5; shrinking must thread the boxed
    # value through the oneOf/branch-mute machinery and report a real Res.
    let r = forAll(eitherStrat(), proc(x: Res[int, string]) =
      ensure (not x.ok) or x.v < 5)
    check r.outcome == otFalsified
    check r.counterexample.isSome
    check r.counterexample.get.ok
    check r.counterexample.get.v >= 5

  test "falsification reports the counterexample value":
    # `forAll` directly so we can inspect the Report rather than fail the
    # unittest. The counterexample is a real `Res` value, boxed via `Opt`.
    let r = forAll(resStrat(), proc(x: Res[int, string]) =
      ensure x.v < 5)
    check r.outcome == otFalsified
    check r.counterexample.isSome
    check r.counterexample.get.ok
    check r.counterexample.get.v >= 5

  test "counterexample shrinks to the minimal boundary":
    # integers(0, 9) shrinks toward 0, so the minimal `v` that still
    # violates `v < 5` is exactly 5. Shrinking must thread the boxed value
    # through replay and report the minimized `Res`.
    let r = forAll(resStrat(), proc(x: Res[int, string]) =
      ensure x.v < 5)
    check r.counterexample.get.v == 5

  test "rendered counterexample shows the value, not a box/ref address":
    let r = forAll(resStrat(), proc(x: Res[int, string]) =
      ensure x.v < 5)
    let text = repro(r)
    check "v: 5" in text       # the actual field value, rendered
    check "0x" notin text      # not a raw pointer address
    let j = renderReport(r, ofJson)
    check "v: 5" in j

  test "explicit example of the variant is pinned and reported":
    # Exercises the explicit-examples path (boxed `Examples[T]`). Pinned
    # examples aren't shrunk, so the reported counterexample is the exact
    # value supplied. NB: pass an *array* literal `[bad]` — for a
    # no-valid-default element type, a `seq` literal `@[bad]` would
    # instantiate `seq[Res]` at this call site.
    let bad = Res[int, string](ok: true, v: 7)
    let r = forAllWithExamples([bad], resStrat(),
      proc(x: Res[int, string]) = ensure x.v < 5)
    check r.outcome == otFalsified
    check r.counterexample.isSome
    check r.counterexample.get.v == 7

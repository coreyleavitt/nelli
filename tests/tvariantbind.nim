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

suite "DSL: requiresInit variant (non-empty default branch)":
  property "binds via given (passing property)":
    given r in resStrat()
    ensure r.ok

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
    # Exercises the explicit-examples seq[T] path (`reqInitSafeSeq`).
    # Pinned examples aren't shrunk, so the reported counterexample is the
    # exact value supplied.
    let bad = Res[int, string](ok: true, v: 7)
    let r = forAllWithExamples(@[bad], resStrat(),
      proc(x: Res[int, string]) = ensure x.v < 5)
    check r.outcome == otFalsified
    check r.counterexample.isSome
    check r.counterexample.get.v == 7

## RFC-0016 INT-57 (RED, open): an `int` built from `$n` (`iekIntToStr`, Z3
## `str.from_int`) and added to an `int`. The query that asks whether the
## addition overflows (the `OverflowDefect` path) is one on which Z3 stops
## advancing its step counter, so `queryRLimit` never ends it; only the wall
## clock does, and the pin settings (`pinSettingsConst`) turn the wall clock
## off so a loaded machine cannot turn a pin into a decline. Under those
## settings the walk does not terminate (killed at 900 s), which breaks the
## engine's "never hang, always classify" invariant on two modelled exact
## rows: magic `IntToStr` and typeop `letCursor/string`. A string ORDER over
## two such strings (magic `LeStr`) beside a set's `card` stalls the query on
## the target's own path the same way, or ends `incomplete (theory seq)`.
##
## K8b's axis suites found it (INT-56): the typeclass, typeop and magic axis
## programs that pack a `$n` fragment with any arithmetic beside it. Alone,
## `len($t) + t <= 3` is exact in about 9 s; `len($t) + t + 129 <= 3` and
## `acc = acc + len($t)` are not.
##
## This file runs each shape under a 20 s wall-clock bound so it terminates,
## and checks what a fix must give: a trusted, exact verdict with no query
## ended by the wall clock. A sat verdict can stand beside a stalled query
## (the witness came from another path), so the stall is checked on its own:
## an error naming it ("Z3 stopped advancing its step count", or the seq
## theory's "incomplete") is the hang the pin settings turn into a 900 s kill.
## It stays red until those queries are decided, and is not registered in the
## nimble test task while it is.
import std/[unittest, times, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc i57LetCursor(a, b: int8) =
  ## typeop `letCursor/string` as K8b generated it (typeop program 6)
  let t = int(a)
  var acc = 0
  var x: string = $t
  let c = x
  acc = acc + c.len
  if acc <= 7: symexTarget("hit")

proc i57Offset(a, b: int8) =
  ## the smallest arithmetic shape: no input reaches the target
  ## (`$(-128)` has four characters, -128 + 4 + 129 = 5)
  let t = int(a)
  if len($t) + t + 129 <= 3: symexTarget("hit")

proc i57Scaled(a, b: int8) =
  ## the typeclass shape (`string` packed with five other rows): `t = 0` hits
  let t = int(a)
  if len($t) + 10 * t <= 3: symexTarget("hit")

type I57E = enum i57e0, i57e1

proc i57Order(a, b: int8) =
  ## the magic shape (program 0 of the magic stream, three of its six rows):
  ## a string order over `$t` and `$u` beside a set's `card`; the query on
  ## the target's own path stalls or ends `incomplete (theory seq)`. `a = b`
  ## hits (the sum is then at most 2)
  let t = int(a)
  let u = int(b)
  var acc = 0
  acc = acc + ord(I57E(t and 1) < I57E(u and 1))
  acc = acc + ord($t <= $u)
  acc = acc + card({a} + {b})
  if acc <= 3: symexTarget("hit")

proc mkBounded(): SymexSettings =
  result = pinSettingsConst
  result.budget.queryTimeoutMs = 20_000
const bounded = mkBounded()

template decide(f: untyped; want: SymexStatusKind) =
  let t0 = epochTime()
  let r = symexFind(f, tLabel("hit"), bounded)
  checkpoint astToStr(f) & ": " & $r.status & " trusted=" & $r.trusted &
    " in " & $int(epochTime() - t0) & " s; errors " & $r.errors
  check r.trusted
  check r.status == want
  # the stall itself: under the pin settings this query never returns
  for e in r.errors:
    check "stopped advancing" notin e.msg
    check "incomplete (theory seq)" notin e.msg

suite "INT-57 (red): a string length's overflow query stalls Z3":
  test "typeop letCursor/string: `acc = acc + len($t)` is exact (sat)":
    decide(i57LetCursor, sxSat)
  test "`len($t) + t + 129 <= 3` is exact (unsat)":
    decide(i57Offset, sxUnsat)
  test "`len($t) + 10 * t <= 3` is exact (sat)":
    decide(i57Scaled, sxSat)
  test "magic: `ord($t <= $u)` beside `card` and an enum order is exact (sat)":
    decide(i57Order, sxSat)

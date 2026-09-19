## Issue #163 review (second-hand-reported gaps, verified by experiment before
## being pinned here — two reported, both reproduced).
##
## (1) `nnkHiddenCallConv` — `echo(intExpr)` failed to parse AT ALL.
## `dsl_parser.nim`'s expression parser had no arm for `nnkHiddenCallConv`,
## the hidden `$`-conversion Nim inserts for a non-string element of a
## `varargs[string, `$`]` (`echo`'s formal). ANY SUT containing `echo(x)` for
## a non-string `x` failed with `feUnsupportedExprKind`, regardless of
## anything else in the program — confirmed via a `treeRepr` probe:
## `echo(x)` for `x: int` types the varargs array element as
## `HiddenCallConv(Sym "$", Sym "x")`.
##
## `tsymex_163_opaque_transparent.nim`'s `withEcho` and
## `tsymex_163rev_inert_argfork.nim` both sidestepped this exact gap
## (documented explicitly in the latter's header) by echoing a string
## literal, or routing the int through a `{.symexOpaque.}` `sink` proc
## instead of `echo` directly.
##
## (2) `nnkHiddenSubConv` — a char-RANGE value compared against a char
## literal (`c > 'm'` for `c: range['a'..'z']`) also failed to parse.
## `tsymex_163audit_range_domain.nim`'s W3 fix repaired the TYPE side
## (`dsl_typebridge.nim`'s alias guard widened to admit `nnkCharLit`
## bounds) but explicitly sidestepped this EXPRESSION-side gap by using
## `ord(c) > ord('m')` instead of a direct comparison — its own comment
## names this exact node kind as "a pre-existing, unrelated gap". Confirmed
## via the same `treeRepr` probe: Nim widens the range value to its base
## `char` type via `HiddenSubConv(Empty, Sym "c")` for the `<` operator to
## resolve (the analogous INT-range comparison instead uses
## `nnkHiddenStdConv`, already handled).
##
## Both fixes land in `dsl_parser.nim`'s `parseExpr` `case n.kind`: (2) joins
## the existing `nnkHiddenStdConv`/`nnkHiddenAddr` blind unwrap (a subrange
## shares its base type's runtime representation, so passthrough is exactly
## as sound as the existing `nnkHiddenStdConv` case); (1) is NOT a blind
## unwrap — it reuses the same `$`-conversion lowering (`iekIntToStr`/
## `iekRuneToStr`) the explicit `nnkPrefix`/`nnkCall` `$` sites already use,
## so the result stays genuinely string-typed even in the hypothetical where
## a hidden `$`-conversion's result were actually consumed, not just handed
## to an opaque sink like `echo`.
##
## House rule: every symbolic expectation below is paired with the SAME
## computation run for real in Nim, in this file.

import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

const Magic = 0x5A4D

# ---------------------------------------------------------------------------
# (1) echo(intExpr) parses; a raise BEHIND it is still found, and a defect
# INSIDE the echoed expression itself still forks (the fix must genuinely
# parse the wrapped operand, not silently stand in a dummy that would hide a
# real defect one level down — this is exactly finding R1's shape, run
# through `echo` directly rather than `tsymex_163rev_inert_argfork.nim`'s
# `sink` workaround).

proc withEchoIntThenRaise(x: int) =
  echo x
  if x == Magic:
    raise newException(ValueError, "magic")
  symexTarget("t_echoint")

proc echoedDivRaises(a, b: int) =
  echo a div b
  symexTarget("reached")

suite "#163 rev (1) -- echo(intExpr) parses":

  test "oracle: withEchoIntThenRaise raises on Magic, and only then":
    expect ValueError:
      withEchoIntThenRaise(Magic)
    withEchoIntThenRaise(0)

  test "a raise BEHIND echo(int) is found, not degraded to sxUnknown":
    let r = symexFind(withEchoIntThenRaise, tRaisedExn("ValueError"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "ValueError"

  test "a label BEHIND the same echo, on the non-raise path, is reachable":
    let r = symexFind(withEchoIntThenRaise, tLabel("t_echoint"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

  test "oracle: echo(a div b) really raises DivByZeroDefect at b == 0, and only then":
    expect DivByZeroDefect:
      echoedDivRaises(1, 0)
    echoedDivRaises(10, 5)

  test "a defect INSIDE the echoed expression itself still forks":
    ## Before the fix `echo(a div b)` did not parse at all (any SUT
    ## containing it degraded to sxUnknown at parse time) -- this is a
    ## stronger claim than "parses": the div-by-zero fork inside the
    ## echoed operand must survive the fix, not just the outer call.
    let r = symexFind(echoedDivRaises, tRaisedExn("DivByZeroDefect"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

# ---------------------------------------------------------------------------
# (2) a char-range value compared DIRECTLY against a char literal parses,
# reaches a real verdict, and still respects its declared domain.

type
  Letter = range['a'..'z']

proc checkLetter(c: Letter) =
  if c > 'm':
    raise newException(ValueError, "past m")

proc letterUpperHalf(c: Letter) =
  if c > 'm':
    symexTarget("upperhalf")

proc letterOutOfBounds(c: Letter) =
  if c > 'z':
    symexTarget("outofbounds")

suite "#163 rev (2) -- a char RANGE compared against a char literal parses":

  test "oracle: checkLetter raises past 'm', and only then":
    expect ValueError:
      checkLetter('n')
    checkLetter('m')
    checkLetter('a')

  test "a raise from a direct char-range comparison is found, not degraded":
    let r = symexFind(checkLetter, tRaisedExn("ValueError"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "ValueError"

  test "the upper-half target is reachable through the direct comparison":
    let r = symexFind(letterUpperHalf, tLabel("upperhalf"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

  test "the unwrap does not discard the declared domain -- past 'z' is unreachable":
    ## No Nim oracle is possible here (the type system never lets a real
    ## program construct a `Letter` past 'z' to begin with) -- the
    ## complementary fact is that W3/W7's own domain reasoning applies: this
    ## is the SAME allocated symbol and the SAME `hasRange` constraint the
    ## `ord(c) > ord('z')` route in `tsymex_163audit_range_domain.nim`
    ## already proves unreachable. If the new `nnkHiddenSubConv` unwrap
    ## somehow bypassed the type's range constraint (e.g. by reclassifying
    ## through the wrong node), this would go sxSat instead.
    let r = symexFind(letterOutOfBounds, tLabel("outofbounds"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnsat

suite "#163 rev parser gaps -- walker version pin":

  test "walker version floor >= 139":
    check parseInt(symexWalkerVersion) >= 139

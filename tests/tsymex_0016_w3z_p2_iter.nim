## RFC-0016 W3-z P2 (wiring audit A2) -- the default build.
##
## A closure iterator is compiled at its definition, under the options in
## force there. The inliner parsed its body under the CALLER's check scope, so
## an iterator under `{.push nanChecks: on.}` called from a default routine
## was walked unchecked: `0.0/0.0` gave NaN instead of `FloatInvalidOpDefect`.
## An `{.inline.}` iterator is expanded at the call site and takes the caller's
## options (probed natively below), as `RFC-0005 S8cu` already says.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

{.push nanChecks: on.}
iterator nanClosure(): int {.closure.} =
  var z = 0.0
  let r = z / z
  if r != r: yield 1
  yield 2

iterator nanInline(): int {.inline.} =
  var z = 0.0
  let r = z / z
  if r != r: yield 1
  yield 2
{.pop.}

iterator plainClosure(): int {.closure.} =
  var z = 0.0
  let r = z / z
  if r != r: yield 1
  yield 2

iterator plainInline(): int {.inline.} =
  var z = 0.0
  let r = z / z
  if r != r: yield 1
  yield 2

{.push nanChecks: on.}
proc callsPlainClosure(x: int) =
  var touch = 1.0   # the routine reads a float, so its float checks are read
  touch += 1.0
  ## The caller is pushed on; the closure iterator is defined with the build's
  ## options (off): a NaN result, no raise.
  if x == 5:
    try:
      for v in plainClosure(): discard v
    except FloatInvalidOpDefect:
      return
    symexTarget("hit")
{.pop.}

proc sutClosure(x: int) =
  if x == 5:
    try:
      for v in nanClosure(): discard v
    except FloatInvalidOpDefect:
      symexTarget("hit")

proc sutClosureNoRaise(x: int) =
  if x == 5:
    try:
      for v in nanClosure(): discard v
    except FloatInvalidOpDefect:
      return
    symexTarget("hit")

proc sutInline(x: int) =
  if x == 5:
    try:
      for v in nanInline(): discard v
    except FloatInvalidOpDefect:
      symexTarget("hit")

proc sutInlineNoRaise(x: int) =
  if x == 5:
    try:
      for v in nanInline(): discard v
    except FloatInvalidOpDefect:
      return
    symexTarget("hit")

{.push nanChecks: on.}
proc sutInlineInPushed(x: int) =
  var touch = 1.0   # the routine reads a float, so its float checks are read
  touch += 1.0
  if x == 5:
    try:
      for v in plainInline(): discard v
    except FloatInvalidOpDefect:
      symexTarget("hit")
{.pop.}

suite "W3-z P2: closure iterator check scope, default build":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 313

  test "native: a pushed closure iterator raises under a default caller":
    check native(sutClosure(5)) == "hit"
    check native(sutClosureNoRaise(5)) == "ran"

  test "native: a default closure iterator under a pushed caller does not raise":
    check native(callsPlainClosure(5)) == "hit"

  test "native: an inline iterator takes the caller's options":
    check native(sutInline(5)) == "ran"
    check native(sutInlineNoRaise(5)) == "hit"

  test "native: a default inline iterator under a pushed caller raises":
    check native(sutInlineInPushed(5)) == "hit"

  test "a pushed closure iterator raises FloatInvalidOpDefect":
    let r = symexFind(sutClosure, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check r.trusted

  test "and the no-raise path is unsat":
    let r = symexFind(sutClosureNoRaise, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status != sxSat

  test "a default closure iterator under a pushed caller does not raise":
    let r = symexFind(callsPlainClosure, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat

  test "an inline iterator is walked under the caller's options":
    let a = symexFind(sutInline, tLabel("hit"), pinSettingsConst)
    checkpoint show(a.errors) & " " & $a.soundness
    check a.status != sxSat
    let b = symexFind(sutInlineInPushed, tLabel("hit"), pinSettingsConst)
    checkpoint show(b.errors) & " " & $b.soundness
    check b.status == sxSat

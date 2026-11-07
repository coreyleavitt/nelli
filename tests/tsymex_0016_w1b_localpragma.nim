## RFC-0016 W1-b -- a local pragma outside the allowlist declines
## `feLocalPragma` (W-02). `{.cursor.}` makes the local share the source's
## memory, which the walk models as a copy: the verdict was a trusted false
## pair. `noinit` and `global` stay modelled.
import std/[unittest, os, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

putEnv("NELLI_PIN_DIR", getTempDir() / ("w1b_pins_" & $getCurrentProcessId()))

var gs: seq[int]

proc varCursor(k: int) =
  gs = @[k]
  var c {.cursor.} = gs
  gs[0] = 9
  if c[0] == 9: symexTarget("shared")

proc letCursor(k: int) =
  gs = @[k]
  let c {.cursor.} = gs
  gs[0] = 9
  if c[0] == 9: symexTarget("shared")

proc noinitSut(k: int) =
  var x {.noinit.}: int
  x = k
  if x == 7: symexTarget("hit")

var gcount {.global.}: int
proc globalSut(k: int) =
  var seen {.global.} = 0
  if k == 3 and seen == 0: symexTarget("hit")

suite "RFC-0016 W1-b: local pragmas":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 275

  test "native: a cursor aliases the source, so the write shows through":
    for k in [-5, 0, 3, 9]:
      check "shared" in nativeRun(varCursor(k)).hits
      check "shared" in nativeRun(letCursor(k)).hits

  test "var cursor declines feLocalPragma":
    pinDecline(varCursor, cellKey(axPragma, "local/cursor"), feLocalPragma,
               target = tLabel("shared"))

  test "let cursor declines feLocalPragma":
    pinDecline(letCursor, cellKey(axPragma, "local/cursor"), feLocalPragma,
               target = tLabel("shared"))

  test "the decline names the pragma":
    let r = symexFind(varCursor, tLabel("shared"), pinSettingsConst)
    check "cursor" in show(r.errors)

  test "noinit (written before read) is unchanged":
    discard pinExact(noinitSut, cellKey(axPragma, "local/noinit"))

  test "global is unchanged":
    discard pinExact(globalSut, cellKey(axPragma, "local/global"))

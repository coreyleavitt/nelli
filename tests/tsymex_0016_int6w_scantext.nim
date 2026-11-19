## RFC-0016 int6-w: the check-option scan reads a module's text from disk when
## a macro first asks, which can be after the compiler parsed the module. A
## file edited in between (an editor saving, a re-pin landing during a run) is
## read as the new text and placed by the old positions. Two lines added above
## a `{.push overflowChecks: off.}` routine put the push two lines below the
## position the compiler gave it, so the routine was read as checked and its
## `high(int) + 1` came back a trusted `sxRaised` (`OverflowDefect`), which the
## binary never raises: the run that found it (int6-o, 72bb313a) saw it only
## in-suite, as the re-pin rewrote the suite's header.
##
## This file makes that edit itself, deterministically: the first `static`
## block prepends two lines to `s0016_int6w_scantext_sut.nim` after the
## compiler has parsed it (it is imported above), and the last one removes
## them. Native, probed on the pinned toolchain (c and cpp): `chk*(high(int))`
## raises `OverflowDefect`; `off*(high(int))` raises nothing (the add is plain
## C, undefined on overflow). The control module is not rewritten, so each
## regime is walked as int6-o walks it in the same process, in the order that
## tripped (checked first, then pushed off).
import std/[unittest, strutils, os, tables]
import nelli
import nelli/symex
import ./s8cu_helpers
import ./s0016_int6w_scantext_ctl
import ./s0016_int6w_scantext_sut
import nelli/smt/check_scan

const shiftMark = "## int6-w: a line written while the compile ran"
const sutPath = currentSourcePath().parentDir / "s0016_int6w_scantext_sut.nim"

proc unshifted(t: string): string =
  for ln in t.splitLines(keepEol = true):
    if not ln.startsWith(shiftMark): result.add ln

static:
  # Two lines in; or, where an interrupted compile left them (the compiler
  # parsed them), two lines out. Either way the positions move.
  let now = staticRead(sutPath)
  let base = unshifted(now)
  writeFile(sutPath, (if base != now: base
                      else: shiftMark & "\n" & shiftMark & "\n" & base))

proc raisesOverflow(f: proc (v: int) {.nimcall.}; v: int): bool =
  try:
    f(v)
    false
  except OverflowDefect:
    true

proc show(tag: string; r: auto): string =
  var ks: seq[string]
  for e in r.errors: ks.add $e.kind
  tag & ": " & $r.status & " trusted=" & $r.trusted & " errors=" & ks.join(",")

var memFiles {.compileTime.}: Table[string, string]
proc memExists(p: string): bool = p in memFiles
proc memRead(p: string): string = memFiles[p]
proc memAnchor(p: string): string = p
const memEnv = SourceEnv(exists: memExists, read: memRead, anchor: memAnchor)

const
  # `textDisagrees` on a literal text: the pure scan, no disk.
  memScan = scanModuleText("mem/x.nim",
    "proc foo*() = discard\n\nproc `bar`() =\n  proc inner() = discard\n", memEnv)
  pure = [textDisagrees(memScan, "mem/x.nim", "foo", 1),    # 0 where it is written
          textDisagrees(memScan, "mem/x.nim", "bar", 3),    # 1 a quoted name
          textDisagrees(memScan, "mem/x.nim", "inner", 4),  # 2 a nested routine
          textDisagrees(memScan, "mem/x.nim", "f_oo", 1),   # 3 Nim's identifier equality
          textDisagrees(memScan, "mem/x.nim", "made", 2),   # 4 a name the text never defines
          textDisagrees(memScan, "mem/y.nim", "foo", 3),    # 5 a file the scan did not read
          textDisagrees(memScan, "mem/x.nim", "foo", 3),    # 6 moved
          textDisagrees(memScan, "mem/x.nim", "made", 9)]   # 7 past the text's end

suite "int6-w: the scan reads the text the compiler parsed":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 468

  test "pure: a routine is placed against the text the scan read":
    for i in 0 .. 5:
      checkpoint $i & ": " & pure[i]
      check pure[i] == ""
    check "defines `foo` at line 1, not at line 3" in pure[6]
    check "has 4 lines" in pure[7]

  test "native: checked raises, pushed off does not":
    check raisesOverflow(chkSteady, high(int))
    check not raisesOverflow(offSteady, high(int))
    check raisesOverflow(chkShifted, high(int))
    check not raisesOverflow(offShifted, high(int))

  test "control: each regime walked as its own, checked first":
    let c = symexFind(chkSteady, tLabel("hit"), defaultSymexSettings())
    checkpoint show("chkSteady", c)
    check c.status == sxRaised and c.trusted
    # native: `chkSteady(high(int))` raises OverflowDefect (test above)
    discard pinFind(chkSteady, tLabel("hit"), pinSettingsConst)
    let o = symexFind(offSteady, tLabel("hit"), defaultSymexSettings())
    checkpoint show("offSteady", o)
    check not o.trusted
    check o.errors.named(ubSignedOverflow)
    pinDecline(offSteady, cellKey(axDefinedness, "add/signed/scantext/steady"),
               ubSignedOverflow)

  test "rewritten: the pushed-off routine is never a trusted raise":
    let c = symexFind(chkShifted, tLabel("hit"), defaultSymexSettings())
    checkpoint show("chkShifted", c)
    let o = symexFind(offShifted, tLabel("hit"), defaultSymexSettings())
    checkpoint show("offShifted", o)
    check not (o.trusted and o.status == sxRaised)
    check not o.trusted
    check o.errors.named(feCheckOption)
    var said = false
    for e in o.errors:
      if e.kind == feCheckOption and "not the text the compiler parsed" in e.msg:
        said = true
    check said
    pinDecline(offShifted, cellKey(axDefinedness, "add/signed/scantext/shifted"),
               feCheckOption, needle = "not the text the compiler parsed")

  test "rewritten: the checked routine declines, it is not read either":
    let c = symexFind(chkShifted, tLabel("hit"), defaultSymexSettings())
    checkpoint show("chkShifted", c)
    check not c.trusted
    check c.errors.named(feCheckOption)
    pinDecline(chkShifted, cellKey(axDefinedness, "chk/signed/scantext/shifted"),
               feCheckOption)

static:
  writeFile(sutPath, unshifted(staticRead(sutPath)))

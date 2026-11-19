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
import std/[unittest, strutils, os]
import nelli
import nelli/symex
import ./s0016_int6w_scantext_ctl
import ./s0016_int6w_scantext_sut

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

func named(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true

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

suite "int6-w: the scan reads the text the compiler parsed":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 468

  test "native: checked raises, pushed off does not":
    check raisesOverflow(chkSteady, high(int))
    check not raisesOverflow(offSteady, high(int))
    check raisesOverflow(chkShifted, high(int))
    check not raisesOverflow(offShifted, high(int))

  test "control: each regime walked as its own, checked first":
    let c = symexFind(chkSteady, tLabel("hit"), defaultSymexSettings())
    checkpoint show("chkSteady", c)
    check c.status == sxRaised and c.trusted
    let o = symexFind(offSteady, tLabel("hit"), defaultSymexSettings())
    checkpoint show("offSteady", o)
    check not o.trusted
    check o.errors.named(ubSignedOverflow)

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

  test "rewritten: the checked routine declines, it is not read either":
    let c = symexFind(chkShifted, tLabel("hit"), defaultSymexSettings())
    checkpoint show("chkShifted", c)
    check not c.trusted
    check c.errors.named(feCheckOption)

static:
  writeFile(sutPath, unshifted(staticRead(sutPath)))

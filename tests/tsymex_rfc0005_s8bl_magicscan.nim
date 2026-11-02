## RFC-0005 (soundness channels) slice S8bl, item 1 -- the guard against a
## silent no-op magic. A system magic with a `var` parameter that no parser
## arm models was registered with an EMPTY body before S8bl, so its write to
## the argument was dropped without a record. Every such magic is now either
## modelled or declined by name (`varParamMagics`, `varMagicDecline`). This
## file scans the stdlib's system sources for `var`-parameter magics, so a
## toolchain that adds one fails here until it is classified.
import std/[unittest, os, strutils, compilesettings, sets]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/dsl_parser

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasMsg(errs: seq[SymexErrorInfo], needle: string): bool =
  for e in errs:
    if needle in e.msg: return true
  false

const nimLib = querySetting(libPath)

proc scanVarParamMagics(file: string): seq[tuple[routine, magic: string]] =
  ## The `proc`/`func` declarations of `file` with a `magic` pragma and a
  ## `var` formal. A declaration is read from its keyword to its pragma's
  ## close (`.}`) or its body's `=`, at most eight lines on.
  let lines = readFile(file).splitLines
  var i = 0
  while i < lines.len:
    let l = lines[i].strip
    if l.startsWith("proc ") or l.startsWith("func "):
      var decl = l
      var j = i
      while ".}" notin decl and not decl.endsWith("=") and j < i + 8 and
            j + 1 < lines.len:
        inc j
        decl.add " " & lines[j].strip
      let mg = decl.find("magic: \"")
      let po = decl.find('(')
      let pc = decl.find(')')
      if mg >= 0 and po >= 0 and pc > po:
        let params = decl[po + 1 ..< pc]
        if (" " & params.replace(":", " ") & " ").contains(" var "):
          let start = mg + "magic: \"".len
          let magic = decl[start ..< decl.find('"', start)]
          let head = decl.split({' ', '(', '[', '*'})
          result.add (routine: head[1], magic: magic)
    inc i

proc pnew(x: int) =
  var p: ref int
  unsafeNew(p, 8)
  if x == 1: symexTarget("unsafe_new")

proc idx(i: int): int = i + 1

proc pswapImpure(x: int) =
  var a = [x, 1, 2]
  swap(a[idx(x and 1)], a[0])   # an index with a call: read once, not twice
  if a[0] == 1: symexTarget("swap_impure")

suite "S8bl (1): every system magic with a var parameter is classified":
  test "the scan sees the stdlib's var-parameter magics":
    var files = @[nimLib / "system.nim"]
    for f in walkFiles(nimLib / "system" / "*.nim"): files.add f
    var found: seq[tuple[routine, magic: string]]
    for f in files: found.add scanVarParamMagics(f)
    checkpoint $found
    var names: HashSet[string]
    for m in found: names.incl m.magic
    # Not vacuous: the scan finds the magics S8bl was written against.
    for m in ["Swap", "WasMoved", "Move", "SetLengthSeq", "SetLengthStr",
              "AppendStrCh", "AppendStrStr", "AppendSeqElem", "Inc", "Dec",
              "New", "NewSeq", "Asgn", "Incl", "Excl"]:
      checkpoint m
      check m in names
    var classified: HashSet[string]
    for m in varParamMagics: classified.incl m.magic
    for m in found:
      checkpoint "unclassified var-parameter magic `" & m.routine &
                 "` (magic \"" & m.magic & "\"): add it to `varParamMagics`"
      check m.magic in classified

  test "a declined magic is a decline that names it, never a no-op":
    let r = symexFind(pnew, tLabel("unsafe_new"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasMsg("unsafeNew")
    check r.errors.hasMsg("magic \"New\"")
    let d = symexFind(pswapImpure, tLabel("swap_impure"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnknown
    check d.errors.hasMsg("magic \"Swap\"")

  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 213

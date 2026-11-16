## RFC-0016 code review (0.10.0), finding H7: `mayWriteMagics` omitted
## `mSetLengthSeqUninit`.
##
## A magic in Nim's `FakeVarParams` (`semdata.nim`) takes its `var` argument
## with no `nnkHiddenAddr`, so the "may write" scans read it by its magic
## (`mayWriteMagics`). `setLenUninit` is one, and was not listed:
## `lentLoopDecline` read `setLenUninit(s, 0)` in the body of `for x in s` as
## no write, and the walk kept `x` bound to the element read where it stood.
## Natively `x` holds the element's memory and sees the shrink: the walk found
## "one" trusted where Nim reaches "other".
##
## The cross-check below keeps the list whole: every magic Nim 2.2.10 lists in
## `FakeVarParams`, every `msVarStmt` row of `magicAxis`, and every magic
## declared under `lib/` with a `var` or `out` formal is in `mayWriteMagics`
## or carries a reason in `mayWriteMagicsExempt`.
import std/[unittest, strutils, os, sets, compilesettings]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/admission
import nelli/smt/magic_rows
import nelli/smt/dsl_parser

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

proc hSetLenUninit(n: int) =
  if n != 1: return
  var s = @["a", "bb", "ccc"]
  for x in s:
    setLenUninit(s, 0)
    if x.len == 1: symexTarget("slu_one")
    else: symexTarget("slu_other")

proc hSetLenUninitRead(n: int) =
  ## Precision: a body that does not write the container stays decided.
  if n != 1: return
  var s = @["a", "bb", "ccc"]
  var t = @[1]
  for x in s:
    setLenUninit(t, 0)
    if x.len == 1: symexTarget("slr_one")

suite "CR3 H7: setLenUninit in a lent loop body":
  test "native: the variable sees the shrink":
    let h = hits(hSetLenUninit(1))
    checkpoint $h
    check "slu_other" in h
    check "slu_one" notin h
  test "RED was a trusted sxSat on slu_one; now declined":
    template declined(lbl: static string) =
      block:
        let r = symexFind(hSetLenUninit, tLabel(lbl))
        checkpoint lbl & " " & $r.status & " trusted=" & $r.trusted & "\n" &
                   show(r.errors)
        check r.status == sxUnknown
        check "memory" in show(r.errors)
    declined("slu_one")
    declined("slu_other")
  test "precision: a shrink of another seq stays decided":
    let r = symexFind(hSetLenUninitRead, tLabel("slr_one"))
    checkpoint $r.status & "\n" & show(r.errors)
    check r.status == sxSat
    check r.trusted

# ---- the cross-check --------------------------------------------------------

const fakeVarParams_2_2_10 = ["New", "NewFinalize", "Inc", "Dec", "Incl",
  "Excl", "SetLengthStr", "SetLengthSeq", "SetLengthSeqUninit", "AppendStrCh",
  "AppendStrStr", "Swap", "AppendSeqElem", "NewSeq", "ShallowCopy", "DeepCopy",
  "Move", "WasMoved"]
  ## Nim 2.2.10 `compiler/semdata.nim`, `FakeVarParams`: the magics whose
  ## `var` argument carries no `nnkHiddenAddr`.

const nimLib = querySetting(libPath)

proc closeParen(decl: string): int =
  ## The `)` that closes `decl`'s formal list (`-1` if none yet): a formal of
  ## procedural type has parentheses, and a pragma, of its own.
  let po = decl.find('(')
  if po < 0: return -1
  var depth = 0
  for k in po ..< decl.len:
    if decl[k] == '(': inc depth
    elif decl[k] == ')':
      dec depth
      if depth == 0: return k
  -1

proc scanVarParamMagics(file: string): seq[tuple[routine, magic: string]] =
  ## The routine declarations of `file` with a `magic` pragma and a `var` or
  ## `out` formal, read from the keyword to the close (`.}`) of the pragma
  ## after the formal list, or the body's `=`, at most eight lines on
  ## (`tsymex_rfc0005_s8bl_magicscan`). The formal list is matched by depth:
  ## `new(a: var ref T, finalizer: proc (x: ref T) {.nimcall.})` holds a `)`
  ## and a pragma of its own.
  let lines = readFile(file).splitLines
  var i = 0
  while i < lines.len:
    let l = lines[i].strip
    if l.startsWith("proc ") or l.startsWith("func "):
      var decl = l
      var j = i
      proc ended(d: string): bool =
        let c = closeParen(d)
        (c >= 0 and d.find(".}", c) >= 0) or d.endsWith("=")
      while not ended(decl) and j < i + 8 and j + 1 < lines.len:
        inc j
        decl.add " " & lines[j].strip
      var mg = decl.find("magic: \"")
      var mlen = "magic: \"".len
      if mg < 0:
        mg = decl.find("magic:\"")
        mlen = "magic:\"".len
      let po = decl.find('(')
      let pc = closeParen(decl)
      if mg >= 0 and po >= 0 and pc > po:
        let params = " " & decl[po + 1 ..< pc].replace(":", " ") & " "
        if params.contains(" var ") or params.contains(" out "):
          let start = mg + mlen
          let magic = decl[start ..< decl.find('"', start)]
          let head = decl.split({' ', '(', '[', '*'})
          result.add (routine: head[1], magic: magic)
    inc i

proc listed(m: string): bool =
  if m in mayWriteMagics: return true
  for e in mayWriteMagicsExempt:
    if e.magic == m: return true

suite "CR3 H7: every var-writing magic is in mayWriteMagics or exempt":
  test "Nim's FakeVarParams":
    for m in fakeVarParams_2_2_10:
      checkpoint m
      check m in mayWriteMagics
  test "every msVarStmt row of magicAxis":
    var n = 0
    for k in magicAxis.keysAt(msVarStmt):
      inc n
      checkpoint k
      check listed(k)
    check n >= 8
  test "every magic with a var or out formal under lib/":
    var found: seq[tuple[routine, magic: string]]
    for f in walkDirRec(nimLib):
      if f.endsWith(".nim"): found.add scanVarParamMagics(f)
    var names: HashSet[string]
    for m in found: names.incl m.magic
    # Not vacuous: the scan sees the magics this finding is about.
    for m in ["SetLengthSeqUninit", "SetLengthSeq", "Swap", "Inc", "Asgn",
              "Destroy", "DeepCopy", "NewFinalize"]:
      checkpoint m
      check m in names
    for m in found:
      checkpoint "var-writing magic `" & m.routine & "` (magic \"" & m.magic &
                 "\") is neither in `mayWriteMagics` nor exempt"
      check listed(m.magic)
  test "an exemption carries a reason and is not also listed":
    for e in mayWriteMagicsExempt:
      checkpoint e.magic
      check e.reason.len > 0
      check e.magic notin mayWriteMagics

suite "CR3 H7: the walker version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 356

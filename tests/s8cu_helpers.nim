## RFC-0005 S8cu. What the suites share: the native check and the decline check.
import std/[sets, strutils]
import nelli/symex

proc show*(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs:
    if e.severity == sevError: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc named*(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k and e.severity == sevError: return true

template native*(call: untyped): string =
  ## "hit" if the call reached the label, the Defect's name if it raised, else
  ## "ran". On this build, so a wrong expectation fails with the verdict.
  block:
    var res = ""
    symexCaptureBegin()
    try:
      call
    except Defect as e:
      res = $e.name
    let hits = symexCaptureEnd()
    if res.len == 0: res = if "hit" in hits: "hit" else: "ran"
    res

template declines*(fn: untyped; kind: SymexErrorKind) =
  let r = symexFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == sxUnknown
  check r.errors.named(kind)

template decides*(fn: untyped; want: SymexStatusKind) =
  let r = symexFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == want

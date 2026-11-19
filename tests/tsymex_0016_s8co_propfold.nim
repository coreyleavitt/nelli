## RFC-0016 S8co (PRC-33 item 4b) -- 8.37's JIT's `detect_repeat` folds next
## to a character property. Auto-possessification decides which copies of a
## bracket are byte-identical (a possessified repeat is another opcode), and
## `compare_opcodes` reads a property through its PT_* type and data
## (`pcre_possess.propType`). The fold reader declined every fold next to a
## property it could not type (`Possess.unknown`); no pattern the reader
## accepts carries one: a `\p{name}` parses only when `name` is one of
## PCRE's (`pcre_props.pcrePropSet`), and each of those has its type. The
## decline is gone, and the typing is total over the accepted names (an
## untyped one is a defect, not a decline). Every accepted name is read in
## each mode, folds next to properties are compared with the native 8.37
## JIT, and the walker decides such a call.
##
## On the native 8.37 JIT (`scripts/dt-bounded.sh -i pcre-8.37-jit`) every
## corpus call is checked against std/re; the automaton is pinned anywhere.
import std/[unittest, re, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
import nelli/smt/pcre_props
import nelli/smt/pcre_ucd
import ./s8cu_helpers

const
  patterns = [
    "(?:\\p{L}a){3}", "(?:\\p{L}+1){3}", "(?:a\\p{Lu}+b){2,4}",
    "\\p{L}+(?:ab){3}", "(?:ab){1,3}\\p{N}+", "(?:\\d+\\p{N}){0,3}c",
    "(?:\\p{Ll}+\\p{Lu}){3}", "(?:\\p{L}+\\p{N})(?:\\p{L}+\\p{N})(?:\\p{L}+\\p{N})",
    "(?:\\p{L}*\\p{L}){2,3}x", "(?:\\P{N}+\\p{N}){1,3}", "(?:\\p{Lu}\\p{Ll}+){3,}",
    "(*UCP)(?:\\d+\\w){3}", "(*UCP)(?:\\w+\\s){1,3}", "(?:\\p{Xan}+-){2,3}",
    "(*UTF)(?:\\p{Lu}b){3}", "(*UTF)(?:a\\p{Greek}){1,3}"]
  subjects = ["", "aa1", "a1a1a1", "Ab1Ab1Ab1", "abababab", "11c", "1122c",
    "aBcDeF", "aBaBaB", "xx", "ab1ab1ab1", "aaaaaax", "123c", "ab-ab-ab-",
    "1 a b c ", "AbAbbAbbb", "a\xce\xb1a\xce\xb2", "AbAbAb"]
  limits = [1, 2, 3, 4, 5, 6, 7, 8, 10, 13]

proc names(): seq[string] =
  for (n, _) in pcrePropMaps: result.add n
  for n in pcreEmptyProps: result.add n
  for (n, _) in ucdProps: result.add n

proc propSym(s: string) =
  if s == "a1a1a1" and s.find(re"(*LIMIT_MATCH=3)(?:\p{L}+1){3}") == -8:
    symexTarget("co_propfold")

proc propSymNo(s: string) =
  if s == "a1a1a1" and s.find(re"(*LIMIT_MATCH=3)(?:\p{L}+1){3}") != -8:
    symexTarget("co_propfold_no")

suite "S8co item 4b: detect_repeat folds next to a character property":
  test "every accepted property name is typed, and its folds are read":
    var accepted, read, unread: int
    var bad: seq[string]
    for n in names():
      for mode in ["", "(*UTF)"]:
        for shape in ["\\p{$1}+\\p{$1}", "\\P{$1}*a", "a+\\p{$1}",
                      "(?:\\p{$1}+b){3}", "(?:b\\P{$1}?){2,4}"]:
          let q = "(*LIMIT_MATCH=5)" & mode & shape % [n]
          let pr = parsePcre(q)
          if pr.status != psOk: continue
          inc accepted
          let jit = buildNfa(pr, peJit837, limitRoom = 0)
          let interp = buildNfa(pr, peInterp, limitRoom = 0)
          for m in [jit, interp]:
            if m.ok: inc read
            elif "propert" in m.why or "detect_repeat" in m.why:
              bad.add q & ": " & m.why
            else: inc unread   # past the automaton's size cap
    echo "  accepted ", accepted, " read ", read, " size-capped ", unread,
         " declined next to a property ", bad.len
    for b in bad[0 ..< min(bad.len, 20)]: echo "  ", b
    check accepted >= 1000
    check bad.len == 0

  test "every limited call is read":
    var unread: seq[string]
    for p in patterns:
      for lim in limits:
        let q = "(*LIMIT_MATCH=" & $lim & ")" & p
        let pr = parsePcre(q)
        if pr.status != psOk:
          unread.add q & " parse " & $pr.status & " " & pr.reason
          continue
        let n = buildNfa(pr, peJit837, limitRoom = 0)
        if not n.ok or limitEffect(n)[0] == leUnknown:
          unread.add q & " ok=" & $n.ok & " " & n.why
    for u in unread[0 ..< min(unread.len, 20)]: echo "  unread ", u
    check unread.len == 0

  test "native JIT against the automaton":
    if not pcreRunsJit() or pcreVersion() != "8.37 2015-04-28":
      skipCell(cellKey(axBuild, "8.37 2015-04-28|jit"),
        "the native JIT 8.37 is not the PCRE this host runs (" & pcreVersion() &
        ", jit=" & $pcreRunsJit() & "); folds are compared against it only there")
    else:
      var bad: seq[string]
      var calls, stops = 0
      for p in patterns:
        for lim in limits:
          let q = "(*LIMIT_MATCH=" & $lim & ")" & p
          let pr = parsePcre(q)
          if pr.status != psOk: continue
          let n = buildNfa(pr, peJit837, limitRoom = 0)
          if not n.ok or limitEffect(n)[0] == leUnknown: continue
          let rx = re(q)
          for s in subjects:
            inc calls
            let got = pcreExec(n, s, 0, false)
            let want = find(s, rx)
            let g = if got[0] >= 0: got[1] else: got[0]
            if g == pcreErrMatchLimit: inc stops
            if g != want and bad.len < 40:
              bad.add escape(q) & " on " & escape(s) & ": model " & $g &
                      " native " & $want
      echo "  calls ", calls, " stops ", stops, " differ ", bad.len
      for b in bad: echo "  ", b
      check bad.len == 0
      check stops > 0
      check find("a1a1a1", re"(*LIMIT_MATCH=3)(?:\p{L}+1){3}") == -8

  test "the walker decides a fold next to a property":
    check parseInt(symexWalkerVersion) >= 393
    overridePcreLib("8.37 2015-04-28", true)
    defer: clearPcreLibOverride()
    check pinFind(propSym, tLabel("co_propfold")).status == sxSat
    check pinFind(propSymNo, tLabel("co_propfold_no")).status == sxUnsat

## RFC-0005 (soundness channels) slice S5 -- classify the `degradeStrArm`
## funnel and the R1 placeholder funnel (§5 row S5, §3.1's substitution
## rule, §3.2's split discipline). Verdict-changing: walker 142 -> 143.
##
## What the site-by-site audit found (every row is pinned in suite (a)):
##
## `degradeStrArm` (`runtime.nim`) converts the classified raises of
## `lowerStrArm` (`runtime_strings.nim`) into a FRESH, per-read
## (`freshDegradeName`), unconstrained symbol of the op's result sort (its
## `allocateSym` init facts are discarded). The funnel's name still does not
## decide the class -- what the degraded op DROPS does:
##   - `seBytesLengthTooLarge` (`bytes(<literal>)` over the cap): the receiver
##     is a literal, nothing is dropped. `dcFreshSymbol` as found.
##   - `seBytesSymbolicLength`, `seZ3VersionMissing`, and the lowering-time
##     `seZ3StringIncomplete` sites RAISED BEFORE LOWERING THEIR OPERANDS, so
##     an operand's own effects -- a `div`-by-zero / `parseInt` / index raise
##     fork deposited during its lowering, a closure descent -- were DROPPED
##     with the op. That removes behaviours (a raise the real program takes),
##     i.e. an under-approximation hiding inside a "fresh symbol" site: under
##     `dcFreshSymbol` it proved a caught `DivByZeroDefect` unreachable (a
##     false `sxUnsat`, pinned RED in suite (d)). S5 lowers the operands
##     first (and, for regex replace, parses the pattern first, so an
##     unsupported pattern keeps its ⊤ `seUnsupportedRegex`), then declines.
##   - `seZ3StringIncomplete` was ALSO emitted by two PARSE-time sites
##     (`runeLen(s)` / `for r in s.runes` over a symbolic string), which
##     substitute a forced `0` / drop the loop body (`dcSubstituted`). §3.2
##     split: the minority funnel gets the tail-appended
##     `seRuneDecodeSymbolic` (`dcSubstituted`); the lowering-time majority
##     keeps `seZ3StringIncomplete` and becomes `dcFreshSymbol`.
##   - `seUnsupportedStringOp` stays ⊤: its catch-all carries ops whose real
##     counterpart RAISES (`parseFloat` -> `ValueError`) with the raise
##     dropped; its `requireStr` sites drop `s[i]`'s `IndexDefect` and
##     `parseInt`'s `ValueError` forks; `iekStrSubstr`'s bound decline names
##     every occurrence `__strSubstrBoundDegrade` (shared across reads); the
##     `strip` parse site substitutes `""`.
##   - `seUnsupportedRegex` stays ⊤: a MALFORMED pattern raises `RegexError`
##     in reality (`re"…"` compiles at run time), which the decline drops.
##
## The R1 placeholder funnel (`placeholderReadDeclineKind`) records
## `seNestedSeqUnsupported` or `weInternalWalkerFault` -- both stay ⊤, and
## RFC §3.1's "R1 placeholder funnel = fresh symbol" is corrected here:
## `iekSeqLen`'s decline names every occurrence `__seqLenPlaceholderDecline`
## (two placeholders' lengths correlate), `isIndex`'s decline continues
## WITHOUT binding the destination and WITHOUT the `IndexDefect` fork,
## `iekSeqSlice`/`.add`/`.del` return the flagged receiver without lowering
## their bound/argument operands, `iteSV` forwards one operand, and the kind
## has a parse-time statement-drop site. Suite (e) pins that a run through it
## keeps an unreachable target `sxUnknown`.
##
## Flip audit (§4.3): pins that flipped are rewritten through
## `checkUnsatOverTaintOnly` in the slice that flipped them.
import std/[unittest, strutils, os, unicode]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import audit_scan_utils

proc kindNames(errs: seq[SymexErrorInfo]): seq[string] =
  for e in errs: result.add $e.kind

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc sevErrorKinds(errs: seq[SymexErrorInfo]): seq[SymexErrorKind] =
  for e in errs:
    if e.severity == sevError and e.kind notin result: result.add e.kind

# `replaceAll` / `bytes` are not Nim stdlib procs; the symex parser intercepts
# them BY NAME on an `itString` receiver (smkStrReplaceAll / smkStrBytes).
# The bodies never run under symex (the S5_strops / S7a_bytes shim idiom).
proc replaceAll(s, old, neu: string): string = s.replace(old, neu)
proc bytes(s: string): seq[byte] =
  for c in s: result.add byte(c)

# `std/re` needs libpcre at run time, which the podman test image does not
# ship (why `tsymex_phase15_S6b_regex` is red there). The parser routes a
# regex call BY NAME -- callee `match`/`replace` with an `re"…"` generalized
# raw-string argument (`dsl_parser.nim`, Phase 15 S6b) -- so a local `re`
# shim drives the identical `iekStrMatch` / `iekStrReplaceRe` IR. The bodies
# implement the real semantics of exactly the patterns used here (`c+` and
# `(.)\1`) for the oracles; they never run under symex.
type S5Re = object
  pat: string

proc re(p: string): S5Re = S5Re(pat: p)

proc replace(s: string; r: S5Re; repl: string): string =
  doAssert r.pat.len == 2 and r.pat[1] == '+', "shim models `c+` only"
  var i = 0
  while i < s.len:
    if s[i] == r.pat[0]:
      result.add repl
      while i < s.len and s[i] == r.pat[0]: inc i
    else:
      result.add s[i]
      inc i

proc match(s: string; r: S5Re): bool =
  doAssert r.pat == "(.)\\1", "shim models `(.)\\1` only"
  s.len >= 2 and s[0] == s[1]

const lit33 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"   ## > maxBytesEncodingLen (32)

# ---- (b) over-taint-only, target unreachable: one SUT per classified kind ---

proc s5DeadBytesTooLarge(s: string, n: int) =
  let b = bytes("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
  discard b
  if n == 5 and n == 6:
    symexTarget("s5_dead_bytes_too_large")

proc s5DeadBytesSymbolic(s: string, n: int) =
  let b = bytes(s)
  discard b
  if n == 5 and n == 6:
    symexTarget("s5_dead_bytes_symbolic")

proc s5DeadReplaceAll(s: string, n: int) =
  let t = s.replaceAll("a", "b")
  discard t
  if n == 5 and n == 6:
    symexTarget("s5_dead_replace_all")

proc s5DeadReplaceRe(s: string, n: int) =
  let t = s.replace(re"a+", "b")
  discard t
  if n == 5 and n == 6:
    symexTarget("s5_dead_replace_re")

proc s5DeadSplit(s: string, n: int) =
  let parts = s.split(",")
  discard parts
  if n == 5 and n == 6:
    symexTarget("s5_dead_split")

proc s5DeadJoin(s: string, n: int) =
  let j = s.split(",").join("-")
  discard j
  if n == 5 and n == 6:
    symexTarget("s5_dead_join")

## The contradiction runs THROUGH the fresh value: no string is both.
proc s5DeadThroughValue(s: string) =
  let t = s.replaceAll("a", "b")
  if t == "x" and t == "y":
    symexTarget("s5_dead_through_value")

# ---- (c) introduction invariant: fresh per read, no constraint -------------

proc s5TwoCellsReplaceAll(a, b: string) =
  if a.replaceAll("x", "y") != b.replaceAll("x", "y"):
    symexTarget("s5_two_cells_replace_all")

proc s5TwoCellsReplaceRe(a, b: string) =
  if a.replace(re"x+", "y") != b.replace(re"x+", "y"):
    symexTarget("s5_two_cells_replace_re")

proc s5TwoCellsBytes(a, b: string) =
  if bytes(a).len != bytes(b).len:
    symexTarget("s5_two_cells_bytes")

proc s5TwoCellsSplit(a, b: string) =
  if a.split(",").len != b.split(",").len:
    symexTarget("s5_two_cells_split")

proc s5TwoCellsJoin(a, b: string) =
  if a.split(",").join("-") != b.split(",").join("-"):
    symexTarget("s5_two_cells_join")

## Repeat hits of the SAME site across loop iterations.
proc s5TwoCellsLoop(a, b: string) =
  var first = ""
  var differ = false
  for i in 0 .. 1:
    let cur = if i == 0: a.replaceAll("x", "y") else: b.replaceAll("x", "y")
    if i == 0: first = cur
    elif cur != first: differ = true
  if differ:
    symexTarget("s5_two_cells_loop")

## The REAL value is reachable: `bytes(lit33)` really has length 33 and its
## first byte really is 'a'. A placeholder forced to anything (length 0) would
## prove this unreachable.
proc s5TooLargeRealValue(s: string) =
  let b = bytes("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
  if b.len == 33 and b[0] == 97'u8:
    symexTarget("s5_too_large_real_value")

# ---- (d) operand effects survive the decline (RED before S5's fix) ---------

proc s5EffReplaceAll(s: string, a, b: int) =
  try:
    let t = replaceAll($(a div b), "x", "y")
    discard t
  except DivByZeroDefect:
    symexTarget("s5_eff_replace_all")

proc s5EffReplaceRe(s: string, a, b: int) =
  try:
    let t = ($(a div b)).replace(re"x+", "y")
    discard t
  except DivByZeroDefect:
    symexTarget("s5_eff_replace_re")

proc s5EffBytes(s: string, a, b: int) =
  try:
    let t = bytes($(a div b))
    discard t
  except DivByZeroDefect:
    symexTarget("s5_eff_bytes")

proc s5EffSplitGeneral(s: string, a, b: int) =
  try:
    let t = ($(a div b)).split(",")
    discard t
  except DivByZeroDefect:
    symexTarget("s5_eff_split_general")

proc s5EffSplitSep(s: string, a, b: int) =
  try:
    let t = s.split($(a div b))
    discard t
  except DivByZeroDefect:
    symexTarget("s5_eff_split_sep")

proc s5EffSplitEmptySep(s: string, a, b: int) =
  try:
    let t = ($(a div b)).split("")
    discard t
  except DivByZeroDefect:
    symexTarget("s5_eff_split_empty_sep")

proc s5EffJoin(s: string, a, b: int) =
  try:
    let t = s.split(",").join($(a div b))
    discard t
  except DivByZeroDefect:
    symexTarget("s5_eff_join")

# ---- guard: reachable ONLY through the fresh value -------------------------

proc s5LiveReplaceAll(s: string) =
  if s.replaceAll("a", "b") == "zzz":
    symexTarget("s5_live_replace_all")

proc s5LiveSplit(s: string) =
  if s.split(",").len == 2:
    symexTarget("s5_live_split")

proc s5LiveBytes(s: string) =
  if bytes(s).len == 3:
    symexTarget("s5_live_bytes")

# ---- (e) must-NOT-promote: the funnels' ⊤ kinds -----------------------------

proc s5ToOctDead(x: int, n: int) =
  let t = toOct(x, 3)
  discard t
  if n == 5 and n == 6:
    symexTarget("s5_tooct_dead")

proc s5BackrefDead(s: string, n: int) =
  if s.match(re"(.)\1"):
    discard
  if n == 5 and n == 6:
    symexTarget("s5_backref_dead")

type S5Holder = object
  count: int
  opts: seq[(string, string)]   ## unbacked elem (itTuple) -> R1 placeholder

proc s5PlaceholderLenDead(v: var S5Holder, n: int) =
  if v.opts.len > 0:
    discard
  if n == 5 and n == 6:
    symexTarget("s5_placeholder_len_dead")

proc s5RuneLenDead(s: string, n: int) =
  let k = runeLen(s)
  discard k
  if n == 5 and n == 6:
    symexTarget("s5_runelen_dead")

proc s5RunesLoopDead(s: string, n: int) =
  var c = 0
  for r in s.runes:
    c += 1
  discard c
  if n == 5 and n == 6:
    symexTarget("s5_runes_loop_dead")

## `seRuneDecodeSymbolic` substitutes: `runeLen(s)` is forced to 0, so a
## target reachable ONLY at a nonzero rune count must never go sxUnsat.
proc s5RuneLenLive(s: string) =
  if runeLen(s) == 2:
    symexTarget("s5_runelen_live")

# =============================================================================
# Oracles -- the same facts executed for real (house rule)
# =============================================================================

suite "RFC-0005 S5 -- oracles":

  test "oracle: n == 5 and n == 6 is a genuine contradiction":
    for n in [0, 5, 6, -1]:
      check not (n == 5 and n == 6)

  test "oracle: the degraded ops are total over these inputs (no raise to drop)":
    for s in ["", "a,b", "aaa", "x"]:
      discard s.replaceAll("a", "b")
      discard s.replace(re"a+", "b")
      discard bytes(s)
      discard s.split(",").join("-")
    check bytes(lit33).len == 33
    check bytes(lit33)[0] == 97'u8

  test "oracle: the two-cell targets are reachable (distinct inputs, distinct results)":
    check "a".replaceAll("x", "y") != "b".replaceAll("x", "y")
    check "a".replace(re"x+", "y") != "b".replace(re"x+", "y")
    check bytes("a").len != bytes("ab").len
    check "a".split(",").len != "a,b".split(",").len
    check "a".split(",").join("-") != "b".split(",").join("-")

  test "oracle: every dropped-effect target is reachable (b == 0 raises DivByZeroDefect)":
    var hits = 0
    proc probe(body: proc ()) =
      try: body()
      except DivByZeroDefect: inc hits
    let z = 0
    probe(proc () = discard replaceAll($(1 div z), "x", "y"))
    probe(proc () = discard ($(1 div z)).replace(re"x+", "y"))
    probe(proc () = discard bytes($(1 div z)))
    probe(proc () = discard ($(1 div z)).split(","))
    probe(proc () = discard "s".split($(1 div z)))
    probe(proc () = discard ($(1 div z)).split(""))
    probe(proc () = discard "s".split(",").join($(1 div z)))
    check hits == 7

  test "oracle: the live targets are reachable":
    check "zzz".replaceAll("a", "b") == "zzz"
    check "a,b".split(",").len == 2
    check bytes("abc").len == 3
    check runeLen("ab") == 2

# =============================================================================
# (a) the classification rows S5 wrote (types.nim `classOf`, rows marked S5)
# =============================================================================

suite "RFC-0005 S5 (a) -- the degradeStrArm / R1 funnels' classOf rows":

  test "the fresh-per-read, effect-preserving kinds are dcFreshSymbol":
    for k in [seBytesLengthTooLarge, seBytesSymbolicLength, seZ3VersionMissing,
              seZ3StringIncomplete]:
      checkpoint($k)
      check classOf(k) == dcFreshSymbol
      check channels(k).path == {scSpurious}
      check channels(k).run == {scSpurious}

  test "the rune-decode parse sites split off as seRuneDecodeSymbolic, dcSubstituted":
    check classOf(seRuneDecodeSymbolic) == dcSubstituted
    check scIncomplete in runTaint(classOf(seRuneDecodeSymbolic))

  test "the split is a TAIL append (ordinal stability, §3.2)":
    ## RFC-0005 S6a tail-appended after this kind; adjacency, not `.high`.
    check ord(heUnsupportedPointeeRead) + 1 == ord(seRuneDecodeSymbolic)

  test "the funnels' substituting / effect-dropping kinds stay ⊤":
    for k in [seUnsupportedStringOp, seUnsupportedRegex, seNestedSeqUnsupported,
              weInternalWalkerFault]:
      checkpoint($k)
      check classOf(k) == dcNoAnswer
      check scIncomplete in runTaint(classOf(k))

# =============================================================================
# (b) the flip: over-taint-only runs that prove the target unreachable
# =============================================================================

suite "RFC-0005 S5 (b) -- over-taint-only UNSAT, one SUT per classified kind":

  test "seBytesLengthTooLarge: bytes(<33-byte literal>) -> sxUnsat":
    let r = symexFind(s5DeadBytesTooLarge, tLabel("s5_dead_bytes_too_large"))
    checkpoint($kindNames(r.errors))
    checkUnsatOverTaintOnly(r)
    check sevErrorKinds(r.errors) == @[seBytesLengthTooLarge]

  test "seBytesSymbolicLength: bytes(s) -> sxUnsat":
    let r = symexFind(s5DeadBytesSymbolic, tLabel("s5_dead_bytes_symbolic"))
    checkpoint($kindNames(r.errors))
    checkUnsatOverTaintOnly(r)
    check sevErrorKinds(r.errors) == @[seBytesSymbolicLength]

  test "seZ3VersionMissing (replaceAll): -> sxUnsat":
    let r = symexFind(s5DeadReplaceAll, tLabel("s5_dead_replace_all"))
    checkpoint($kindNames(r.errors))
    checkUnsatOverTaintOnly(r)
    check sevErrorKinds(r.errors) == @[seZ3VersionMissing]

  test "seZ3VersionMissing (regex replace, supported pattern): -> sxUnsat":
    let r = symexFind(s5DeadReplaceRe, tLabel("s5_dead_replace_re"))
    checkpoint($kindNames(r.errors))
    checkUnsatOverTaintOnly(r)
    check sevErrorKinds(r.errors) == @[seZ3VersionMissing]

  test "seZ3StringIncomplete (general split): -> sxUnsat":
    let r = symexFind(s5DeadSplit, tLabel("s5_dead_split"))
    checkpoint($kindNames(r.errors))
    checkUnsatOverTaintOnly(r)
    check sevErrorKinds(r.errors) == @[seZ3StringIncomplete]

  test "seZ3StringIncomplete (join over a symbolic-length split): -> sxUnsat":
    let r = symexFind(s5DeadJoin, tLabel("s5_dead_join"))
    checkpoint($kindNames(r.errors))
    checkUnsatOverTaintOnly(r)
    check sevErrorKinds(r.errors) == @[seZ3StringIncomplete]

  test "a contradiction THROUGH the fresh value is still sxUnsat (the symbol is free, not pinned)":
    let r = symexFind(s5DeadThroughValue, tLabel("s5_dead_through_value"))
    checkpoint($kindNames(r.errors))
    checkUnsatOverTaintOnly(r)
    check sevErrorKinds(r.errors) == @[seZ3VersionMissing]

  test "guard: a target reachable ONLY through the fresh value is a candidate -- sxUnknown, never sxUnsat":
    for (name, r) in [
        ("replaceAll", symexFind(s5LiveReplaceAll, tLabel("s5_live_replace_all")).status),
        ("split", symexFind(s5LiveSplit, tLabel("s5_live_split")).status),
        ("bytes", symexFind(s5LiveBytes, tLabel("s5_live_bytes")).status)]:
      checkpoint(name & " -> " & $r)
      check r == sxUnknown

# =============================================================================
# (c) §2.1's introduction invariant for every dcFreshSymbol kind
# =============================================================================

suite "RFC-0005 S5 (c) -- introduction invariant: fresh per read, no constraint":

  test "seZ3VersionMissing: two cells' replaceAll results are independent -- never sxUnsat":
    let r = symexFind(s5TwoCellsReplaceAll, tLabel("s5_two_cells_replace_all"))
    checkpoint($kindNames(r.errors))
    check r.status != sxUnsat
    check r.errors.hasKind(seZ3VersionMissing)

  test "seZ3VersionMissing: two cells' regex-replace results are independent -- never sxUnsat":
    let r = symexFind(s5TwoCellsReplaceRe, tLabel("s5_two_cells_replace_re"))
    checkpoint($kindNames(r.errors))
    check r.status != sxUnsat
    check r.errors.hasKind(seZ3VersionMissing)

  test "seBytesSymbolicLength: two cells' byte views are independent -- never sxUnsat":
    let r = symexFind(s5TwoCellsBytes, tLabel("s5_two_cells_bytes"))
    checkpoint($kindNames(r.errors))
    check r.status != sxUnsat
    check r.errors.hasKind(seBytesSymbolicLength)

  test "seZ3StringIncomplete: two cells' splits are independent -- never sxUnsat":
    let r = symexFind(s5TwoCellsSplit, tLabel("s5_two_cells_split"))
    checkpoint($kindNames(r.errors))
    check r.status != sxUnsat
    check r.errors.hasKind(seZ3StringIncomplete)

  test "seZ3StringIncomplete: two cells' joins are independent -- never sxUnsat":
    let r = symexFind(s5TwoCellsJoin, tLabel("s5_two_cells_join"))
    checkpoint($kindNames(r.errors))
    check r.status != sxUnsat
    check r.errors.hasKind(seZ3StringIncomplete)

  test "repeat hits of one site across loop iterations are independent -- never sxUnsat":
    let r = symexFind(s5TwoCellsLoop, tLabel("s5_two_cells_loop"))
    checkpoint($kindNames(r.errors))
    check r.status != sxUnsat

  test "seBytesLengthTooLarge: the placeholder admits the REAL value (len 33, byte 'a') -- never sxUnsat":
    let r = symexFind(s5TooLargeRealValue, tLabel("s5_too_large_real_value"))
    checkpoint($kindNames(r.errors))
    check r.status != sxUnsat
    check r.errors.hasKind(seBytesLengthTooLarge)

  test "structural: degradeStrArm allocates only through freshDegradeName and never asserts its init facts":
    const rtSrc = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                  "smt" / "runtime.nim"
    var inBody = false
    var body = ""
    var freshUses: seq[string]
    for raw in readFile(rtSrc).splitLines():
      if raw.startsWith("proc degradeStrArm("):
        inBody = true
        continue
      if inBody and raw.len > 0 and not raw.startsWith(" "):
        break                              ## next top-level decl ends the body
      if not inBody: continue
      let t = raw.strip()
      if t.len == 0 or isCommentLine(t): continue
      body.add t & " "
      if "fresh" in t and "freshDegradeName" notin t and
         not t.startsWith("var fresh"):
        freshUses.add t
    ## One chunk per `allocateSym(` call (a call may wrap across lines).
    let chunks = body.split("allocateSym(")[1 .. ^1]
    checkpoint($chunks)
    checkpoint($freshUses)
    check chunks.len >= 6
    for c in chunks:
      check "freshDegradeName(" in c
    ## `fresh` appears only as allocateSym's discarded out-param.
    for u in freshUses:
      check u.endsWith("fresh)") or u.endsWith("fresh,") or
            "fresh, intOffsetPositions" in u or "allocateSym(" in u

  test "structural: every lowering-time dcFreshSymbol raise lowers its operands first":
    ## The S5 audit's effect rule, as a source pin: in each of these arms the
    ## operand `lower(env, ...)` precedes the classified raise, so a raise
    ## fork the operand deposits is never dropped with the op.
    const strSrc = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                   "smt" / "runtime_strings.nim"
    let src = readFile(strSrc)
    for (arm, carrier) in [("of iekStrReplaceAll:", "SymexZ3VersionMissingError"),
                           ("of iekStrReplaceRe:", "SymexZ3VersionMissingError"),
                           ("of iekStrBytes:", "SymexBytesSymbolicLengthError")]:
      let a = src.find(arm)
      check a >= 0
      let r = src.find("raise (ref " & carrier & ")", a)
      let l = src.find("lower(env, e.strArgs[0])", a)
      checkpoint(arm & " lower@" & $l & " raise@" & $r)
      check r > a
      check l > a and l < r

# =============================================================================
# (d) operand effects survive the decline (RED before S5 lowered them first)
# =============================================================================

suite "RFC-0005 S5 (d) -- a caught operand raise is never dropped with the op":

  test "replaceAll($(a div b), ...): the DivByZeroDefect handler is reachable -- never sxUnsat":
    let r = symexFind(s5EffReplaceAll, tLabel("s5_eff_replace_all"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.status != sxUnsat

  test "($(a div b)).replace(re, ...): never sxUnsat":
    let r = symexFind(s5EffReplaceRe, tLabel("s5_eff_replace_re"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.status != sxUnsat

  test "bytes($(a div b)): never sxUnsat":
    let r = symexFind(s5EffBytes, tLabel("s5_eff_bytes"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.status != sxUnsat

  test "($(a div b)).split(\",\") (general path, receiver effect): never sxUnsat":
    let r = symexFind(s5EffSplitGeneral, tLabel("s5_eff_split_general"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.status != sxUnsat

  test "s.split($(a div b)) (general path, separator effect): never sxUnsat":
    let r = symexFind(s5EffSplitSep, tLabel("s5_eff_split_sep"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.status != sxUnsat

  test "($(a div b)).split(\"\") (empty-sep path, receiver effect): never sxUnsat":
    let r = symexFind(s5EffSplitEmptySep, tLabel("s5_eff_split_empty_sep"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.status != sxUnsat

  test "s.split(\",\").join($(a div b)) (join separator effect): never sxUnsat":
    let r = symexFind(s5EffJoin, tLabel("s5_eff_join"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.status != sxUnsat

# =============================================================================
# (e) must-NOT-promote: the funnels' ⊤ kinds keep blocking sxUnsat
# =============================================================================

suite "RFC-0005 S5 (e) -- the funnels' substituting kinds stay ⊤":

  test "seUnsupportedStringOp (toOct, the S3 F2 shape) keeps an unreachable target sxUnknown":
    let r = symexFind(s5ToOctDead, tLabel("s5_tooct_dead"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(seUnsupportedStringOp)

  test "seUnsupportedRegex (backreference) keeps an unreachable target sxUnknown":
    let r = symexFind(s5BackrefDead, tLabel("s5_backref_dead"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(seUnsupportedRegex)

  test "seNestedSeqUnsupported (R1 placeholder .len) keeps an unreachable target sxUnknown":
    let r = symexFind(s5PlaceholderLenDead, tLabel("s5_placeholder_len_dead"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(seNestedSeqUnsupported)

  test "seRuneDecodeSymbolic (runeLen, forced 0) keeps an unreachable target sxUnknown":
    let r = symexFind(s5RuneLenDead, tLabel("s5_runelen_dead"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(seRuneDecodeSymbolic)
    check not r.errors.hasKind(seZ3StringIncomplete)

  test "seRuneDecodeSymbolic (runes loop, body dropped) keeps an unreachable target sxUnknown":
    let r = symexFind(s5RunesLoopDead, tLabel("s5_runes_loop_dead"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(seRuneDecodeSymbolic)

  test "seRuneDecodeSymbolic: a target live only past the forced 0 is never sxUnsat":
    let r = symexFind(s5RuneLenLive, tLabel("s5_runelen_live"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown

suite "RFC-0005 S5 -- walker version pin":

  test "walker version floor >= 143 (S5 classifies the degradeStrArm funnel)":
    check parseInt(symexWalkerVersion) >= 143

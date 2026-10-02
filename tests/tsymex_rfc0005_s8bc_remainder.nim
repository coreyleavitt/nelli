## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder.
import std/[unittest, strutils, sequtils, tables, sets, hashes]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

template replays(call: untyped; label: string) =
  ## The witness is typed (the parameter was not demoted) and replays.
  when compiles(call):
    check reproduces(call, label)
  else:
    checkpoint "the witness of `" & astToStr(call) & "` is not typed"
    check false

# ---- (1) `getOrDefault` -----------------------------------------------------

proc hcAnd(s: string) =
  # `Hash` is a plain alias the model does not classify, so `hc` holds a
  # declined placeholder; `and` on it was a walker fault (`r.kind == svBool`).
  var hc: Hash
  hc = hash(s)
  if (hc and 7) == 3: symexTarget("hc_and")

proc godPresent(t: Table[string, int]) =
  if t.getOrDefault("a") == 3: symexTarget("god_present")

proc godAbsent(t: Table[string, int]) =
  if "a" notin t and t.getOrDefault("a") == 0: symexTarget("god_absent")
  if "a" notin t and t.getOrDefault("a") != 0: symexTarget("god_absent_dead")

proc godAnd(t: Table[string, int], x: int) =
  if x == 1 and t.getOrDefault("a", 7) == 7: symexTarget("god_and")

proc godDef(t: Table[string, int]) =
  if "a" notin t and t.getOrDefault("a", 5) == 5: symexTarget("god_def")
  if "a" notin t and t.getOrDefault("a", 5) != 5: symexTarget("god_def_dead")
  if "a" in t and t["a"] == 2 and t.getOrDefault("a", 5) != 2:
    symexTarget("god_def_dead2")

proc godLocal(k: string, x: int) =
  var t = initTable[string, int]()
  t[k] = x
  if t.getOrDefault(k, 1) == 6 and t.getOrDefault("q", 9) == 9 and k != "q":
    symexTarget("god_local")
  if t.getOrDefault(k, 1) != x: symexTarget("god_local_dead")

proc godSeq(t: Table[string, seq[int]]) =
  if "a" notin t and t.getOrDefault("a").len == 0 and t.len == 1:
    symexTarget("god_seq")
  if "a" notin t and t.getOrDefault("a").len != 0: symexTarget("god_seq_dead")
  if "a" in t and t.getOrDefault("a").len == 2 and t["a"][1] == 4:
    symexTarget("god_seq_present")

proc godNan(x: int) =
  var t = initTable[float, int]()
  let n = NaN
  t[n] = 1
  if t.getOrDefault(n, 4) == 4 and x == 2: symexTarget("god_nan")
  if t.getOrDefault(n, 4) != 4: symexTarget("god_nan_dead")

suite "S8bc (1): getOrDefault":
  test "a declined `Hash` under `and` is a scoped decline, not a walker fault":
    let r = symexFind(hcAnd, tLabel("hc_and"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check not r.errors.hasKind(weInternalWalkerFault)

  test "a present key's value":
    let r = symexFind(godPresent, tLabel("god_present"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat: replays(godPresent(r.witness[0]), "god_present")

  test "an absent key is default(V)":
    let r = symexFind(godAbsent, tLabel("god_absent"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(godAbsent(r.witness[0]), "god_absent")
    let d = symexFind(godAbsent, tLabel("god_absent_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "under `and`":
    let r = symexFind(godAnd, tLabel("god_and"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat:
      replays(godAnd(r.witness[0], r.witness[1]), "god_and")

  test "an explicit default":
    let r = symexFind(godDef, tLabel("god_def"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(godDef(r.witness[0]), "god_def")
    block:
      let d = symexFind(godDef, tLabel("god_def_dead"))
      checkpoint "god_def_dead " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat
    block:
      let d = symexFind(godDef, tLabel("god_def_dead2"))
      checkpoint "god_def_dead2 " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat

  test "a local table":
    let r = symexFind(godLocal, tLabel("god_local"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(godLocal(r.witness[0], r.witness[1]), "god_local")
    let d = symexFind(godLocal, tLabel("god_local_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a seq value: absent is the empty seq":
    let r = symexFind(godSeq, tLabel("god_seq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(godSeq(r.witness[0]), "god_seq")
    let d = symexFind(godSeq, tLabel("god_seq_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let p = symexFind(godSeq, tLabel("god_seq_present"))
    checkpoint $p.status & " " & show(p.errors)
    check p.status == sxSat
    if p.status == sxSat: replays(godSeq(p.witness[0]), "god_seq_present")

  test "a NaN key is never found, so it is the default":
    let r = symexFind(godNan, tLabel("god_nan"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(godNan, tLabel("god_nan_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

suite "S8bc: walker version floor":
  test "walker version floor >= 203":
    check parseInt(symexWalkerVersion) >= 203

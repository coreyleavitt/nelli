## RFC-0005 (soundness channels) slice S8at -- S8ar's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 6 of 6 of this suite, with
## `tsymex_rfc0005_s8at_remainder`, `tsymex_rfc0005_s8at_remainder_b`,
## `tsymex_rfc0005_s8at_remainder_c`, `tsymex_rfc0005_s8at_remainder_d`,
## `tsymex_rfc0005_s8at_remainder_e`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 115 s).

import std/[unittest, strutils, sequtils, tables, sets]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

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

# ---- (5) a `distinct` over a composite base ---------------------------------

type
  DSq = distinct seq[int]
  DTp = distinct (int, bool)
  DSH = ref object
    ds: DSq
    dt: DTp
    n: int

proc len(d: DSq): int {.borrow.}

proc tcBranch(x: int) =
  var t = initTable[string, seq[int]]()
  if x > 0: t["a"] = @[1]
  else: t["a"] = @[1, 2]
  if t["a"].len == 2 and x == -4: symexTarget("tc_branch")
  if t["a"].len == 2 and x > 0: symexTarget("tc_branch_dead")

proc tcIncl(t: Table[string, HashSet[int]]) =
  var u = t
  if "a" in u and u["a"].len == 0:
    u["a"].incl 4
    if 4 notin u["a"] or u["a"].len != 1: symexTarget("tc_incl_dead")
    if 4 in u["a"]: symexTarget("tc_incl")

proc tkKeyErr(t: Table[string, int]) =
  # An absent key's `[]` raises `KeyError`; it was a narrowed path only, so
  # the handler was dead (a false sxUnsat at base).
  try:
    let v = t["z"]
    if v == 3: symexTarget("tk_hit")
  except KeyError:
    symexTarget("tk_keyerr")

proc tkKeyErrDead(t: Table[string, int]) =
  if "z" in t:
    try:
      discard t["z"]
    except KeyError:
      symexTarget("tk_keyerr_dead")

suite "S8at (7): Table float keys and container values":
  test "a set value is included into in place":
    let r = symexFind(tcIncl, tLabel("tc_incl"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcIncl(r.witness[0]), "tc_incl")
    let d = symexFind(tcIncl, tLabel("tc_incl_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an absent key raises KeyError":
    let r = symexFind(tkKeyErr, tLabel("tk_keyerr"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tkKeyErr(r.witness[0]), "tk_keyerr")
    let d = symexFind(tkKeyErrDead, tLabel("tk_keyerr_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a container value merges across a branch":
    let r = symexFind(tcBranch, tLabel("tc_branch"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tcBranch, tLabel("tc_branch_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

# ---- (8) uint8 vs char top-level containers ---------------------------------

proc u8Tab(t: Table[uint8, int]) =
  if t.len == 1 and 200'u8 in t: symexTarget("u8_tab")

proc chTab(t: Table[char, int]) =
  if t.len == 1 and 'z' in t: symexTarget("ch_tab")

proc u8Seq(s: seq[uint8]) =
  if s.len == 1 and s[0] == 250: symexTarget("u8_seq")

proc chSet(s: HashSet[char]) =
  if s.len == 1 and 'q' in s: symexTarget("ch_set")

proc u32Set(s: HashSet[uint32]) =
  # A 2^32-cell domain: `mkInt` (a `cint`) faulted on its size at base.
  if s.len == 1 and 4_000_000_000'u32 in s: symexTarget("u32_set")

proc u32Tab(t: Table[uint32, int]) =
  if t.len == 1 and 3_000_000_000'u32 in t: symexTarget("u32_tab")

suite "S8at (8): uint8 and char containers are told apart":
  test "Table[uint8, int]":
    let r = symexFind(u8Tab, tLabel("u8_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(u8Tab(r.witness[0]), "u8_tab")

  test "Table[char, int]":
    let r = symexFind(chTab, tLabel("ch_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(chTab(r.witness[0]), "ch_tab")

  test "seq[uint8]":
    let r = symexFind(u8Seq, tLabel("u8_seq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(u8Seq(r.witness[0]), "u8_seq")

  test "HashSet[char]":
    let r = symexFind(chSet, tLabel("ch_set"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(chSet(r.witness[0]), "ch_set")

  test "HashSet[uint32] (a 2^32-cell domain)":
    let r = symexFind(u32Set, tLabel("u32_set"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(u32Set(r.witness[0]), "u32_set")

  test "Table[uint32, int] (a 2^32-cell domain)":
    let r = symexFind(u32Tab, tLabel("u32_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(u32Tab(r.witness[0]), "u32_tab")

suite "S8at: walker version floor":
  test "walker version floor >= 193":
    check parseInt(symexWalkerVersion) >= 193

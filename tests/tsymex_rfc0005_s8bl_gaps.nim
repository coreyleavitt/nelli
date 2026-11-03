## RFC-0005 (soundness channels) slice S8bl, items 3 and 4 -- S8bc's smaller
## remainders: `add` to a local seq of an unbacked element, a plain type
## alias, `for x in [a, b]`, `mpairs` / `mvalues`, a Table length change
## while iterating, a witness seq element with a ref part, and an element's
## nested seq longer than 1024.
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with `tsymex_rfc0005_s8bl_gaps_b`,
## `tsymex_rfc0005_s8bl_gaps_c`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 71 s).

import std/[unittest, strutils, tables, hashes]
import nelli
import nelli/symex
import nelli/smt/types

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

# ---- (3) add to a local seq of an unbacked element --------------------------

proc addUnbacked(x: int) =
  var p: seq[seq[int]] = @[]
  p.add(@[x])
  if x == 4: symexTarget("add_unbacked")

# ---- (4) a plain alias ------------------------------------------------------

type Meters = int

proc aliasHash(s: string) =
  var hc: Hash
  hc = hash(s)
  if (hc and 7) == 3 and s.len == 1: symexTarget("alias_hash")

proc aliasParam(m: Meters) =
  if m < -100 or m > 100: return
  if m * 2 == 14: symexTarget("alias_param")
  if m * 2 == 15: symexTarget("alias_param_dead")

# ---- (4) for over an array literal ------------------------------------------

proc forLit(a, b: int) =
  if a < -100 or a > 100 or b < -100 or b > 100: return
  var s = 0
  for x in [a, b]: s += x
  if s == 9 and a == 4: symexTarget("for_lit")
  if s != a + b: symexTarget("for_lit_dead")

# ---- (4) witnesses ----------------------------------------------------------

type RW = object
  id: int
  p: ref int

suite "S8bl (3): add to a seq of an unbacked element":
  test "a placeholder decline, not a walker fault":
    let r = symexFind(addUnbacked, tLabel("add_unbacked"))
    checkpoint $r.status & " " & show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)
    check r.status in {sxSat, sxUnknown}

suite "S8bl (4): plain alias, array literal loop":
  test "`Hash = int` is an int (was a scoped decline)":
    let r = symexFind(aliasHash, tLabel("alias_hash"))
    checkpoint $r.status & " " & show(r.errors)
    check not r.errors.hasKind(feUnsupportedParamType)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "a user alias param":
    let r = symexFind(aliasParam, tLabel("alias_param"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(aliasParam(r.witness[0]), "alias_param")
    let d = symexFind(aliasParam, tLabel("alias_param_dead"))
    check d.status == sxUnsat

  test "for x in [a, b] (was a walker fault)":
    let r = symexFind(forLit, tLabel("for_lit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(forLit(r.witness[0], r.witness[1]), "for_lit")
    let d = symexFind(forLit, tLabel("for_lit_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

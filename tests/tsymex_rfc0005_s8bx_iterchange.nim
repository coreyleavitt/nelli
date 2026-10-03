## RFC-0005 (soundness channels) slice S8bx, item 4 -- a key removed from a
## Table while iterating over it, with its length kept.
##
## Nim's `pairs` / `keys` / `values` / `mpairs` / `mvalues` walk the hash
## slots: `for h in 0 .. high(t.data): if isFilled(...): yield ...`, with
## `assert(len(t) == L)` after each yield. A key removed and another (or the
## same one) inserted in one iteration keeps the length, so no assertion
## fires, and what the rest of the loop visits depends on the slots: the new
## key's slot against the current one, and `del`'s backshift, which moves a
## later entry back into the hole. The native runs below show it: from
## `{"a"}`, deleting `a` and inserting `c` visits `c`; from `{"f"}` it does
## not; from `{"k308", "k321"}`, deleting and re-inserting `k308` at its
## own visit visits it twice and skips `k321`. The slots are a function of
## the keys' hashes and the table's capacity, which the walker does not
## model (a key is a symbolic string), so the slot walk is not decided: a
## path that removed a key and kept the length declines (`feUnsupportedOp`,
## ⊤). It followed the enumeration taken when the loop began, untainted for
## a table of one entry: a false `sxUnsat` for a label only the new key's
## visit reaches, and a false `sxSat` for one only the initial enumeration
## reaches.
import std/[unittest, strutils, tables]
import nelli
import nelli/symex

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  ## A reached decline (an unreached one is a `sevHint`, RFC-0005 S9).
  for e in errs:
    if e.kind == k and e.severity == sevError: return true
  false

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

# One entry; its key is replaced by "c" at the first visit.
proc replaceKey(t0: Table[string, int]) =
  if t0.len != 1: return
  var t = t0
  var n = 0
  for k, v in t.pairs:
    inc n
    if n == 1:
      t.del(k)
      t["c"] = 9
  if n == 2: symexTarget("new_key_visited")
  if n == 1: symexTarget("new_key_skipped")

# Two entries; the first visited key is removed and re-inserted.
proc reinsert(t0: Table[string, int]) =
  if t0.len != 2: return
  var t = t0
  var first = ""
  var n = 0
  var again = false
  for k, v in t.pairs:
    inc n
    if n == 1:
      first = k
      t.del(k)
      t[k] = 2
    elif k == first:
      again = true
  if again: symexTarget("visited_twice")

# No removal: a value write keeps every slot, and the enumeration is exact.
proc valueWrite(t0: Table[string, int]) =
  if t0.len != 1: return
  var t = t0
  var n = 0
  for k, v in t.pairs:
    inc n
    if v < 1000: t[k] = v + 1
  if n == 1 and t0.len == 1: symexTarget("value_live")
  if n == 2: symexTarget("value_dead")

proc mkTab(keys: varargs[string]): Table[string, int] =
  ## Built as a witness is (`readTableAs`: `initTable`, then `[]=`); the
  ## slots depend on the capacity too (`toTable` sizes it for its pairs).
  result = initTable[string, int]()
  for k in keys: result[k] = 1

proc nativeReplace(key: string): (bool, bool) =
  symexCaptureBegin()
  replaceKey(mkTab(key))
  let hits = symexCaptureEnd()
  ("new_key_visited" in hits, "new_key_skipped" in hits)

suite "S8bx (4): the slot walk depends on the hashes (native runs)":

  test "replacing the key: visited from {a}, not from {f}":
    check nativeReplace("a") == (true, false)
    check nativeReplace("f") == (false, true)

  test "re-inserting the visited key visits it twice from {k308, k321}":
    check reproduces(reinsert(mkTab("k308", "k321")), "visited_twice")
    check not reproduces(reinsert(mkTab("a", "b")), "visited_twice")

suite "S8bx (4): a key removed while iterating, the length kept":

  test "a label only the new key's visit reaches is not sxUnsat":
    let r = symexFind(replaceKey, tLabel("new_key_visited"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    check hasKind(r.errors, feUnsupportedOp)
    if r.status == sxSat:
      check reproduces(replaceKey(r.witness[0]), "new_key_visited")

  test "the label the initial enumeration reaches is replay-gated":
    let r = symexFind(replaceKey, tLabel("new_key_skipped"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    if r.status == sxSat:
      check reproduces(replaceKey(r.witness[0]), "new_key_skipped")

  test "a re-inserted key visited twice is not sxUnsat":
    let r = symexFind(reinsert, tLabel("visited_twice"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    check hasKind(r.errors, feUnsupportedOp)

  test "a value write keeps the enumeration exact":
    let r = symexFind(valueWrite, tLabel("value_live"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(valueWrite(r.witness[0]), "value_live")
    let d = symexFind(valueWrite, tLabel("value_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    check not hasKind(d.errors, feUnsupportedOp)

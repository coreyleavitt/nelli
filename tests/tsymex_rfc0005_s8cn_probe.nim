## RFC-0005 slice S8cn, item 2 -- step 1e, the bounded concrete search behind
## `bt_limit_replace` on Z3 4.13.4.
##
## In its own context (S8bp), 4.13.4 spends both of a query's searches on one
## free byte over a regex's recursive step function, while the query with that
## byte pinned is evaluation. Step 1e tries a bounded set of strings, each by
## the WHOLE query, so a wrong candidate is only a miss. A/B on the original
## query, in the RFC's "As landed (S8cn)": with S8bp's isolation off step 1 is
## SAT in 3.8M units; on 5.1 in 2.4M with it on; on 4.13.4 with it on, past 10M
## with the domain or without it. These shapes are other subjects, so the step
## is not a case of the one pin.
import std/[unittest, re, strutils]
import nelli/symex

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    call
    symexCaptureEnd()

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs: result.add $e.severity & ": " & e.msg & "\n"


proc twoBytes(s: string) =
  # A limit of 6 stops "ac" (S8bt's `bt_limit_replace_err`); 20 does not.
  if s.len == 2 and s.replace(re"(*LIMIT_MATCH=20)(?:a|b)*c", "-") == "-":
    symexTarget("two_bytes")

proc outsideAlphabet(s: string) =
  # A subject with no match: its output is itself, a byte the regex never names.
  if s.len == 1 and s.replace(re"(*LIMIT_MATCH=6)(?:a|b)*c", "-") == s and s != "a" and s != "b":
    symexTarget("outside_alphabet")

proc noLength(s: string) =
  # No length in the query: the theory-free model gives one, or 0..3 do.
  if s.len <= 3 and s.replace(re"(*LIMIT_MATCH=6)(?:a|b)*c", "-") == "-a":
    symexTarget("no_length")

proc twoLeaves(s, t: string) =
  if s.len == 1 and t.len == 1 and s.replace(re"(*LIMIT_MATCH=6)(?:a|b)*c", t) == "z":
    symexTarget("two_leaves")

proc noModel(s: string) =
  if s.len == 1 and s.replace(re"(*LIMIT_MATCH=6)(?:a|b)*c", "-") == "--":
    symexTarget("no_model")

suite "S8cn (2): step 1e, other subjects":

  test "a two-byte subject":
    check "two_bytes" in hits(twoBytes("ac"))
    let r = symexFind(twoBytes, tLabel("two_bytes"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check "two_bytes" in hits(twoBytes(r.witness[0]))

  test "a byte outside the regex's alphabet":
    let r = symexFind(outsideAlphabet, tLabel("outside_alphabet"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check "outside_alphabet" in hits(outsideAlphabet(r.witness[0]))

  test "a subject with no length of its own":
    let r = symexFind(noLength, tLabel("no_length"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check "no_length" in hits(noLength(r.witness[0]))

  test "two free strings":
    let r = symexFind(twoLeaves, tLabel("two_leaves"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check "two_leaves" in hits(twoLeaves(r.witness[0], r.witness[1]))

  test "no model: every byte natively, and the step answers nothing":
    symexCaptureBegin()
    for b in 0 .. 255: noModel($chr(b))
    check "no_model" notin symexCaptureEnd()
    let r = symexFind(noModel, tLabel("no_model"))
    checkpoint show(r.errors)
    check r.status != sxSat

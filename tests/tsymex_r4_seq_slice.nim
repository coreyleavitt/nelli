## Round-4 dev item 1 (walker v67) — seq-slice VALUES model as
## ARRAY-LAMBDA VIEWS (`iekSeqSlice`).
##
## Pre-v67 truth (established empirically, correcting an earlier vacuous
## probe): a slice VALUE (`let payload = data[4 .. ^1]`) was a MACRO-TIME
## COMPILE ABORT (`getImpl`-inlining system's `[]` died on `len`), and a
## DISCARDED slice was silently dropped by the discard arm — so "slices
## prove" observations were artifacts of nothing being modeled at all.
## v67: `len = hi - lo + 1`, `data = (lambda (i) (select base (+ i lo)))`,
## OOB deposits a real IndexDefect fork (SND-4 sink), ADR-0027 bound
## discipline. The UNSAT pins are load-bearing: an unconstrained-fresh-seq
## stub would satisfy their negations instantly.
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

proc sliceLenOk(data: seq[int]) =
  ## chapulin decode DATA-arm shape: payload = data[4 .. ^1]; its length
  ## is ALWAYS data.len - 4 under the guard.
  if data.len > 4:
    let payload = data[4 .. ^1]
    if payload.len == data.len - 4:
      symexTarget("len-ok")

proc sliceLenImpossible(data: seq[int]) =
  if data.len > 4:
    let payload = data[4 .. ^1]
    if payload.len == data.len - 3:
      symexTarget("len-impossible")

proc sliceElemImpossible(data: seq[int]) =
  ## View correctness: payload[0] IS data[4] — inequality is unreachable.
  if data.len > 5:
    let payload = data[4 .. ^1]
    if payload[0] != data[4]:
      symexTarget("elem-impossible")

proc sliceElemOk(data: seq[int]) =
  if data.len > 5:
    let payload = data[4 .. ^1]
    if payload[0] == 7:
      symexTarget("elem-seven")

proc sliceTwoEndpointLenOk(data: seq[int]) =
  ## Chapulin P3: the EXPLICIT two-endpoint form `data[a .. data.len-1]`
  ## (not the `^k` backward form) — same lambda view, spelled directly.
  if data.len > 4:
    let payload = data[4 .. data.len - 1]
    if payload.len == data.len - 4:
      symexTarget("p3-len-ok")

proc sliceTwoEndpointImpossible(data: seq[int]) =
  if data.len > 4:
    let payload = data[4 .. data.len - 1]
    if payload.len == data.len - 3:
      symexTarget("p3-len-impossible")

proc sliceHalfOpenElemImpossible(data: seq[int]) =
  ## `..<` half-open spelling: payload = data[4 ..< data.len] has
  ## payload[0] IS data[4].
  if data.len > 5:
    let payload = data[4 ..< data.len]
    if payload[0] != data[4]:
      symexTarget("halfopen-elem-impossible")

proc sliceOobUnguarded(data: seq[int]) =
  ## No length guard: data.len < 4 makes `4 .. data.len-1` a REAL
  ## IndexDefect (lo > hi + 1) — the defect search must find it.
  let payload = data[4 .. ^1]
  discard payload.len

proc sliceOobGuarded(data: seq[int]) =
  if data.len > 4:
    let payload = data[4 .. ^1]
    discard payload.len

suite "symex round-4 — seq-slice values as array-lambda views":

  test "payload.len == data.len - 4 is SAT with a consistent witness (was a compile abort)":
    let r = symexFind(sliceLenOk, tLabel("len-ok"))
    check r.status == sxSat
    let w = r.witness[0]
    check w.len > 4 and w[4 .. ^1].len == w.len - 4

  test "payload.len == data.len - 3 is UNSAT (view-length soundness)":
    let r = symexFind(sliceLenImpossible, tLabel("len-impossible"))
    check r.status == sxUnsat

  test "payload[0] != data[4] is UNSAT (view-element soundness)":
    let r = symexFind(sliceElemImpossible, tLabel("elem-impossible"))
    check r.status == sxUnsat

  test "payload[0] == 7 is SAT with a consistent witness":
    let r = symexFind(sliceElemOk, tLabel("elem-seven"))
    check r.status == sxSat
    let w = r.witness[0]
    check w.len > 5 and w[4] == 7

  test "two-endpoint form: payload.len == data.len - 4 is SAT (chapulin P3)":
    let r = symexFind(sliceTwoEndpointLenOk, tLabel("p3-len-ok"))
    check r.status == sxSat
    let w = r.witness[0]
    check w.len > 4 and w[4 .. w.len - 1].len == w.len - 4

  test "two-endpoint form: payload.len == data.len - 3 is UNSAT":
    let r = symexFind(sliceTwoEndpointImpossible, tLabel("p3-len-impossible"))
    check r.status == sxUnsat

  test "half-open `..<` form: payload[0] != data[4] is UNSAT":
    let r = symexFind(sliceHalfOpenElemImpossible,
                      tLabel("halfopen-elem-impossible"))
    check r.status == sxUnsat

  test "unguarded slice: the IndexDefect is FOUND (defect-fork honesty)":
    let r = symexFind(sliceOobUnguarded, tIndexError())
    check r.status == sxRaised

  test "guarded slice: no IndexError path (sxUnsat)":
    let r = symexFind(sliceOobGuarded, tIndexError())
    check r.status == sxUnsat

suite "symex round-4 seq-slice — walker version pin":

  test "walker version floor >= 67 (iekSeqSlice lambda view + getImpl degrade)":
    check parseInt(symexWalkerVersion) >= 67

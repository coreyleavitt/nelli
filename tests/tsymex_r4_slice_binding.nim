## Round-4 Slice A (walker v66) — bound string slices are REAL substrings.
##
## `let t = s[0 ..< i]` reached the string `[]`-call route wrapped in
## `nnkStmtListExpr`/`nnkHiddenStdConv`; the shape-only `nnkInfix` test fell
## through to the single-CHAR path and the binding mis-lowered as an svBV8
## char (field-observed on chapulin's real `parseTftpUri`: `hostPort` — a
## `rest[0 ..< slashPos]` binding — degraded every downstream string op,
## and TWO such mis-lowered slices would have compared as first-char
## equality: a wrong-verdict hazard). v66 unwraps the wrappers and
## dispatches on the index's TYPE.
##
## Bounds here are FIND-DERIVED (Int-sorted) — the field-realistic class
## (chapulin's `slashPos`/`closeBracket` are find results). A free-int-PARAM
## bound is BV-represented and its bv2int bridge into Sequence theory is an
## empirical Z3 NON-TERMINATOR (bisected: the UNSAT side hung > 3 h) — that
## shape now DECLINES CLASSIFIED (CR-17 class; pinned below); the
## Int-representation pre-pass lifting it is the recorded round-5 slice.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

proc sliceLenOk(s: string) =
  ## p = find-derived bound; len(s[0 ..< p]) == p always holds when p > 0.
  let p = s.find(':')
  if p > 0 and p < s.len:
    let t = s[0 ..< p]
    if t.len == p:
      symexTarget("len-ok")

proc sliceLenImpossible(s: string) =
  let p = s.find(':')
  if p > 0 and p < s.len:
    let t = s[0 ..< p]
    if t.len == p + 1:
      symexTarget("len-impossible")

proc slicePrefixNeq(s: string) =
  ## t = strict prefix of u (one char shorter) — never equal. Pre-v66 both
  ## bindings mis-lowered to chars: a false-SAT hazard.
  let p = s.find(':')
  if p > 1 and p < s.len:
    let t = s[0 ..< p - 1]
    let u = s[0 ..< p]
    if t == u:
      symexTarget("impossible-eq")

proc sliceEndsWith(s: string) =
  ## A bound slice flows into a later string op across statements — the
  ## chapulin parseTftpUri host-extraction shape.
  let p = s.find(':')
  if p >= 4 and p < s.len:
    let t = s[0 ..< p]
    if t.endsWith(".md5"):
      symexTarget("ends-md5")

proc bvBoundDeclined(s: string, i: int) =
  ## A FREE int param as the bound — BV-represented; must degrade
  ## CLASSIFIED (never hang, never a char mis-read).
  if i > 0 and i < s.len:
    let t = s[0 ..< i]
    if t.len == i:
      symexTarget("bv-bound")

suite "symex round-4 Slice A — bound string slices lower as substrings":

  test "find-bounded slice: len(s[0 ..< p]) == p is SAT with a consistent witness":
    let r = symexFind(sliceLenOk, tLabel("len-ok"))
    check r.status == sxSat
    let ws = r.witness[0]
    let p = ws.find(':')
    check p > 0 and ws[0 ..< p].len == p

  test "find-bounded slice: len == p + 1 is UNSAT (soundness)":
    let r = symexFind(sliceLenImpossible, tLabel("len-impossible"))
    check r.status == sxUnsat

  test "strict prefix never equals its extension (the pre-v66 false-SAT hazard)":
    let r = symexFind(slicePrefixNeq, tLabel("impossible-eq"))
    check r.status == sxUnsat

  test "bound slice flows into a later endsWith: SAT with a consistent witness":
    let r = symexFind(sliceEndsWith, tLabel("ends-md5"))
    check r.status == sxSat
    let ws = r.witness[0]
    let p = ws.find(':')
    check p >= 4 and ws[0 ..< p].endsWith(".md5")

  test "free-int-param bound declines classified (the bv2int non-termination shape)":
    let r = symexFind(bvBoundDeclined, tLabel("bv-bound"))
    check r.status == sxUnknown
    check r.errors.len > 0

suite "symex round-4 Slice A — walker version pin":

  test "walker version floor >= 66 (typed slice-index dispatch + CR-17 bound guard)":
    check parseInt(symexWalkerVersion) >= 66

## RFC-0005 (soundness channels) slice S8s -- S8p's precision remainder.
##
## Four places the walker gave up on (or faulted over) code whose behaviour
## is fully determined, and one cpp compile failure. S8p reported them.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## debug build) by the oracle test of each suite, which runs the SUT itself.
##   (1) a `seq[uint8]` element compared against a literal
##       (was `weInternalWalkerFault`, "field 'bv8' ... kind = svBV64");
##   (2) the zero value of a multi-variant whose ordinal 0 falls in an
##       `else` arm (was `feUnsupportedOpHavoc`);
##   (3) a callee returning an `array` (was `feUnsupportedOpHavoc`);
##   (4) a write to a variant arm field and a positional tuple-element
##       write (was `feUnsupportedStmtKind`);
##   (5) the walker version floor.
## The cpp compile failure of `tsymex_r6_n43_parity` (a deleted
## `std::atomic::operator=`) is pinned by that suite compiling on cpp.
##
## RFC-0005 S8cm: part 3 of 8 of this suite, with
## `tsymex_rfc0005_s8s_precision`, `tsymex_rfc0005_s8s_precision_b`,
## `tsymex_rfc0005_s8s_precision_c`, `tsymex_rfc0005_s8s_precision_d`,
## `tsymex_rfc0005_s8s_precision_e`, `tsymex_rfc0005_s8s_precision_f`,
## `tsymex_rfc0005_s8s_precision_g`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 134 s).
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

# ---- (2) a multi-variant whose ordinal 0 is in an else arm ------------------------
#
# Real Nim zero-initialises `result`: both discriminators s3A (ordinal 0, which
# each axis's `else` arm covers) and every field 0, the else arms' too. Before
# S8s the untouched result was `feUnsupportedOpHavoc`.

type
  S8sK = enum s3A, s3B, s3C
  S8sMVE = object
    case k: S8sK
    of s3B: b: int
    else: e: int
    case j: S8sK
    of s3C: c: int
    else: f: int
  S8sVE = object
    ## A single `case` whose ordinal 0 is in its `else` arm.
    case vk: S8sK
    of s3C: vc: int
    else: ve: int

proc mveParam(m: S8sMVE) =
  ## An input multi-variant: every ordinal an `else` arm covers is a legal
  ## discriminator value (s3A and s3C on `k`, s3A and s3B on `j`).
  if m.k == s3A and m.e == 4: symexTarget("s8s_mvpe")
  if m.j == s3B and m.f == 2 and m.k == s3C: symexTarget("s8s_mvpf")

type
  S8sR = range[0..5]
  S8sK2 = enum s2A, s2B
  S8sMVR = object
    ## A multi-variant with a `range` discriminator and an `else` arm: no
    ## enum tags, so the else arm covers 1..5 of `r`'s declared range.
    case r: S8sR
    of 0: z: int
    else: w: int
    case q: S8sK2
    of s2A: nf: int
    of s2B: nt: int

proc mvrParam(m: S8sMVR) =
  if m.r == 3 and m.w == 7 and m.q == s2B: symexTarget("s8s_mvr")

suite "S8s (2) a multi-variant whose ordinal 0 is in an else arm":
  test "an input's discriminator ranges over its else arms (was a false sxUnsat)":
    ## `allocateSym` constrained each axis's discriminator to its explicit
    ## tags plus the else arm's sentinel ordinal (-1), never to an ordinal
    ## the `else` arm covers: both labels were `sxUnsat`.
    let r = symexFind(mveParam, tLabel("s8s_mvpe"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].k == s3A
      check reproduces(mveParam(r.witness[0]), "s8s_mvpe")
    let f = symexFind(mveParam, tLabel("s8s_mvpf"))
    checkpoint($f.status & " " & show(f.errors))
    check f.status == sxSat
    if f.status == sxSat:
      check reproduces(mveParam(f.witness[0]), "s8s_mvpf")

  test "a range discriminator's else values render in the witness":
    ## The else arm's values (1..5) became reachable with the domain fix;
    ## the multi-variant witness emitter rendered no branch for them (the
    ## `default` fallback: `r: 0`), so the witness would not reach the label.
    let r = symexFind(mvrParam, tLabel("s8s_mvr"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].r == 3
      check r.witness[0].w == 7
      check reproduces(mvrParam(r.witness[0]), "s8s_mvr")

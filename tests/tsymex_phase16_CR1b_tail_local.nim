## Phase 16 — CR-1b (RFC-chapulin-hardening, Cluster 2 — Crash-totality):
## tail-return-of-local fixed at lowering.
##
## Before this slice, a value-returning callee whose body binds a local `let`
## and then implicitly returns an expression over it —
##
##   proc tailLocal(data: seq[int], o: int): int =
##     let hi = data[o] mod 256
##     hi + 1
##
## — native-crashed the walker with an uncaught `KeyError: key not found: hi`
## the moment the caller reached the call site. `hi` is an ordinary bound
## local; the walker fully supports reading one elsewhere. The gap was NOT at
## the raw `env[e.vname]` index in `runtime.nim`'s `iekVar` lowering arm (the
## RFC's cited crash site) — that index is a faithful symptom, not the fault.
## The real defect was one layer up, in `dsl_parser.nim`'s `parseExpr` arm for
## `nnkStmtListExpr`/`nnkPar`: Nim's semchecker presents a multi-statement
## implicit-tail-return body as a single `result = (let hi = ...; hi + 1)`
## assignment, whose RHS is a `StmtListExpr` holding the `LetSection` followed
## by the tail expression. The old arm took ONLY the last child
## (`parseExpr(n[n.len - 1], ...)`), silently discarding every leading
## statement — including the `let` the tail expression depends on — so `hi`
## never made it into the callee's parsed IR, let alone `env`.
##
## The fix parses each leading child as an ordinary statement into the
## existing `preamble` A-normalisation channel (mirroring the `nnkLetSection`
## handling in `parseStmtInner`, and consistent with how every other
## expression-position side-effect in this file already flows into
## `preamble`), so the binding reaches the tail expression's environment at
## walk time. This is a pure parser fix — `runtime.nim`'s `iekVar` arm is
## unchanged, and the local resolves via the normal, already-sound `env`
## lookup (no soft-fail / no `.hasKey` degrade was introduced there).
##
## No new ADR: this is a bug fix at an existing lowering locus (the
## `nnkStmtListExpr` arm of `parseExpr`), not a new capability axis.
import std/unittest
import std/strutils
import proptest/symex
import proptest/smt/canonicalize

proc tailLocal(data: seq[int], o: int): int =
  let hi = data[o] mod 256
  hi + 1

proc gateSat(data: seq[int], o: int) =
  ## `data[o] >= 0` keeps `mod` unambiguous (Nim's truncated `mod` and Z3's
  ## Int `mod` agree on non-negative operands) — this test is about the
  ## tail-return-of-local lowering, not int-mod sign semantics.
  if o >= 0 and o < data.len and data[o] >= 0:
    if tailLocal(data, o) == 5:
      symexTarget("hit")

proc gateUnsat(data: seq[int], o: int) =
  ## `hi = data[o] mod 256` with `data[o] >= 0` always satisfies
  ## `0 <= hi < 256`, so `hi + 1` can never reach 300. A stub that resolves
  ## the dropped local to a fresh, unconstrained symbol (rather than
  ## genuinely binding it) would NOT be pinned down by this range and could
  ## incorrectly report `sxSat` here — this regression is load-bearing
  ## against exactly that failure mode, not just the crash.
  if o >= 0 and o < data.len and data[o] >= 0:
    if tailLocal(data, o) == 300:
      symexTarget("impossible")

suite "symex Phase 16 CR-1b — tail-return-of-local fixed at lowering":

  test "let hi = data[o] mod 256; hi + 1 — implicit tail return no longer KeyErrors":
    let r = symexFind(gateSat, tLabel("hit"))
    check r.status == sxSat
    # Load-bearing: the witness must actually satisfy the tail-expression
    # relation through the callee's local `hi`, not just reach the call site.
    let (data, o) = r.witness
    check o >= 0 and o < data.len
    check data[o] mod 256 == 4          ## hi == 4  =>  hi + 1 == 5
    check tailLocal(data, o) == 5

  test "hi + 1 == 300 is UNSAT — the mod-256 local is genuinely bound, not a free stub":
    let r = symexFind(gateUnsat, tLabel("impossible"))
    check r.status == sxUnsat

suite "symex Phase 16 CR-1b — walker version pin":

  test "walker version floor >= 42 (CR-1b: tail-return-of-local fixed at 42)":
    ## SW pin idiom (RFC §Version-pin discipline): this incidental
    ## feature-test pin uses the tolerant `>=` floor (only the canonical
    ## tsymex_phase15_CR2_cachekey.nim keeps the brittle `==`).
    check parseInt(symexWalkerVersion) >= 42

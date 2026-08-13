## Phase 16 — CR-1c (RFC-chapulin-hardening, Cluster 2 — Crash-totality,
## ADR-0020): narrow last-resort walker catch -> distinct internal-fault
## `sxUnknown`.
##
## The genuine safety net for the §0 "walker never crashes" invariant: a
## final `except CatchableError` catch-all on the existing `runSymex` try
## (`runtime.nim`) now converts a genuinely UNANTICIPATED native exception —
## one that escapes the walker from any dispatch depth and matches NONE of the
## specific `Symex*Error`/`SymexClassifiedDegradeError`/`Z3Error` arms — into a
## classified degrade tagged with the DISTINCT `weInternalWalkerFault` kind,
## which is NEVER conflated with an ordinary construct-gap `se*`/`fe*` kind.
## (An earlier per-`walk`-frame `try/except` was reverted: catching and
## re-raising the anticipated carriers at every recursion frame crashed the C
## backend — an ORC-destructor/goto-exception interaction on `walkBlock`'s live
## `seq[Path]` result, the b7258f7 divergence class; see ADR-0020.)
##
## CR-1a/CR-1b already fixed the two known native-crash constructs this RFC
## found, so there is no naturally-occurring repro left to exercise the
## safety net. This test uses SYNTHETIC fault injection instead: a
## `when defined(symexTestInjectWalkerFault):` hook (compiled out of every
## normal build) raises a plain `ValueError` — deliberately the SAME type as
## an ordinary internal-invariant guard, so the safety net cannot be
## distinguishing by anything other than "not one of the known carriers" —
## the moment the walker's per-statement dispatch reaches a sentinel
## `symexTarget("__inject_walker_fault__")` label. The companion
## `tsymex_phase16_CR1c_internal_fault.nim.cfg` sets
## `-d:symexTestInjectWalkerFault` for THIS file only (Nim auto-reads
## `<testfile>.nim.cfg`), so the injection fires under the unmodified
## `scripts/dt-bounded.sh <c|cpp> ...` harness on both backends, with zero
## overhead anywhere else.
##
## Cross-backend divergence this guards against (b7258f7, hard precedent): a
## bare `try/finally` (no `except`) around walk dispatch previously hit Nim's
## C-backend goto-based exception model and SILENTLY SWALLOWED a re-raise,
## producing a wrong `sxUnsat` instead of `sxUnknown` — a failure mode that
## was C-BACKEND-ONLY and completely invisible on C++. The assertions below
## are deliberately backend-agnostic-strong (exact `== sxUnknown`, the
## `weInternalWalkerFault` kind present, AND explicit `!= sxUnsat`/
## `!= sxSat` checks) so that if a future regression reintroduces a
## swallow-shaped bug on either backend, the `c` or `cpp` sweep entry for
## this file fails loudly rather than merely "not being sxUnknown" by
## omission.
import std/unittest
import std/strutils
import nelli/symex
import nelli/smt/canonicalize

proc faultInjector() =
  ## The sentinel label name is matched verbatim by the injection hook in
  ## `runtime.nim`'s `walk(isTargetLabel)` arm, independent of whether it is
  ## the run's actual solve target — the injected raise happens the instant
  ## per-statement DISPATCH reaches this statement.
  symexTarget("__inject_walker_fault__")

suite "symex Phase 16 CR-1c — narrow last-resort walker catch":

  test "injected unanticipated native fault -> sxUnknown + weInternalWalkerFault, " &
       "never sxUnsat, never sxSat":
    let r = symexFind(faultInjector, tLabel("__inject_walker_fault__"))
    # The RED failure mode (no catch at all) is a native crash: the
    # `ValueError` raised by the injection hook propagates uncaught out of
    # `runSymex` and kills the whole test process (or, under the b7258f7
    # try/finally-shaped bug, silently degrades to a WRONG `sxUnsat` on the C
    # backend only). Both are unacceptable; the assertions below pin the
    # GREEN behavior precisely enough that either RED shape fails loudly.
    check r.status == sxUnknown
    check r.status != sxUnsat
    check r.status != sxSat
    check r.errors.len >= 1
    check r.errors[0].kind == weInternalWalkerFault
    check r.errors[0].severity == sevError
    # The distinct kind must never be conflated with an ordinary
    # construct-gap `se*`/`fe*` kind — spot-check it is not any of a
    # representative sample of those.
    check r.errors[0].kind != feUnsupportedOp
    check r.errors[0].kind != seUnsupportedStringOp
    check r.errors[0].kind != heUnresolvedRef
    # The injected message rides through (via `SymexClassifiedDegradeError.msg`
    # -> `SymexErrorInfo.msg`), confirming the ONE new `runSymex` except arm
    # (for `SymexClassifiedDegradeError`) — not some pre-existing arm — is
    # what actually produced this result.
    check "CR-1c synthetic fault" in r.errors[0].msg

suite "symex Phase 16 CR-1c — walker version pin":

  test "walker version floor >= 43 (CR-1c: narrow last-resort catch landed at 43)":
    ## SW pin idiom (RFC §Version-pin discipline): this incidental
    ## feature-test pin uses the tolerant `>=` floor (only the canonical
    ## tsymex_phase15_CR2_cachekey.nim keeps the brittle `==`).
    check parseInt(symexWalkerVersion) >= 43

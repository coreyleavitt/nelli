## RFC-chapulin-hardening CR-2b — parameter-type `error()` → whole-run
## forced-`sxUnknown` (Cluster 2 — Crash-totality).
##
## `classifyType`'s resolved-type-name text-match catch-all
## (`dsl_typebridge.nim`, the final `else:` arm of its `case s`) used to
## `error()` at MACRO-EXPANSION time whenever a SUT parameter's resolved type
## name was not in the supported scalar set — aborting COMPILATION of the
## whole test file outright, before any proc body was even walkable. This is
## a DIFFERENT mechanism from CR-2a's expression-position catch-all:
## `classifyType*(ty: NimNode): ClassifiedType` takes no `ctx`/`preamble`
## param, so there is no statement to demote and no sound dummy value
## (downstream witness-typing needs a real `IRType`) — the CR-2a/CR-2b split
## is genuinely irreducible, not cosmetic.
##
## CR-2b (Option 2, control-loop-resolved): the unsupported parameter type
## now classifies to an `itUninterp` placeholder carrying a recognisable
## `"__unsupported:" & s` name — mirroring the existing `WeakRef`/`Atomic` →
## `__ownership:*` precedent (`dsl_typebridge.nim` ~404-410) and the
## `nnkProcTy` → `__closure` precedent (~427-428). `allocateSym`'s
## `itUninterp` arm (`runtime.nim`) special-cases the `__unsupported:` prefix
## and raises the generic `SymexClassifiedDegradeError` carrier (introduced
## by CR-1c; CR-1c's doc comment already names CR-2b as its second consumer)
## with the new `feUnsupportedParamType` kind. Because params are allocated
## BEFORE the proc body is walked, this fires immediately — giving a
## whole-run `sxUnknown`, never a walk-time crash. No new exception type.
##
## Concrete repro (RED before this slice, GREEN after): a `cstring` SUT
## parameter is not in `classifyType`'s supported scalar set ({bool, int,
## int{8,16,32,64}, uint, uint{8,16,32,64}, range[..], Natural, Positive,
## float, float{32,64}, string, char, byte}) and is not special-cased
## earlier (unlike `WeakRef`/`Atomic`/proc types/ref/ptr/seq/array/Table/
## HashSet). Before this slice: `nim c tests/tsymex_CR2b_paramtype_catchall.nim`
## FAILED to compile with `Error: symex (Phase 2): unsupported parameter
## type `cstring`; ...`. After: it compiles and the SUT resolves to a
## classified `sxUnknown` carrying `feUnsupportedParamType`, on both the `c`
## and `cpp` backends, with no native crash.
##
## Walker version: v44 -> v45 (compile-abort -> sxUnknown is a verdict change).
##
## No new ADR: CR-2b reuses CR-1c's `SymexClassifiedDegradeError` carrier and
## the existing `__ownership:`-style `itUninterp` placeholder idiom at a new
## site; it introduces no new mechanism (per RFC judgment call, round-2).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs
# ---------------------------------------------------------------------------

# SUT 1 (RED repro / strong-form): a `cstring` parameter hits classifyType's
# text-match catch-all. Params are allocated before the body is walked, so
# this degrades the WHOLE RUN to sxUnknown regardless of the body — even
# though `y == 42` is trivially reachable, it must never be reported sxSat.
proc sutCstringParam(s: cstring, y: int) =
  if y == 42:
    symexTarget("cstring_target")

# SUT 2 (genuine regression guard): ordinary supported scalar param types —
# no unsupported type anywhere — must still resolve exactly as before.
proc sutPlainSupported(x: int, y: uint8) =
  if x == 7:
    symexTarget("plain_supported")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex RFC-chapulin-hardening CR-2b — param-type catch-all degrade":

  test "CR-2b-1: cstring param compiles and degrades to whole-run sxUnknown + feUnsupportedParamType":
    ## Strong form: assert the classified KIND, not just the verdict.
    let r = symexFind(sutCstringParam, tLabel("cstring_target"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedParamType and e.severity == sevError:
        sawKind = true
    check sawKind

  test "CR-2b-2: no walk-time crash — run completes with sxUnknown, never sxSat/sxUnsat":
    ## The RFC's crash-trap (round-2) is that an unguarded itUninterp name
    ## falls through to an uncaught ValueError raise, which §0's crash-
    ## doctrine does not catch. If that trap were still open, this test
    ## would either hang (killed by the bounded runner) or the underlying
    ## `nim c`/`nim cpp` process would abort natively. Reaching this
    ## assertion at all is part of the proof; the status must never be a
    ## silently-wrong verdict.
    let r = symexFind(sutCstringParam, tLabel("cstring_target"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat

suite "symex RFC-chapulin-hardening CR-2b — regression guard":

  test "CR-2b-3: plain supported scalar param types unaffected — sxSat with exact witness":
    let r = symexFind(sutPlainSupported, tLabel("plain_supported"))
    check r.status == sxSat
    check r.witness[0] == 7

suite "symex RFC-chapulin-hardening CR-2b — walker version pin":

  test "walker version floor >= 45 (CR-2b introduced at 45)":
    ## CR-2b converts classifyType's parameter-type compile-abort catch-all
    ## to a classified whole-run sxUnknown degrade; bump 44->45 rotates any
    ## stale cache entries (there are none for the compile-abort case — a
    ## compile failure has no cache entry — but SUTs newly reachable through
    ## this path must not collide with any unrelated pre-45 cache key).
    check parseInt(symexWalkerVersion) >= 45

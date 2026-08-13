## Phase 16 INV — wire never-emitted SymexErrorKinds to structured classification.
##
## This test file covers the INV (Invariant-3 consistency cleanup) slice, which
## wires five defined-but-never-emitted SymexErrorKinds and appends geVtableDispatch
## to the enum tail. All paths remain sxUnknown (verdict-stable); the change
## improves tooling that matches errors[0].kind.
##
## == KIND DISPOSITION ==
##
## WIRED — emission site found and connected (runtime tests below):
##   seByteIterUnsupported:
##     Site: dsl_parser.nim `for c in s` over a symbolic string (mkUnsupported path).
##     Wired via ctx.parseErrors.add before returning mkUnsupported — the parse-time
##     error flows through prog.parseErrors → r.errors.
##
## WIRED IN ENGINE (defensive crash-prevention), but NOT directly testable via
## symexFind (symexFind's emitTyAndReader fires a compile-time error for these
## parameter types before the walker runs):
##   seNestedSeqUnsupported:
##     Site: runtime.nim allocateSeqDataRaw, `else` arm for elemTy.kind == itSeq.
##     Was: `raise newException(ValueError, ...)` (engine crash).
##     Now:  raises SymexNestedSeqUnsupportedError → runSymex boundary → sxUnknown.
##     Blocked by: emitTyAndReader fires `error("seq witness reader ... not yet
##     implemented")` for seq[seq[T]] SUT parameters at compile time.
##   seUnsupportedTableValType:
##     Sites: runtime.nim allocateSym(itTable) else-branch AND isIndex/svTable
##     else-branch (both were ValueError crashes).
##     Now: SymexUnsupportedTableValTypeError → sxUnknown.
##     Blocked by: emitTyAndReader fires `error("only Table[string, int] supported")`
##     for Table[K, non-int-V] SUT parameters at compile time.
##   seUnsupportedSetCharInterop:
##     Sites: runtime.nim allocateSym(itSet) else-branch (ValueError crash) AND
##     iekContains/svSet doAssert → now guarded if-raise.
##     Now: SymexUnsupportedSetCharInteropError → sxUnknown.
##     Blocked by: emitTyAndReader fires `error("only HashSet[int] supported")`
##     for HashSet[non-int64-T] SUT parameters at compile time.
##
## DOCUMENTED RESERVED/UNUSED — no distinct degrade point reachable from symexFind:
##   seByteIndexUnsupported:
##     No distinct runtime degrade site; symbolic string index `s[i]` is handled
##     by the walker via a different path. Retained for enum ordinal stability.
##     (see types.nim comment)
##   geVtableDispatch:
##     Method/vtable dispatch fires a compile-time error() in ensureProcRegistered
##     rather than yielding a runtime classified error. No emission site today.
##     Appended at enum tail for ordinal stability.
##     (see types.nim comment)
##
## == VERSION / CACHE DECISION ==
## No symexWalkerVersion bump. Evidence: symexCacheKey is built from
## canonicalize(prog) + canonicalize(target) + canonicalize(settings) + versions
## (canonicalize.nim proc symexCacheKey). The RawResult.errors field is NOT part
## of this hash — only the INPUT program is canonicalized, not the output errors.
## The DB stores only verdict + witness choices, never errors. Error kind changes
## are output-only and do not invalidate any cached entry.

import std/unittest
import nelli/symex

# --- seByteIterUnsupported: `for c in s` over a symbolic string ---
# The for-loop over a symbolic string returns mkUnsupported (parse-time),
# recording seByteIterUnsupported in ctx.parseErrors. The symexTarget after
# the loop IS in the IR (it's a separate statement in the proc body, not inside
# the for-body which is not parsed). The walker hits isUnsupported → sawUnknown,
# continues to the target label. prog.parseErrors → r.errors[0].
proc iterStr(s: string) =
  for c in s:
    discard c        ## for-body not lowered: for c in symbolic s → mkUnsupported
  symexTarget("itstr")   ## this statement IS in the IR (after the for-loop)

suite "symex Phase 16 INV — structured SymexErrorKind wiring":

  test "seByteIterUnsupported: `for c in s` yields sxUnknown + classified kind":
    ## The `for c in s` over a symbolic string cannot be soundly bounded
    ## (unbounded symbolic iteration length — ADR-0006). The walker
    ## classifies it seByteIterUnsupported (sevError) → sxUnknown
    ## (Invariant 3 — never silent UNSAT, never a crash).
    let r = symexFind(iterStr, tLabel("itstr"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seByteIterUnsupported

  test "geVtableDispatch: exists in SymexErrorKind enum (compile-time check)":
    ## geVtableDispatch was appended at the enum tail (after heUnresolvedRef)
    ## to preserve ordinal stability of all preceding members. Not emitted
    ## today (reserved for a future phase that classifies method/vtable dispatch
    ## instead of firing a compile-time error()).
    check geVtableDispatch is SymexErrorKind

## Phase 15 — Cluster C, cycle C4: DSL higher-order functions over `seq[T]`.
##
## `filter` / `map` / `fold` from `std/sequtils`, each taking a closure
## argument, are intercepted by the walker's HOF dispatch (NOT the generic
## `isCall` descent). The handler selects:
##
##   (a) INLINE path — when `inlinePolicy` permits and the seq has a CONCRETE
##       length (numeral, after `simplify`) ≤ `settings.seqInlineThreshold`
##       (default 8). The closure body is applied once per element via the C2b
##       ground closure-call machinery; the result is accumulated
##       quantifier-free (map: per-element store; filter: compacted keep-mask;
##       fold: left-fold accumulator). No path explosion (bounded by N ≤ 8).
##
##   (b) AXIOM path — when the length is SYMBOLIC. `map` → `mapArray`
##       (z3/funcdecl, `Z3_mk_map`, decidable array-map — NO universal-∀ hang);
##       `fold` → raw `Z3_mk_app` (ground, C2b discipline); `filter` → DEFERRED
##       to Phase 16 (`ceUnsupportedHof`, sevError → sxUnknown; no Z3 seqFilter).
##
## C4 is ADDITIVE under walker version "8" (no bump; Cluster C bumps at C6).
import std/[unittest, sequtils]
import proptest/symex

# --- Sub-test 1 (INLINE): filter over a CONCRETE-length seq. -----------------
#
# The seq is built by `.add` inside the SUT, so its length folds to a concrete
# numeral (`simplify(0+1+1+1) == 3`) → the bounded inline path (3 ≤ 8). The
# predicate closure `x > 0` is applied per element; the filtered RESULT is
# gated non-empty, which is satisfiable iff at least one of a,b,c is positive.
proc sutFilterInline(a: int, b: int, c: int) =
  var xs: seq[int] = @[]
  xs.add a
  xs.add b
  xs.add c
  let kept = xs.filter(proc(x: int): bool = x > 0)
  if kept.len > 0:
    symexTarget("nonempty")

# --- Sub-test 1b (INLINE): map over a concrete-length seq. -------------------
# `map (x => x+1)` then gate the first mapped element at 10 ⇒ witness a == 9.
proc sutMapInline(a: int, b: int) =
  var xs: seq[int] = @[]
  xs.add a
  xs.add b
  let ys = xs.map(proc(x: int): int = x + 1)
  if ys.len == 2 and ys[0] == 10:
    symexTarget("mapped")

# NOTE on FOLD: `std/sequtils.foldl`/`foldr` are TEMPLATES that the typed macro
# EXPANDS into a `for x in items(xs)` loop with injected `a`/`b` BEFORE the
# symex parser runs — so a fold NEVER reaches a HOF handler through
# std/sequtils. `walkHofFold` (the fold arm of the C4 HOF dispatch) exists and
# is wired (dispatched if a closure-TAKING fold proc ever surfaces), but the
# realised C4 closure-taking HOFs over seq[T] are `map`/`filter` (real procs).
# Fold is therefore NOT exercised here (the expanded loop is the existing loop
# machinery's concern, not C4's). See the C4 report / reconciliation note.

# --- Sub-test 2 (AXIOM, filter): SYMBOLIC length → ceUnsupportedHof. ---------
# `xs` is a SUT parameter with symbolic length; `filter` cannot inline and its
# axiomatize path is deferred to Phase 16 → ceUnsupportedHof (sevError),
# sxUnknown (Invariant 3 — classified, never a hang or silent verdict).
proc sutFilterSymbolic(xs: seq[int]) =
  let kept = xs.filter(proc(x: int): bool = x > 0)
  if kept.len > 0:
    symexTarget("symfilter")

# --- Sub-test 3 (AXIOM, map/fold): SYMBOLIC length must TERMINATE. -----------
# These take the axiom path (mapArray / raw Z3_mk_app). The DoD requires only
# that they TERMINATE without a Z3Error / hang; verdict may be sxUnknown.
proc sutMapSymbolic(xs: seq[int]) =
  let ys = xs.map(proc(x: int): int = x + 1)
  if ys.len > 0:
    symexTarget("symmap")

# --- Sub-test 4 (REGRESSION GUARD): user-defined `filter` is NOT hijacked. ---
# A same-named user proc whose origin is NOT std/sequtils must fall through to
# the standard isCall descent (here: ceNotImplemented for an unsupported shape),
# NOT the HOF dispatch (Des-LOW-L3).
proc filter(s: seq[int], f: proc(x: int): bool): int =
  ## user-defined homonym — returns a COUNT, different signature/owner.
  result = 0
  for x in s:
    if f(x): result += 1

proc sutUserFilter(xs: seq[int]) =
  let n = filter(xs, proc(x: int): bool = x > 0)
  if n > 0:
    symexTarget("userfilter")

suite "symex Phase 15 C4 — DSL HOFs filter/map/fold over seq[T]":

  # Sub-test 1 (inline) runs FIRST — confirm no path explosion / hang before
  # the axiom sub-tests.
  test "C4-1: filter over bounded seq with predicate closure produces sat with predicate body realized":
    let r = symexFind(sutFilterInline, tLabel("nonempty"))
    check r.status == sxSat
    # At least one of a,b,c must be positive for the filtered result to be
    # non-empty (the inline predicate `x > 0` was realized per element).
    check (r.witness[0] > 0) or (r.witness[1] > 0) or (r.witness[2] > 0)

  test "C4-1b: map over bounded seq applies mapper per element (ys[0] == a+1)":
    let r = symexFind(sutMapInline, tLabel("mapped"))
    check r.status == sxSat
    check r.witness[0] == 9    ## a+1 == 10 ⇒ a == 9

  test "C4-2: symbolic-length filter emits ceUnsupportedHof (sevError), sxUnknown":
    let r = symexFind(sutFilterSymbolic, tLabel("symfilter"))
    check r.status == sxUnknown
    var sawHof = false
    for e in r.errors:
      if e.kind == ceUnsupportedHof and e.severity == sevError:
        sawHof = true
    check sawHof

  test "C4-3: symbolic-length map axiom path TERMINATES (no Z3Error / hang)":
    let r = symexFind(sutMapSymbolic, tLabel("symmap"))
    # Verdict may be sxSat or sxUnknown; the DoD is termination without crash.
    check r.status in {sxSat, sxUnknown}

  test "C4-4: user-defined `filter` (non-sequtils) is NOT hijacked by HOF dispatch":
    let r = symexFind(sutUserFilter, tLabel("userfilter"))
    # Falls through to the standard isCall descent — NOT an incorrect HOF
    # dispatch. The result is allowed to be any status, but if it degrades it
    # must NOT be via a ceUnsupportedHof (that would mean wrong dispatch).
    for e in r.errors:
      check e.kind != ceUnsupportedHof

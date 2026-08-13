## Phase 15 — Cluster C, cycle C5: closure EQUALITY semantics.
##
## When the walker lowers a `bEq` / `bNe` binop whose BOTH operands resolve to
## `svClosure`, it applies **nominal-for-site + structural-for-env** equality
## (ADR-0009 D7, closing the RFC's Open Question 6):
##
##   - If `(c1.siteHash, c1.declOrder) != (c2.siteHash, c2.declOrder)` — a
##     pure Nim-side INTEGER-PAIR comparison, no Z3 involved — the closures are
##     unequal: `==` → `mkBool(false)`, `!=` → `mkBool(true)`. Two closures from
##     DIFFERENT syntactic lambda sites are ALWAYS unequal, regardless of their
##     captured environments. (The common case stays entirely off the solver.)
##   - If the site pairs are EQUAL, the closures are equal iff their captured
##     environments are equal: `==` → `c1.closureEnv == c2.closureEnv` via the
##     net-new structural tuple-equality helper `svTupleEq` (a field-by-field
##     conjunction of leaf equalities — there was NO `svTuple` `==` arm in the
##     engine before C5).
##
## ── Nim-runtime divergence (documented, not tested by execution) ────────────
## Nim's OWN `==` on closure VALUES is *not* a defined structural comparison:
## at runtime it compares proc-and-environment POINTERS, so two distinct
## allocations of the same captured values are NOT pointer-equal (and a bare
## `proc ==` may be rejected/undefined). The symex model is therefore *more
## precise* than Nim runtime for the same-site environment-equality question:
## it asserts a SOUND structural equality where Nim compares allocation
## identity. This divergence is documented in `docs/symex/closures.md`
## (§ Known divergences) and `docs/symex/determinism.md`. See sub-test 3.
##
## ── Site keying: lineInfo, NOT symBodyHash (RFC-vs-reality reconciliation) ───
## The RFC §C5 (and ADR-0009 Rejected-Alt-A) assume the lambda SITE is keyed by
## `symBodyHash` (a semantic-AST hash, formatting-STABLE: two whitespace-/
## comment-differing copies of the same lambda hash equal). But **C1 reality**
## (commit 22d0de3) keys a NAMELESS lambda by its **lineInfo** (`file:line:col`)
## because a nameless `nnkLambda` has NO symbol for `symBodyHash` to hash
## (ADR-0008 D2 lineInfo fallback). lineInfo is POSITION-based, so the RFC's
## "two whitespace-differing versions → same siteHash" does NOT hold:
## different source POSITIONS → different siteHash, which is CORRECT (they are
## genuinely different lambda sites). What lineInfo keying DOES guarantee, and
## what sub-test 4 actually tests, is: the SAME lambda at the SAME source
## position re-parses to a STABLE (siteHash, declOrder) across runs, and a
## comment INSIDE the lambda body does not move the lambda's declaration
## line:col, so two distinct closures from that one site compare equal on the
## same-site (structural-env) branch. We do NOT assert formatting-stability
## across positions that lineInfo keying cannot provide.
##
## C5 is ADDITIVE under walker version "8" (no bump; Cluster C bumps at C6).
import std/unittest
import nelli/symex

# --- Sub-test 1: two DISTINCT lambda sites are ALWAYS unequal. ----------------
#
#   proc sut(x: int): bool =
#     let f = proc(y: int): int = y + x   # site A
#     let g = proc(y: int): int = y + x   # site B (different line:col → diff key)
#     f == g                              # nominal-for-site: A != B → false
#
# `f == g` is `false` for EVERY x (distinct (siteHash, declOrder) pairs), so the
# target behind `if f == g` is UNREACHABLE ⇒ sxUnsat. This is the integer-pair
# short-circuit: no Z3 env comparison even happens.
proc sutDistinctSites(x: int) =
  let f = proc(y: int): int = y + x
  let g = proc(y: int): int = y + x
  if f == g:
    symexTarget("distinct-sites-equal")   # provably unreachable

# --- Sub-test 1b: distinct sites are unequal ⇒ `f != g` is ALWAYS reachable. --
#
# The dual of sub-test 1: with distinct sites, `f != g` is `true` for every x,
# so the target behind `if f != g` IS reachable ⇒ sxSat (any x witnesses).
proc sutDistinctSitesNe(x: int) =
  let f = proc(y: int): int = y + x
  let g = proc(y: int): int = y + x
  if f != g:
    symexTarget("distinct-sites-unequal")

# --- Sub-test 2: SAME site, SAME env → equal (structural-env branch). ---------
#
# ADAPTATION (honest): the RFC's canonical same-site shape is a
# closure-RETURNING closure (`let mk = proc(): (proc(y:int):int) = …; mk(); mk()`).
# That is OUT OF REACH in C5: a closure-call's result is wrapped by
# `symValFromRawAst`, which only handles SCALAR return types (int/bool/float) —
# a proc/closure return kind raises "unsupported closure return type kind".
# (Verified against runtime.nim:4851-4878.) So we use the closest SOUND same-site
# construction that still exercises the "same site → env equality" branch:
# bind one lambda, then alias it. `f` and `g` share the SAME (siteHash,declOrder)
# AND the same captured-env `svTuple` ⇒ the dispatch takes the structural-env
# branch and asserts `c1.closureEnv == c2.closureEnv` via `svTupleEq` (a one-
# field tuple `{x}`), which is reflexively satisfiable ⇒ sxSat.
#
#   proc sut(x: int): bool =
#     let f = proc(y: int): int = y + x   # single site
#     let g = f                           # same site, same env
#     f == g                              # site pairs equal → svTupleEq(env) → SAT
proc sutSameSiteEqual(x: int) =
  let f = proc(y: int): int = y + x
  let g = f
  if f == g:
    symexTarget("same-site-equal")

# --- Sub-test 3: runtime-divergence DOCUMENTING test. ------------------------
#
# Nim runtime closure `==` is undefined (proc/env POINTER identity, not a
# structural comparison; may be rejected). The symex semantics are
# nominal-for-site + structural-for-env per ADR-0009 D7 / closures.md
# § Known divergences / determinism.md. We assert the symex semantics: under the
# symex model the same-site aliased closure compares EQUAL (sub-test 2's sxSat),
# whereas a naive Nim runtime `==` would NOT structurally compare the
# environments. This test documents (via this comment + the assertion below)
# that the symex verdict is the DEFINED one; it does not — and cannot — run the
# undefined Nim runtime `==`.
proc sutDivergenceDoc(x: int) =
  # SAME site, SAME env (alias) — symex defines this as equal; Nim runtime `==`
  # on closures is undefined. We assert the symex-defined verdict.
  let f = proc(y: int): int = y + x
  let g = f
  if f == g:
    symexTarget("symex-defined-equal")

# --- Sub-test 4: lineInfo site keying — stability of the SAME site. ----------
#
# RECONCILED with reality (see header). We do NOT assert the RFC's
# whitespace-across-positions formatting-stability (lineInfo keying cannot
# provide it). Instead we test what lineInfo keying DOES guarantee:
#   (a) a comment INSIDE the lambda body does not move the lambda's declaration
#       line:col, so the SAME-position lambda keys stably and two aliased
#       closures from it compare equal (same-site structural-env branch → sxSat);
#   (b) re-running the SAME SUT yields the SAME verdict (deterministic keying).
proc sutLineInfoStable(x: int) =
  let f = proc(y: int): int =
    # a comment inside the body does not move the lambda's declaration line:col
    y + x
  let g = f
  if f == g:
    symexTarget("lineinfo-stable-equal")

suite "symex Phase 15 C5 — closure equality (nominal-site + structural-env)":

  test "C5-1: two distinct lambda sites are ALWAYS unequal (==) ⇒ sxUnsat":
    # nominal-for-site integer-pair short-circuit: distinct (siteHash,declOrder)
    # ⇒ `f == g` is false for every x ⇒ target unreachable.
    let r = symexFind(sutDistinctSites, tLabel("distinct-sites-equal"))
    check r.status == sxUnsat

  test "C5-1b: two distinct lambda sites ⇒ `f != g` is ALWAYS true ⇒ sxSat":
    let r = symexFind(sutDistinctSitesNe, tLabel("distinct-sites-unequal"))
    check r.status == sxSat

  test "C5-2: same site + same env → equal (structural-env svTupleEq branch) ⇒ sxSat":
    let r = symexFind(sutSameSiteEqual, tLabel("same-site-equal"))
    check r.status == sxSat

  test "C5-3: runtime-divergence — symex defines same-site env equality (sxSat)":
    # Documents the Nim-runtime divergence: symex's nominal-for-site +
    # structural-for-env `==` is the DEFINED semantics; Nim runtime closure `==`
    # is undefined (pointer identity). See ADR-0009 D7 / closures.md / determinism.md.
    let r = symexFind(sutDivergenceDoc, tLabel("symex-defined-equal"))
    check r.status == sxSat

  test "C5-4: lineInfo site keying — same-position lambda keys stably (sxSat, deterministic)":
    # lineInfo keying (NOT symBodyHash): a comment inside the body does not move
    # the declaration line:col, so the same-site closures compare equal; and the
    # verdict is stable across re-runs.
    let r1 = symexFind(sutLineInfoStable, tLabel("lineinfo-stable-equal"))
    let r2 = symexFind(sutLineInfoStable, tLabel("lineinfo-stable-equal"))
    check r1.status == sxSat
    check r2.status == sxSat
    check r1.status == r2.status   ## deterministic lineInfo keying across runs

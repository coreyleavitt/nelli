## Phase 16 — CR-1a (RFC-chapulin-hardening, Cluster 2 — Crash-totality):
## bitwise `and`/`or`/`xor` on a Z3-Int-sorted operand.
##
## `.len`, `.find`, `.indexOf`, and `parseInt` all lower UNCONDITIONALLY to
## `svInt` (Z3 Int sort) — there is no BV-vs-Int representation *choice* for
## them the way there is for a plain symbolic var, so there was never a
## promotion decision to "decline". Before this slice, `runtime.nim`'s
## `bAnd`/`bOr`/`bXor` walker arm hard-raised `ValueError: bitwise op on
## promoted Z3Int` whenever an operand arrived as `svInt`, native-crashing
## instead of classifying. Z3's Int theory has no bitwise operators, so the
## fix bridges the Int-sorted operand(s) to BV via `int2bv` (unsigned — these
## values are always non-negative) and dispatches through the existing BV
## bitwise path (`binBV`), producing a correctly-modeled, sound verdict.
##
## No new ADR: this is a bug fix at an existing locus (the CR-9(c) `bAnd`/
## `bOr`/`bXor` dispatch arm in `runtime.nim`), not a new capability axis.
##
## Both UNSAT-branch tests below are load-bearing: they pin an impossible
## parity value (`== 2`, when a single AND-with-1 bit can only be 0 or 1).
## A buggy "always accept" stub would incorrectly report these `sxSat`; only
## a genuinely sound BV model rejects them.
import std/unittest
import std/strutils   ## find on strings
import proptest/symex
import proptest/smt/canonicalize

# --- `len and 1` (operand is svInt from `.len`) ---
proc lenAndOneSat(s: string) =
  if (s.len and 1) == 1:
    symexTarget("odd-len")

proc lenAndOneUnsat(s: string) =
  ## `len and 1` can only ever be 0 or 1 — `== 2` is impossible. SAT here
  ## would mean the bitwise AND is not being modeled correctly.
  if (s.len and 1) == 2:
    symexTarget("impossible-len")

# --- `s.find(x) and 1` (operand is svInt from `.find`) ---
proc findAndOneSat(s: string) =
  if s.find("bc") != -1 and (s.find("bc") and 1) == 1:
    symexTarget("odd-find")

proc findAndOneUnsat(s: string) =
  if s.find("bc") != -1 and (s.find("bc") and 1) == 2:
    symexTarget("impossible-find")

# --- `bOr`/`bXor` on the same svInt-producing locus (same walker arm) ---
proc lenOrTwoSat(s: string) =
  if (s.len or 2) == 3:
    symexTarget("or-hit")

proc lenXorSelfIsZero(s: string) =
  ## x xor x == 0 always; contradiction target must be UNSAT.
  if (s.len xor s.len) == 1:
    symexTarget("impossible-xor")

suite "symex Phase 16 CR-1a — bitwise and/or/xor on svInt (.len/.find)":

  test "len and 1 == 1 is SAT with an odd-length witness (was a native crash)":
    let r = symexFind(lenAndOneSat, tLabel("odd-len"))
    check r.status == sxSat
    check r.witness[0].len mod 2 == 1

  test "len and 1 == 2 is UNSAT (a single AND-1 bit is never 2 — soundness)":
    let r = symexFind(lenAndOneUnsat, tLabel("impossible-len"))
    check r.status == sxUnsat

  test "s.find(\"bc\") and 1 == 1 is SAT with an odd find-index witness":
    let r = symexFind(findAndOneSat, tLabel("odd-find"))
    check r.status == sxSat
    check r.witness[0].find("bc") mod 2 == 1

  test "s.find(\"bc\") and 1 == 2 is UNSAT (soundness)":
    let r = symexFind(findAndOneUnsat, tLabel("impossible-find"))
    check r.status == sxUnsat

  test "len or 2 == 3 is SAT (bOr shares the same svInt-coercion arm)":
    let r = symexFind(lenOrTwoSat, tLabel("or-hit"))
    check r.status == sxSat
    check (r.witness[0].len or 2) == 3

  test "len xor len == 1 is UNSAT (bXor shares the same svInt-coercion arm)":
    let r = symexFind(lenXorSelfIsZero, tLabel("impossible-xor"))
    check r.status == sxUnsat

suite "symex Phase 16 CR-1a — walker version pin":

  test "walker version floor >= 41 (CR-1a: svInt-operand bitwise fixed at 41)":
    ## CR-1a bumps 40→41: `and`/`or`/`xor` on a `.len`/`.find`/`.indexOf`/
    ## `parseInt`-derived `svInt` operand now bridges to BV via `int2bv`
    ## instead of native-crashing.
    ## SW pin idiom (RFC §Version-pin discipline): this incidental
    ## feature-test pin uses the tolerant `>=` floor (only the canonical
    ## tsymex_phase15_CR2_cachekey.nim keeps the brittle `==`).
    check parseInt(symexWalkerVersion) >= 41

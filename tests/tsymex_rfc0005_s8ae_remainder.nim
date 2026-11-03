## RFC-0005 (soundness channels) slice S8ae -- S8v's remainder.
##
## `checkCapped`'s step 1c checks a query that step 1 found UNSAT under the
## `maxSeqLen` caps with no sequence theory, plus `seqRangeFacts`: facts
## each valid in the theory. It checks them first without the caps (an
## UNSAT is the query's own), then with them (an UNSAT is the cap's: a
## decline, with no sequence-theory search, RFC-0005 S8r / S8v).
##
## (1) A query refuted only by the theory's relations between two of its
##     functions, such as `str.indexof(s, ":", 0) > 200 and not
##     str.contains(s, ":")`, was a cap decline: theory-free, the `indexof`
##     range fact lets `> 200` through only past the cap, so step 1c's
##     capped check was UNSAT. Before S8r step 2's unsat core decided it.
##     The facts now link the functions (`indexof >= 0` implies `contains`,
##     and so on), so the uncapped fact check refutes it: `sxUnsat`.
##     Running step 2 again behind step 1c under a small `rlimit` was
##     measured and rejected (the RFC's S8ae note): its core names the cap
##     on the `startsWith` and slice shapes below anyway, and `rlimit` does
##     not bound it on a query SAT only past the cap (`s.len > 210 and
##     s[205] == 'x'`: 49 s and 1.2 GB under 200k units on Z3 5.1).
## (2) `str.at`, `str.substr`, `str.to_code` and `str.to_int` had no
##     facts, and a string equal to another term had no length link, so a
##     cap conflict through them was SAT theory-free and reached step 2.
##     `str.len(a ++ b)` needs no fact: Z3's rewriter folds it to
##     `len(a) + len(b)` with the theory off too.
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8ae_remainder_b`, `tsymex_rfc0005_s8ae_remainder_c`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 80 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc sidx(ctx: Z3Context; s, t: Z3String; i: Z3Int): Z3Int =
  wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_index(ctx.raw, s.raw, t.raw, i.raw))

proc stepOneC(ctx: Z3Context; roots: seq[Z3Bool]; caps: seq[Z3Bool] = @[]):
    Z3Status =
  ## The query as step 1c poses it: no sequence theory, with the facts
  ## (built from the query alone, as `checkCapped` does), and the caps.
  let s = querySolver(ctx, roots, 1_000_000'u, seqTheory = false)
  for f in seqRangeFacts(ctx, roots): s.add f
  for c in caps: s.add c
  s.check()

# ---- (1) relational facts: UNSAT through two functions is the query's own --

proc colonPastCap(s: string) =
  if s.find(':') > 200 and ':' notin s:
    symexTarget("s8ae_find_notin")

proc prefixFoundLate(s: string) =
  if s.startsWith("abc") and s.find("abc") > 150:
    symexTarget("s8ae_prefix_find")

proc pieceFoundLate(s: string) =
  if s.len > 3 and s[1..2] == "ab" and s.find("ab") > 150:
    symexTarget("s8ae_piece_find")

proc byteNotContained(s: string) =
  if s.len > 150 and s[140] == ':' and ':' notin s:
    symexTarget("s8ae_byte_notin")

proc colonFoundEarly(s: string) =
  if s.find(':') > 5 and ':' in s:
    symexTarget("s8ae_found_early")

proc concatLong(s, t: string) =
  if (s & t).len > 300:
    symexTarget("s8ae_concat_long")

suite "S8ae (1): UNSAT through the theory's relations is decided":

  test "find > 200 and notin: sxUnsat, not a maxSeqLen decline":
    let r = symexFind(colonPastCap, tLabel("s8ae_find_notin"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "startsWith and a late find of the prefix: sxUnsat":
    let r = symexFind(prefixFoundLate, tLabel("s8ae_prefix_find"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "a slice equal to the needle and a late find of it: sxUnsat":
    let r = symexFind(pieceFoundLate, tLabel("s8ae_piece_find"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "a byte equal to the needle and notin: sxUnsat":
    # `s[140]` is past the 128 cap: the cap refutes it too, so before this
    # slice it was a decline.
    let r = symexFind(byteNotContained, tLabel("s8ae_byte_notin"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "companion: find > 5 and in is still sxSat":
    let r = symexFind(colonFoundEarly, tLabel("s8ae_found_early"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "companion: a real >128-byte witness stays a maxSeqLen decline":
    let r = symexFind(concatLong, tLabel("s8ae_concat_long"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    var capped = false
    for e in r.errors:
      if e.kind == beSolverUndef and "maxSeqLen" in e.msg: capped = true
    check capped

  test "the example query is UNSAT theory-free with the facts, no cap":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let colon = mkString(ctx, ":")
    let roots = @[sidx(ctx, s, colon, mkInt(ctx, 0)) > mkInt(ctx, 200),
                  not contains(s, colon)]
    check stepOneC(ctx, roots) == zsUnsat

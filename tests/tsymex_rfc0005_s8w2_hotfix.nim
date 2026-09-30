## RFC-0005 S8w2 -- hotfix for S8w (12c2220), red on symex-mingw (Z3 4.13.4).
##
## 1. `tsymex_r6_nulwitness` NW-2-content and `tsymex_r6_b4_readcstring`
##    B4-8-content: S8w's join of a short-circuit guard (`mergeJoinPaths`)
##    merged the chain's guard temporary as `ite(c, d, c)`. That is `c and
##    d` -- equivalent, but not the query the pre-S8w walk built, and Z3
##    4.13.4 answered it with a different valid model (`"AB\0\xFE"`, one
##    byte past the terminator the content check pins). The join now builds
##    the connective. Z3 5.1 happens to pick the short model either way, so
##    the pins here read the query text (`-d:symexQueryStats`, from this
##    file's `.nim.cfg`) and fail on 5.1 as well.
## 2. `tsymex_rfc0005_s8w_remainder` "a shift on an unstamped int is
##    modelled": `find(..) shr 1` bridged the Int through `int2bv`, which
##    cost Z3 4.13.4 the whole `seqQueryRLimit`. A literal `shr` on an
##    unstamped Int is now floor division in Int arithmetic; the pin reads
##    that the query holds no `int2bv` (`int_to_bv` in Z3 5.1's printing).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/runtime

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8w2_hotfix needs -d:symexQueryStats (its .nim.cfg)".}

proc satQueries(): seq[string] =
  for q in symexQueryStats:
    if q.status == "sat": result.add q.query

proc sutAndJoin(x: int, y: int) =
  if x == 5 and y + 1 == 7:
    symexTarget("s8w2_and")

proc sutOrJoin(x: int, y: int) =
  if x != 5 or y + 1 == 7:
    discard
  else:
    symexTarget("s8w2_or")

proc sutFindShr(s: string) =
  if (s.find('a') shr 1) < 0 and s.len > 2:
    symexTarget("s8w2_findshr")

proc sutFindShrPos(s: string) =
  if (s.find('a') shr 2) == 1 and s.len < 8:
    symexTarget("s8w2_findshr_pos")

suite "RFC-0005 S8w2":

  test "an and-chain's join is a conjunction, not an ite":
    symexQueryStats = @[]
    let r = symexFind(sutAndJoin, tLabel("s8w2_and"))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5 and r.witness[1] + 1 == 7
    let qs = satQueries()
    check qs.len > 0
    for q in qs:
      check "(ite " notin q

  test "an or-chain's join is a disjunction, not an ite":
    symexQueryStats = @[]
    let r = symexFind(sutOrJoin, tLabel("s8w2_or"))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5 and r.witness[1] + 1 != 7
    let qs = satQueries()
    check qs.len > 0
    for q in qs:
      check "(ite " notin q

  test "a literal shr on an unstamped Int needs no int2bv":
    symexQueryStats = @[]
    let r = symexFind(sutFindShr, tLabel("s8w2_findshr"))
    check r.status == sxSat
    if r.status == sxSat:
      check (r.witness[0].find('a') shr 1) < 0 and r.witness[0].len > 2
    let qs = satQueries()
    check qs.len > 0
    for q in qs:
      # Z3 5.1 prints the bridge `(_ int_to_bv 64)`, 4.13.4 `(_ int2bv 64)`.
      check "int2bv" notin q and "int_to_bv" notin q

  test "a literal shr on a non-negative unstamped Int floors":
    check (5 shr 2) == 1 and (4 shr 2) == 1 and (7 shr 2) == 1
    let r = symexFind(sutFindShrPos, tLabel("s8w2_findshr_pos"))
    check r.status == sxSat
    if r.status == sxSat:
      let i = r.witness[0].find('a')
      check i in 4 .. 7 and (i shr 2) == 1 and r.witness[0].len < 8

## RFC-0005 S8cf (item 3) -- 8.37's JIT's LIMIT_MATCH: `count_match` sites, not
## `match()` calls. On a JIT libpcre each corpus call is checked against native
## std/re; the automaton is pinned anywhere.
##
## RFC-0005 S8cm: part 1 of 2 of this suite, with
## `tsymex_rfc0005_s8cf_jitlimit_b`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 68 s).

import std/[unittest, re, strutils]
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
import ./s8bt_harness/limit_corpus

proc jitFind(s: string) =
  if s == "aaaaa" and s.find(re"(*LIMIT_MATCH=3)(a|b)*[cd]") == -8:
    symexTarget("cf_jit_count")

proc jitFindNo(s: string) =
  if s == "aaaaa" and s.find(re"(*LIMIT_MATCH=3)(a|b)*[cd]") == -1:
    symexTarget("cf_jit_count_no")

suite "S8cf: the JIT's LIMIT_MATCH":
  test "the automaton counts":
    let n = buildNfa(parsePcre("(*LIMIT_MATCH=3)(a|b)*[cd]"), peJit837, limitRoom = 0)
    check limitEffect(n)[0] == leCounted
    check pcreExec(n, "aaaaa", 0, false)[0] == pcreErrMatchLimit
    let m = buildNfa(parsePcre("(*LIMIT_MATCH=9)(a|b)*[cd]"), peJit837, limitRoom = 0)
    check pcreExec(m, "aaaaa", 0, false)[0] == -1
    let u = buildNfa(parsePcre("(*LIMIT_MATCH=3)(?:a){3}"), peJit837, limitRoom = 0)
    check limitEffect(u)[0] == leUnknown

  test "the walker decides it":
    overridePcreLib("8.37 2015-04-28", true)
    defer: clearPcreLibOverride()
    check symexFind(jitFind, tLabel("cf_jit_count")).status == sxSat
    check symexFind(jitFindNo, tLabel("cf_jit_count_no")).status == sxUnsat

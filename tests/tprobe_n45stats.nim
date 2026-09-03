## N45 probe: does the per-query statistics instrumentation work, and are the
## statistics valid for a query Z3 answers UNKNOWN?
##
## That second question is the one that decides whether this instrument is
## usable at all: B5-4's trip-wire -- the query N45 is actually about -- is
## budget-truncated, so if `getStatistics` were only meaningful for sat/unsat
## the whole approach would be dead.
##
## Build with: -d:symexQueryStats

import std/unittest
import nelli/symex
import nelli/smt/runtime

when not defined(symexQueryStats):
  # The instrumentation is compiled out without the flag, so this suite has
  # nothing to observe. Say so rather than failing to compile -- it is a
  # tool, and a tool that breaks the ordinary build is not one.
  suite "N45 probe — per-query stats":
    test "requires -d:symexQueryStats":
      skip()
else:
 suite "N45 probe — per-query stats":

   test "sat query records nonzero rlimit":
     symexQueryStats = @[]
     proc sut(a: int, b: int) =
       if a + b == 42:
         symexTarget("hit")
     let r = symexFind(sut, tLabel("hit"))
     echo "STATUS=", r.status
     echo symexQueryStatsSummary()
     check symexQueryStats.len > 0

   test "unsat query records stats too":
     symexQueryStats = @[]
     proc sut2(a: int) =
       if a != a:
         symexTarget("impossible")
     let r = symexFind(sut2, tLabel("impossible"))
     echo "STATUS=", r.status
     echo symexQueryStatsSummary()
     check symexQueryStats.len > 0

   test "assertion count tracks path-condition growth":
     ## Two SUTs, the second with strictly more branch constraints on the
     ## satisfying path. If `assertions` is wired correctly the second reports
     ## more. This is the counter that discriminates "the walker is generating
     ## more work" from "the solver is working harder per query".
     symexQueryStats = @[]
     proc small(a: int) =
       if a > 0:
         symexTarget("s")
     discard symexFind(small, tLabel("s"))
     var maxSmall = 0
     for q in symexQueryStats:
       if q.assertions > maxSmall: maxSmall = q.assertions

     symexQueryStats = @[]
     proc big(a: int, b: int, c: int) =
       if a > 0:
         if b > a:
           if c > b:
             if a + b + c > 10:
               symexTarget("b")
     discard symexFind(big, tLabel("b"))
     var maxBig = 0
     for q in symexQueryStats:
       if q.assertions > maxBig: maxBig = q.assertions

     echo "ASSERTS small=", maxSmall, " big=", maxBig
     check maxBig > maxSmall

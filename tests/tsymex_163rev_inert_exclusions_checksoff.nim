## RFC-0016 W1-d2 (W-07), the checks-off build half of
## `tsymex_163rev_inert_exclusions` R14c. This file builds with
## `--overflowChecks:off` (its `.nim.cfg`): the wrap scan reads the BUILD
## (`buildWraps()`), not an `arithChecks` opt-out, so the whole-program ban of
## an unprovable add/sub/mul is only meaningful here. Moved, not weakened: the
## per-variable-banning regression pin is the same.
import std/unittest
import nelli/symex

const Unchecked = SymexSettings(integerSemantics: isOptimised)

proc safeAlone(safeP: range[0'i64..1000'i64]) =
  let s = safeP + safeP     ## <= 2000 -- provably safe in isolation
  symexTarget("t")
  discard s

proc mixedBan(safeP: range[0'i64..1000'i64],
              unsafeP: range[0'i64..4_000_000_000'i64]) =
  let s = safeP + safeP        ## still provably safe, taken alone
  let u = unsafeP * unsafeP    ## reaches 1.6e19 -- NOT provably safe
  symexTarget("t")
  discard s
  discard u

suite "#163 review R14c -- the wrap-scan bans the whole program, not per-variable":

  test "oracle -- safeP's own doubling never leaves int64, unsafeP's square does":
    proc rtSafe(a: range[0'i64..1000'i64]): int64 = a + a
    check rtSafe(1000'i64) == 2000'i64
    {.push overflowChecks: off.}
    proc rtUnsafe(a: range[0'i64..4_000_000_000'i64]): int64 = a * a
    {.pop.}
    ## True product at the ceiling is 1.6e19, which does not fit int64 (max
    ## ~9.22e18) -- it wraps under unchecked semantics to a negative value,
    ## which is the whole reason it is "unprovable": no finite int64
    ## interval bounds it honestly.
    check rtUnsafe(4_000_000_000'i64) < 0'i64

  test "in isolation, the provably-safe param DOES promote":
    let r = symexFind(safeAlone, tLabel("t"), Unchecked)
    check r.status == sxSat
    check r.abstractions.len == 1

  test "sharing a program with an unprovable sibling, NEITHER param promotes":
    ## The load-bearing property. A per-variable-banning regression would
    ## leave `safeP` promoted here (`abstractions.len == 1`, naming only
    ## `safeP`) even though `unsafeP` is banned -- exactly the mixed-sort
    ## state the comment says must never happen under unchecked semantics.
    let r = symexFind(mixedBan, tLabel("t"), Unchecked)
    check r.status == sxSat
    check r.abstractions.len == 0



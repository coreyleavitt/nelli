## RFC-0016 int6-a, leaked scopes, a fallback: a stdlib module imported under
## a push. The scan does not read a library module's own imports, so it
## cannot tell which stdlib modules that import first compiles: each stdlib
## routine reads as possibly under the push, the coarse reading. Natively
## `strutils` is compiled first, before the push, and `cmpIgnoreStyle` keeps
## its own scope: the walk declines where it could have been exact. A user
## module first compiled under the same push is still replayed:
## `leakConv(300)` keeps 300 and is walked pushed.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/errorkind

{.push rangeChecks: off.}
import std/[unicode, strtabs]
import ./s0016_int6a_leaked
{.pop.}

import ./s8cu_helpers

const gk = cellKey(faGeneric, "int6a_leaklib")

proc callsLeaked(v: int) =
  if leakConv(v) == 300: symexTarget("hit")

proc cmpStyle(a: string) =
  if a.len == 1 and cmpIgnoreStyle(a, "_F") == 0: symexTarget("hit")

suite "int6-a leaked scopes: a stdlib import under a push":
  test "a stdlib routine reads as possibly under it and declines":
    check native(cmpStyle("f")) == "hit"
    pinDecline(cmpStyle, gk, feCheckOption, needle = "rangeChecks")
  test "a user module first compiled under it is still walked pushed":
    check native(callsLeaked(300)) == "hit"
    let r = pinFind(callsLeaked, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.errors.named(feCheckOption)

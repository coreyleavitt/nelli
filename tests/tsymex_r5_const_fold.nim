## Round-5 — module-level `const` symbols fold to their values (v69).
##
## Root cause of chapulin's "bare `&`-concat of an unconstrained string
## proves only sxUnknown" HIGH finding — which was never about concat: a
## const sym in value position emitted `iekVar(name)` with no binding in any
## env (module consts are never walked) → KeyError → weInternalWalkerFault →
## sxUnknown in whatever expression referenced it. Spellings where the const
## happened to fold to a literal proved fine — the reported
## shape-sensitivity. v69 folds nskConst syms to their values at parse time.
import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

const SidecarExt = ".md5"
const Radix = 16'i32

proc constSuffixLen(s: string) =
  ## The chapulin writeSidecar lemma, natural spelling.
  let t = s & SidecarExt
  symexAssert(t.len == s.len + 4)

proc constSuffixSat(s: string) =
  let t = s & SidecarExt
  if t.endsWith(".md5") and s.len == 3:
    symexTarget("suffix-lands")

proc mkName(s: string): string =
  result = s & SidecarExt

proc constInCallee(s: string) =
  ## Const referenced inside a walked callee.
  let t = mkName(s)
  symexAssert(t.len == s.len + 4)

proc constInPlace(s: string) =
  ## `&=` spelling.
  var t = s
  t &= SidecarExt
  symexAssert(t.len == s.len + 4)

proc constIntWidth(x: int32) =
  ## A fixed-width int const folds AND shapes at the declared width
  ## (composes with the v69 literal-width protos — no svBV64 leak).
  symexAssume(x >= 0'i32 and x <= 100'i32)
  let scaled = x * Radix
  symexAssert(scaled >= 0'i32 and scaled <= 1600'i32)

suite "symex round-5 — const-symbol folding":

  test "concat with const suffix: length lemma proves (was sxUnknown)":
    let r = symexFind(constSuffixLen, tAssertionViolation())
    check r.status == sxUnsat
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "concat with const suffix: witness through the fold (non-vacuous SAT)":
    let r = symexFind(constSuffixSat, tLabel("suffix-lands"))
    check r.status == sxSat

  test "const referenced inside a walked callee proves":
    let r = symexFind(constInCallee, tAssertionViolation())
    check r.status == sxUnsat
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "`&=` with const suffix proves":
    let r = symexFind(constInPlace, tAssertionViolation())
    check r.status == sxUnsat
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

  test "fixed-width int const folds at declared width (no svBV64 leak)":
    let r = symexFind(constIntWidth, tAssertionViolation())
    check r.status == sxUnsat
    check not r.errors.anyIt(it.kind == weInternalWalkerFault)

suite "symex round-5 const fold — walker version pin":

  test "walker version floor >= 69":
    check parseInt(symexWalkerVersion) >= 69
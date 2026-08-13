## RFC Cluster 3 M6 — `probeProto` sentinel completeness (defensive).
##
## `probeProto` (runtime.nim ~1758) returns a per-op "prototype" SymVal so a
## surrounding comparison/bitwise/arith op lowers its OTHER operand (typically
## a literal) at the right Z3 representation. Its `StrOpKinds - {...modeled}`
## catch-all previously omitted `iekStrToLower`/`iekStrToUpper`/`iekRadixFmt`/
## `iekRuneToStr` from the modeled set, so probing any of these four ops fell
## through to `none` instead of an `svString` sentinel. All four in fact
## lower to Z3Strings (runtime_strings.nim: `SymVal(kind: svString, ...)` in
## each of their arms) — so `none` was the wrong proto kind. This slice adds
## the four kinds to the `svString` arm alongside
## `iekIntToStr`/`iekStrReplace`/`iekStrReplaceAll`/`iekStrReplaceRe`/
## `iekStrJoin`/`iekStrConcat`.
##
## TESTING HONESTY — verified INERT, not assumed:
## `lowerStrArm` (runtime_strings.nim:88-91)'s own doc comment states
## "`proto` is NOT used by any string arm" — and indeed `lower()`'s dispatch
## (`of iekStrLit, StrOpKinds: lowerStrArm(env, e)`, runtime.nim ~2775) never
## even threads its `proto` parameter through to `lowerStrArm`. So whatever
## `probeProto` returns for these four kinds is STRUCTURALLY inert to every
## string-arm lowering decision today, not merely "inert in the cases we
## happened to check." Empirically confirmed: every SUT below — direct
## literal `==`/`!=` AND the cross-op COMPOUND comparisons (where neither
## operand is a bare literal or env-var, so `probeProto`'s own lhs-then-rhs
## binop recursion is the exact site whose `isSome`/`isNone` RESULT flips
## between the pre-fix and post-fix code) — produces IDENTICAL verdicts and
## witnesses before and after this change. There is therefore no
## distinguishing RED here: this is a regression-protection suite, not a
## RED->GREEN test. The four ops' `== "lit"` comparisons already work today
## via the `bEq`/`bNe` PROBE-MISS fallback (runtime.nim ~3011-3016): when
## `probeProto` returns `none`, the fallback lowers the LHS first with no
## proto guidance (string ops/literals don't need one), then hands the LHS's
## REAL computed SymVal to the RHS as ITS proto — recovering the correct
## representation regardless of what the (buggy or fixed) top-level probe
## returned. This suite guards against the day some future string arm starts
## consulting `proto`, at which point a wrong `none` here would go live and
## silently wrong. NO version bump: `symexWalkerVersion` stays "51" — no
## verdict changed by this slice.
##
## Surfaces covered (RFC M6; also confirms Healed #7 — A9's `toLowerAscii`/
## `toUpperAscii` fix already gives correct end-to-end verdicts):
##   iekStrToLower / iekStrToUpper  -> toLowerAscii(s) / toUpperAscii(s) (A9)
##   iekRadixFmt                    -> toHex(x) (A8)
##   iekRuneToStr                   -> $r where r: Rune (A7-S2)

import std/[unittest, strutils, unicode]
import nelli/symex
import nelli/smt/canonicalize

# ---- individual literal-equality SUTs (one per newly-added kind) -----------

proc lowerEqAbc(s: string) =
  if s.toLowerAscii == "abc":
    symexTarget("lower_eq")

proc upperEqAbc(s: string) =
  if s.toUpperAscii == "ABC":
    symexTarget("upper_eq")

proc hexEqFF(x: uint8) =
  if toHex(x) == "FF":
    symexTarget("hex_eq")

proc runeEqA(r: Rune) =
  if $r == "A":
    symexTarget("rune_eq")

# ---- literal not-equal SUTs (bNe shares probeProto's call site) ------------

proc lowerNeXyz(s: string) =
  if s.toLowerAscii != "xyz":
    symexTarget("lower_ne")

proc hexNeGG(x: uint8) =
  if toHex(x) != "GG":
    symexTarget("hex_ne")

# ---- COMPOUND: op result compared to ANOTHER op's result -- neither side a
# bare literal/var, so probeProto's own binop recursion is exercised on both
# branches (this is the exact shape whose isSome/isNone flips with this fix,
# even though the final verdict is unaffected). ------------------------------

proc lowerEqUpper(s: string, t: string) =
  if s.toLowerAscii == t.toUpperAscii:
    symexTarget("cross_op")

proc hexEqLower(x: uint8, s: string) =
  if toHex(x) == s.toLowerAscii:
    symexTarget("hex_vs_lower")

# ---- COMPOUND: three-way conjunction combining all four newly-added kinds --

proc allFour(s: string, t: string, x: uint8, r: Rune) =
  if s.toLowerAscii == "abc" and t.toUpperAscii == "XYZ" and
     toHex(x) == "FF" and $r == "A":
    symexTarget("all_four")

suite "symex RFC M6 — probeProto svString proto for toLower/toUpper/radixFmt/runeToStr":

  test "toLowerAscii(s) == \"abc\" -> sxSat, witness folds to \"abc\" (A9 healed; regression)":
    let r = symexFind(lowerEqAbc, tLabel("lower_eq"))
    check r.status == sxSat
    check r.witness[0].toLowerAscii == "abc"

  test "toUpperAscii(s) == \"ABC\" -> sxSat, witness folds to \"ABC\" (A9 healed; regression)":
    let r = symexFind(upperEqAbc, tLabel("upper_eq"))
    check r.status == sxSat
    check r.witness[0].toUpperAscii == "ABC"

  test "toHex(x: uint8) == \"FF\" -> sxSat, witness x == 255 (A8; regression)":
    let r = symexFind(hexEqFF, tLabel("hex_eq"))
    check r.status == sxSat
    check r.witness[0] == 255

  test "$r == \"A\" -> sxSat, witness r == 0x41 (A7-S2; regression)":
    let r = symexFind(runeEqA, tLabel("rune_eq"))
    check r.status == sxSat
    check r.witness[0] == 0x41

  test "toLowerAscii(s) != \"xyz\" -> sxSat (bNe shares probeProto's call site)":
    let r = symexFind(lowerNeXyz, tLabel("lower_ne"))
    check r.status == sxSat
    check r.witness[0].toLowerAscii != "xyz"

  test "toHex(x) != \"GG\" -> sxSat for any x (\"GG\" is not a valid hex-digit string)":
    let r = symexFind(hexNeGG, tLabel("hex_ne"))
    check r.status == sxSat
    check toHex(r.witness[0]) != "GG"

  test "COMPOUND: toLowerAscii(s) == toUpperAscii(t) -> sxSat (e.g. digits-only strings)":
    ## Both operands are freshly-added StrOpKinds; neither side is a bare
    ## literal/env-var. Witness-validated against real Nim semantics, not
    ## against any assumed concrete value.
    let r = symexFind(lowerEqUpper, tLabel("cross_op"))
    check r.status == sxSat
    check r.witness[0].toLowerAscii == r.witness[1].toUpperAscii

  test "COMPOUND: toHex(x) == toLowerAscii(s) -> sxSat (e.g. x=0, s folds to \"00\")":
    let r = symexFind(hexEqLower, tLabel("hex_vs_lower"))
    check r.status == sxSat
    check toHex(r.witness[0]) == r.witness[1].toLowerAscii

  test "COMPOUND: all four ops conjoined -> sxSat, all four witnesses correct":
    let r = symexFind(allFour, tLabel("all_four"))
    check r.status == sxSat
    check r.witness[0].toLowerAscii == "abc"
    check r.witness[1].toUpperAscii == "XYZ"
    check toHex(r.witness[2]) == "FF"
    check r.witness[3] == 0x41

  test "walker version pin: symexWalkerVersion floor >= 51 (no bump -- verified inert)":
    ## M6 is defensive/inert: `lowerStrArm` never reads `proto` (its own doc
    ## comment says so, and `lower()`'s dispatch never threads it through), so
    ## adding these four kinds to probeProto's svString arm cannot change any
    ## lowering decision or verdict. No version bump for this slice.
    check parseInt(symexWalkerVersion) >= 51

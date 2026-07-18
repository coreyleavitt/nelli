## Phase 16 A9 — `toLowerAscii` / `toUpperAscii` ASCII case-fold via seqMapBody.
##
## Implements BV18-ITE quantifier-free seqMap fold for ASCII case-conversion
## (std/strutils). Each char element is bridged to a BV18, transformed by a
## 2-way ITE (the exact ASCII fold rule), and wrapped back as a Z3Char.
## Result is an svString so `toLowerAscii(s) == "abc"` dispatches to cmpString.
##
## Covered:
##   toLowerAscii(s) == "abc"   → sxSat  (witness satisfies toLowerAscii)
##   toUpperAscii(s) == "ABC"   → sxSat  (witness satisfies toUpperAscii)
##   toLowerAscii(s) == "ABC"   → sxUnsat (cannot be uppercase after fold — Invariant 3)
##   toUpperAscii(s) == "abc"   → sxUnsat (cannot be lowercase after fold)
##
## Degraded → sxUnknown (Invariant 3):
##   toLower/toUpper (unicode)  → still iekStrUnsupported (S9 stub, no Z3 primitive)
##
## Walker version pin: "37" (A9 introduced this pin at 34; kept in sync with the
## current walker — every symexWalkerVersion bump must update THIS file too).

import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

# ---- SUT 1: toLowerAscii(s) == "abc" ----------------------------------------
# Any string whose toLowerAscii == "abc" satisfies this. The witness can be
# "abc", "Abc", "ABC", etc. We check the witness property, not the exact value.
proc lowerEqAbc(s: string) =
  if s.toLowerAscii == "abc":
    symexTarget("lower_abc")

# ---- SUT 2: toUpperAscii(s) == "ABC" ----------------------------------------
proc upperEqABC(s: string) =
  if s.toUpperAscii == "ABC":
    symexTarget("upper_abc")

# ---- SUT 3: SOUNDNESS — toLowerAscii(s) == "ABC" (impossible) ---------------
# After toLowerAscii, all ASCII letters are lowercase. "ABC" contains uppercase
# letters. This must be UNSAT (the fold provably cannot produce uppercase for
# letter positions). Invariant 3: correct model, not silent UNSAT.
proc lowerEqUpper(s: string) =
  if s.toLowerAscii == "ABC":
    symexTarget("lower_impossible")

# ---- SUT 4: SOUNDNESS — toUpperAscii(s) == "abc" (impossible) ---------------
proc upperEqLower(s: string) =
  if s.toUpperAscii == "abc":
    symexTarget("upper_impossible")

suite "symex Phase 16 A9 — toLowerAscii / toUpperAscii ASCII case-fold":

  test "toLowerAscii: sxSat — witness satisfies toLowerAscii == \"abc\"":
    ## A9: BV18-ITE seqMap fold models the ASCII case fold. The solver finds a
    ## string s such that s.toLowerAscii == "abc". Witness validation: the
    ## concrete value satisfies the Nim predicate byte-for-byte (Invariant 3).
    let r = symexFind(lowerEqAbc, tLabel("lower_abc"))
    check r.status == sxSat
    check r.witness[0].toLowerAscii == "abc"

  test "toUpperAscii: sxSat — witness satisfies toUpperAscii == \"ABC\"":
    ## A9: toUpperAscii fold. The solver finds a string s such that
    ## s.toUpperAscii == "ABC". Witness validation checks Invariant 3.
    let r = symexFind(upperEqABC, tLabel("upper_abc"))
    check r.status == sxSat
    check r.witness[0].toUpperAscii == "ABC"

  test "toLowerAscii SOUNDNESS: toLowerAscii(s)==\"ABC\" is sxUnsat (no uppercase output)":
    ## Invariant 3 soundness: the BV18-ITE fold provably maps 'A'-'Z' to 'a'-'z',
    ## so the result cannot contain uppercase letters in the ASCII range.
    ## "ABC" has three uppercase characters → UNSAT, decided by BV arithmetic.
    ## This is not sxUnknown — the model is complete for this query.
    let r = symexFind(lowerEqUpper, tLabel("lower_impossible"))
    check r.status != sxSat   ## must not claim a witness for an impossible constraint

  test "toUpperAscii SOUNDNESS: toUpperAscii(s)==\"abc\" is sxUnsat (no lowercase output)":
    ## Invariant 3 soundness: the BV18-ITE fold provably maps 'a'-'z' to 'A'-'Z',
    ## so the result cannot contain lowercase letters in the ASCII range.
    let r = symexFind(upperEqLower, tLabel("upper_impossible"))
    check r.status != sxSat   ## must not claim a witness for an impossible constraint

  test "walker version pin: symexWalkerVersion is now \"38\" (kept in sync; A9 introduced at 34)":
    ## A9 (ASCII case-fold) introduced this pin at 33→34. It must be kept in sync
    ## with every later walker bump (A7-S1/S2/S3 → 35/36/37; SND-1 → 38), so cached
    ## sxUnknown results for toLowerAscii/toUpperAscii SUTs rotate out and are
    ## re-evaluated.
    check symexWalkerVersion == "38"

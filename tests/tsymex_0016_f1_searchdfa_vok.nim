## RFC-0016 F1 hotfix (PRC-33 item 6b on main). `searchDfa` read the
## verifiers' `vok` only at the top of its state loop. A verifier that
## declined while the LAST state was being expanded was never seen:
## `startHere` skips a declined verifier as empty, so the loop ended with
## `ok=true` and a wrong language. For `skNoOcc` that language rejected
## subjects with no occurrence (`x`), and `find(...) == -1` read it.
##
## The fix reads `vok` once more after the loop. A search language that is
## built must agree with native `std/re` on every subject of the corpus; one
## that declines (`ok=false`) is sound.
import std/[unittest, strutils, re]
import ./s8bt_harness/member
import nelli/symex
from ./s8cu_helpers import pinFind
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select

const inherent = "(?:a(*SKIP:x))+z|a+c(*SKIP)z|(*MARK:y)(?:b(*SKIP:y))+d|b*e"

const corpus = ["", "x", "e", "a", "ac", "be", "z", "az", "acz", "bd",
                "bbd", "bbe", "xa", "ex", "aaz", "ab"]

proc noOccX(s: string) =
  # Natively reachable: `x` holds no occurrence.
  if s.len == 1 and s[0] == 'x' and
     s.find(re"(?:a(*SKIP:x))+z|a+c(*SKIP)z|(*MARK:y)(?:b(*SKIP:y))+d|b*e") == -1:
    symexTarget("f1_noocc_x")

proc noOccTwo(s: string) =
  # Natively reachable: `xx` holds no occurrence.
  if s.len == 2 and s[0] == 'x' and s[1] == 'x' and
     s.find(re"(?:a(*SKIP:x))+z|a+c(*SKIP)z|(*MARK:y)(?:b(*SKIP:y))+d|b*e") == -1:
    symexTarget("f1_noocc_xx")

proc noContainsX(s: string) =
  if s.len == 1 and s[0] == 'x' and
     not s.contains(re"(?:a(*SKIP:x))+z|a+c(*SKIP)z|(*MARK:y)(?:b(*SKIP:y))+d|b*e"):
    symexTarget("f1_nocontains_x")

suite "RFC-0016 F1: searchDfa sees a verifier declining on its last state":
  test "the walker's version floor (F1)":
    check parseInt(symexWalkerVersion) >= 401

  test "native: the corpus' occurrences":
    let rx = re(inherent)
    check "x".find(rx) == -1
    check "xx".find(rx) == -1
    check "e".find(rx) == 0

  test "skNoOcc: built only when it agrees with native std/re":
    let a = buildNfa(parsePcre(inherent))
    check a.ok
    let lang = searchLangV(a, "f1_inherent", skNoOcc, pcStart)
    checkpoint "ok=" & $lang.ok & " why=" & lang.why
    # A declined search names why.
    check lang.ok or lang.why.len > 0
    if lang.ok:
      let rx = re(inherent)
      for s in corpus:
        let native = s.find(rx) == -1
        checkpoint "subject " & s.escape & " native noOcc=" & $native
        check member(lang.re, toSyms(s)) == native

  test "walker: find(...) == -1 on a symbolic one-byte subject `x`":
    let r = pinFind(noOccX, tLabel("f1_noocc_x"))
    echo "  walker: ", r.status
    check r.status != sxUnsat

  test "walker: find(...) == -1 on a symbolic two-byte subject `xx`":
    let r = pinFind(noOccTwo, tLabel("f1_noocc_xx"))
    echo "  walker: ", r.status
    check r.status != sxUnsat

  test "walker: not contains on a symbolic one-byte subject `x`":
    let r = pinFind(noContainsX, tLabel("f1_nocontains_x"))
    echo "  walker: ", r.status
    check r.status != sxUnsat

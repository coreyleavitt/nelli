## Phase 15 — Code-Review finding CR-10: regex {n,m} repetition with counts
## ≥ 2^32 silently truncates to cuint, producing wrong regex bounds.
##
## `parseInt` returns int64 on 64-bit; `cuint` is 32-bit. Values ≥ 2^32 were
## truncated silently: `{4294967296,4294967297}` → cuint wraps to `{0,1}` →
## Z3 regex loop(atom, 0, 1) instead of the correct huge counts — potential
## false UNSAT/SAT.
##
## RED state: `parseNimRegexToZ3Regex(r"\d{4294967296,4294967297}")` returns
## `isOk == true` (silently truncated to loop(digit, 0, 1)).
##
## GREEN state: returns `isOk == false` with an "unsupported" / "seUnsupportedRegex"
## message — honest classification, not a wrong verdict.
##
## Also tests that any value > high(cuint) is rejected. RFC-0005 S8ay: the
## real bound is PCRE's 65535 (a larger count is a compile error, so
## `re` raises RegexError); the high(cuint) pin is replaced accordingly.
import std/[unittest, strutils]
import z3/context
import nelli/smt/regex_parser

suite "symex Phase 15 CR-10 — regex {n,m} overflow guard":
  let ctx = newContext()
  discard ctx

  test "CR-10: lo > 2^32-1 is rejected as unsupported":
    ## The smallest truncating lo value: 2^32 = 4294967296.
    let r = parseNimRegexToZ3Regex(r"\d{4294967296,4294967297}")
    check (not r.isOk)
    check "seUnsupportedRegex" in r.error or "exceeds" in r.error or "unsupported" in r.error

  test "CR-10: hi > 2^32-1 is rejected as unsupported (lo fine, hi overflows)":
    ## lo=1 (safe), hi=4294967296 (= 2^32, truncates to 0).
    let r = parseNimRegexToZ3Regex(r"\d{1,4294967296}")
    check (not r.isOk)
    check "seUnsupportedRegex" in r.error or "exceeds" in r.error or "unsupported" in r.error

  test "CR-10: the bound is PCRE's 65535, not high(cuint)":
    ## RFC-0005 S8ay: this pinned `\d{1,4294967295}` (high(cuint)) as
    ## accepted, but PCRE rejects every count above 65535 ("number too big
    ## in {} quantifier"), so `re` raises RegexError for it. 65535 is the
    ## largest count PCRE accepts.
    let big = parseNimRegexToZ3Regex(r"\d{1,4294967295}")
    check (not big.isOk)
    check "number too big" in big.error
    check parseNimRegexToZ3Regex(r"\d{1,65535}").isOk
    let over = parseNimRegexToZ3Regex(r"\d{1,65536}")
    check (not over.isOk)
    check "number too big" in over.error

  test "CR-10: normal small repetition still works":
    let r = parseNimRegexToZ3Regex(r"\d{2,5}")
    check r.isOk

  test "CR-10: {n,} (open-ended) with overflowing n is rejected":
    let r = parseNimRegexToZ3Regex(r"\d{4294967296,}")
    check (not r.isOk)
    check "seUnsupportedRegex" in r.error or "exceeds" in r.error or "unsupported" in r.error

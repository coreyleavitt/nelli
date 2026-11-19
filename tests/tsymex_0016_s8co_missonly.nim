## RFC-0016 S8co (PRC-33 item 10) -- a `contains` / `startsWith` call that
## makes one attempt (an anchored pattern, or `startsWith`'s anchored call)
## and stops at one of PCRE's own limits only where it misses. std/re reads
## both as `false`, so past `limitReach`'s safe length the call is still read
## exactly as long as the attempt's runs that end in a match stay under the
## limits (`LimitReach.missSafe`: their calls and their depth, and on the
## interpreter, whose stack ends in a SIGSEGV, the depth of every run).
## `find`, `match`, `replace` and an unanchored `contains` keep the limit
## reading, each compared with native PCRE.
import std/[unittest, re, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
from ./s8cu_helpers import named, show

template verdict(fn: typed; lbl: string): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    r

# ---- the walker ---------------------------------------------------------------

proc swLen(s: string) =
  if s.len == 31 and s[30] == 'c' and not s.startsWith(re"(a|a)*b|c"):
    symexTarget("sw_len")

proc ctLen(s: string) =
  if s.len == 31 and s[30] == 'c' and not s.contains(re"^(?:(a|a)*b|c)"):
    symexTarget("ct_len")

proc swRefute(s: string) =
  if s.len == 40 and s[0] == 'b' and not s.startsWith(re"(a|a)*b|c"):
    symexTarget("sw_refute")

proc ctRefute(s: string) =
  if s.len == 40 and s[0] == 'c' and not s.contains(re"^(?:(a|a)*b|c)"):
    symexTarget("ct_refute")

proc swNever(s: string) =
  # Past the plain safe length (its failures grow as n^6): the matching runs
  # cost the same at every length, so no site is recorded.
  if s.len == 100 and s[0] == 'b' and not s.startsWith(re"a*a*a*a*a*a*b"):
    symexTarget("sw_never")

proc findKeeps(s: string) =
  # find returns PCRE_ERROR_MATCHLIMIT (-8) on a^30 c, not -1.
  if s.len == 31 and s[30] == 'c' and s.find(re"^(?:(a|a)*b|c)") == -1:
    symexTarget("find_keeps")

proc unanchoredKeeps(s: string) =
  # The first attempt of a^38 x b stops at the limit: false, though b matches.
  if s.len == 40 and s[39] == 'b' and not s.contains(re"(a|a)*b|c"):
    symexTarget("unanchored_keeps")

suite "S8co item 10: a single attempt that stops only on a miss":
  test "walker floor":
    check parseInt(symexWalkerVersion) >= 419

  test "native":
    symexCaptureBegin()
    swLen('a'.repeat(30) & "c")
    ctLen('a'.repeat(30) & "c")
    swRefute("b" & 'a'.repeat(39))
    ctRefute("c" & 'a'.repeat(39))
    findKeeps('a'.repeat(30) & "c")
    swNever("b" & 'a'.repeat(99))
    unanchoredKeeps('a'.repeat(38) & "xb")
    let hits = symexCaptureEnd()
    check "sw_len" in hits
    check "ct_len" in hits
    check "sw_refute" notin hits
    check "ct_refute" notin hits
    check "find_keeps" notin hits
    check "sw_never" notin hits
    check "unanchored_keeps" in hits
    check find('a'.repeat(30) & "c", re"^(?:(a|a)*b|c)") == -8

  test "past the safe length, startsWith's miss is read: sxSat":
    let r = verdict(swLen, "sw_len")
    check r.status == sxSat
    if r.status == sxSat:
      let s = r.witness[0]
      check s.len == 31 and not s.startsWith(re"(a|a)*b|c")

  test "an anchored pattern's contains: sxSat":
    let r = verdict(ctLen, "ct_len")
    check r.status == sxSat
    if r.status == sxSat:
      check not r.witness[0].contains(re"^(?:(a|a)*b|c)")

  test "a refutation past the safe length stands: sxUnsat":
    check verdict(swRefute, "sw_refute").status == sxUnsat
    check verdict(ctRefute, "ct_refute").status == sxUnsat

  test "past every bound, the length proved: sxUnsat":
    check limitReach(parsePcre("a*a*a*a*a*a*b", false)).safe < 100
    check verdict(swNever, "sw_never").status == sxUnsat

  test "find keeps the limit reading: never sxSat":
    let r = verdict(findKeeps, "find_keeps")
    check r.status == sxUnknown
    check r.errors.named(beSolverUndef)

  test "an unanchored contains keeps it: never sxUnsat":
    let r = verdict(unanchoredKeeps, "unanchored_keeps")
    check r.status != sxUnsat
    if r.status == sxSat:
      check not r.witness[0].contains(re"(a|a)*b|c")

# ---- the bound, against native PCRE ---------------------------------------------

type Gen = proc (n: int): string {.nimcall.}

proc aThenB(n: int): string = 'a'.repeat(max(n - 1, 0)) & "b"
proc aThenC(n: int): string = 'a'.repeat(max(n - 1, 0)) & "c"
proc abThenC(n: int): string = "ab".repeat(max(n - 1, 0) div 2) & "c"

const corpus: seq[(string, Gen)] = @[
  ("(a|a)*b|c", aThenB), ("(a|a)*c|a*b", aThenB), ("(a|a)*c|(a|b)*b", aThenB),
  ("(a|b)*c", aThenC), ("(?:a|b)*c", abThenC), ("(a)*c", aThenC),
  ("(?:ab|a)+c", abThenC), ("(a|aa)*b|c", aThenB), ("(a*)*b", aThenB),
  ("(a+)+c|b", aThenC), ("(?:a|a)*?b", aThenB), ("a*a*a*b", aThenB),
  ("(?:a|b)*?c", abThenC), ("(a|b){2,}c", abThenC), ("a*(a|a)*c|b", aThenC)]

suite "S8co item 10: LimitReach.missSafe against native PCRE":
  test "a subject that matches, within missSafe, is a match natively":
    var tried = 0
    for (p, gen) in corpus:
      let r = limitReach(parsePcre(p, false))
      let rx = re(p)
      let top = (if r.missNever: 3000 else: min(r.missSafe, 3000))
      checkpoint p & " safe " & $r.safe & " missSafe " & $r.missSafe &
        " missNever " & $r.missNever
      check r.missNever or r.missSafe >= r.safe
      var lens = @[top, top - 1, top div 2, r.safe + 1, r.safe + 8]
      for n in lens:
        if n < 1 or n > top: continue
        let s = gen(n)
        check s.len <= n
        let got = matchLen(s, rx)
        checkpoint p & " at " & $s.len & ": " & $got
        check got >= 0
        inc tried
    check tried >= 40

  test "the bound is above the plain one where only misses grow":
    for p in ["(a|a)*b|c", "(a|aa)*b|c", "(?:a|a)*b|c"]:
      let r = limitReach(parsePcre(p, false))
      checkpoint p & " safe " & $r.safe & " missSafe " & $r.missSafe
      check not r.never and not r.missNever
      check r.missSafe > r.safe + 50

  test "every length, where only misses grow":
    for p in ["a*a*a*b", "a*a*a*a*a*a*b", "^a*a*b", "[ab]*a*c", "a*a*(?:b|c)"]:
      let r = limitReach(parsePcre(p, false))
      checkpoint p & " safe " & $r.safe & " missSafe " & $r.missSafe
      check not r.never
      check r.missNever and r.missNeverJit

  test "not where a match costs more with the length":
    # `(a|a)*c|a*b` matches a^n b only after its first branch fails, at
    # 2^n calls; `.*b` backtracks over the tail it took.
    for p in ["(a|a)*c|a*b", ".*b", "(a|b)*c", "(?:ab|a)+c"]:
      let r = limitReach(parsePcre(p, false))
      checkpoint p & " safe " & $r.safe & " missSafe " & $r.missSafe
      check not r.missNever and not r.missNeverJit
    check limitReach(parsePcre("(a|a)*c|a*b", false)).missSafe < 40

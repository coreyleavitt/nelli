## RFC-0016 S8co (PRC-33 item 6b) -- the SKIP:NAME count across attempts.
## pcre_exec.c 8.37 keeps `ignore_skip_arg` (the run number of the SKIP:NAME
## without its MARK that re-ran an attempt) into the next attempt when the
## attempt ends by a SKIP's jump past its start; the next attempt's
## `OP_SKIP_ARG` compares its own count with it (`skip_arg_count <=
## ignore_skip_arg`: no RMATCH). Past `argCap` the automata hold the count
## saturated. Two subjects whose counts differ only past any bound are told
## apart by PCRE: a SKIP:NAME with its MARK that the kept count covers is a
## no-op, one it does not cover jumps to the MARK; the language of the
## subjects where the jump happens compares the two blocks' lengths, which
## no finite automaton decides (`{a^n c b^m e : m <= n}`), so the decline
## is inherent. Within an attempt the saturated count decides nothing: a
## re-run ignores exactly its chain, and every SKIP:NAME run after it is
## past the count; the saturated equality must not read as covered. The
## decline must reach the search: a verifier that declines while the search
## automaton's last state is expanded used to leave an empty `skNoOcc`
## language (`find(...) == -1` a false `sxUnsat`), and an attempt that runs
## a SKIP:NAME per repeat iteration grew its agenda with the subject, so its
## automaton reached neither a decision nor its cap within the bound.
import std/[unittest, strutils, re]
import ./s8bt_harness/[member, jit_corpus, limit_oracle]
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
from ./s8cu_helpers import nativeRun, hitsTarget
from ./s8cu_helpers import pinFind

const
  # Attempt 1 runs n SKIP:x (no MARK:x), re-runs with the count n, then
  # jumps past c keeping it; attempt 2 runs m SKIP:y under MARK:y: the
  # (n+1)-th is live and jumps to the MARK (the attempt's start: a bump),
  # else the repeat backtracks and `b*e` matches at the block.
  inherent = "(?:a(*SKIP:x))+z|a+c(*SKIP)z|(*MARK:y)(?:b(*SKIP:y))+d|b*e"
  # Within one attempt: the barrier's re-run leaves a saturated count; the
  # MARK'd SKIP:y after it runs past the count (live: a jump to the MARK),
  # never under it. A MARK past the attempt's start keeps the saturated
  # count for the next attempt (the inherent decline, `staleWhy`); one at
  # the start is a bump that resets it, so that language builds.
  within = [("(?:a(*SKIP:x))+c|a(*MARK:y)a+(*SKIP:y)d|a*e", false),
            ("(?:a(*SKIP:x))+c|(*MARK:y)a+(*SKIP:y)d|a*e", true),
            ("(?:a(*SKIP:x))+c|aa(*MARK:y)a+(*SKIP:y)d|.*e", false)]

proc inherentNoOcc(s: string) =
  if s.len == 1 and
     s.find(re"(?:a(*SKIP:x))+z|a+c(*SKIP)z|(*MARK:y)(?:b(*SKIP:y))+d|b*e") == -1:
    symexTarget("co_sat_noocc")

proc natFind(p, s: string): int =
  let r = initLimitOracle(p).execInterp(s, 0, false)
  if r[0] == 1: r[1] else: r[0]

proc modelFind(n: Nfa; s: string): int =
  let got = pcreExec(n, s, 0, false)
  if got[0] == 1: got[1] else: got[0]

suite "S8co item 6b: the kept SKIP:NAME count past argCap":
  test "native: counts past any bound are told apart":
    var shown = 0
    for k in [argCap, argCap + 1, 12, 20]:
      let under = "a".repeat(k) & "c" & "b".repeat(k + 1) & "e"   # m > n
      let over = "a".repeat(k + 1) & "c" & "b".repeat(k + 1) & "e"  # m <= n
      let fu = natFind(inherent, under)
      let fo = natFind(inherent, over)
      echo "  n=", k, " m=", k + 1, " native ", fu, "; n=", k + 1, " native ",
        fo
      check fu == under.len - 1      # the jump: only `e` matches
      check fo == k + 2              # `b*e` at the block
      inc shown
    check shown == 4

  test "the concrete call reads them; the automata decline the pattern":
    let n = buildNfa(parsePcre(inherent), limitRoom = 0, concrete = true)
    check n.ok and n.countArgs
    var bad: seq[string]
    for k in 0 .. 12:
      for m in 0 .. 12:
        let s = "a".repeat(k) & "c" & "b".repeat(m) & "e"
        if modelFind(n, s) != natFind(inherent, s):
          bad.add "n=" & $k & " m=" & $m & ": model " & $modelFind(n, s) &
                  " native " & $natFind(inherent, s)
    checkpoint bad.join("\n")
    check bad.len == 0
    let a = buildNfa(parsePcre(inherent))
    check a.ok
    let lang = searchLangV(a, "co_sat_inherent", skNoOcc, pcStart)
    if lang.ok:
      # The language that stood for the decline: `x` has no occurrence.
      check natFind(inherent, "x") == -1
      check member(lang.re, toSyms("x"))
    check not lang.ok
    echo "  declined: ", lang.why
    check staleWhy in lang.why
    # The walker: `x` is a one-byte subject with no occurrence, so a search
    # for one is never unsatisfiable.
    check "x".find(re"(?:a(*SKIP:x))+z|a+c(*SKIP)z|(*MARK:y)(?:b(*SKIP:y))+d|b*e") == -1
    let r = symexFind(inherentNoOcc, tLabel("co_sat_noocc"))
    echo "  walker: ", r.status
    check r.status != sxUnsat
    # and natively `x` reaches the target, so unsat would be a wrong verdict
    check nativeRun(inherentNoOcc("x")).hitsTarget(tLabel("co_sat_noocc"))

  test "within an attempt, the saturated count never reads as covered":
    var bad: seq[string]
    var runs, built = 0
    for (p, builds) in within:
      let n = buildNfa(parsePcre(p))
      check n.ok and n.countArgs
      let nc = buildNfa(parsePcre(p), limitRoom = 0, concrete = true)
      for pc in startClasses(n):
        let pre = prefixOf(pc)
        let noOcc = searchLangV(n, "co_sat:" & p, skNoOcc, pc)
        let first = searchLangV(n, "co_sat:" & p, skFirst, pc)
        if not (noOcc.ok and first.ok):
          if builds or not (staleWhy in noOcc.why and staleWhy in first.why):
            bad.add "declined " & p & " " & $pc & ": " & noOcc.why & first.why
          continue
        if not builds:
          bad.add "built " & p & " " & $pc & " (a kept count past argCap)"
          continue
        inc built
        for k in 0 .. 12:
          for tail in ["e", "d", "ce", "ae", ""]:
            let u = "a".repeat(k) & tail
            let subj = pre & u
            inc runs
            let nat = natFind(p, subj)
            let nat2 = (if nat >= 0: nat - pre.len else: nat)
            let (rc, a0, _) = pcreExec(nc, subj, pre.len, false)
            let q = (if rc == 1: a0 - pre.len else: -1)
            if q != nat2:
              bad.add "concrete " & p & " " & escape(u) & ": " & $q &
                      " native " & $nat2
            if member(noOcc.re, toSyms(u)) != (nat2 == -1):
              bad.add "skNoOcc " & p & " " & $pc & " " & escape(u) &
                      " native " & $nat2
            for j in 0 .. u.len:
              let w = toSyms(u[0 ..< j]) & @[markSym] & toSyms(u[j .. ^1])
              if member(first.re, w) != (nat2 == j):
                bad.add "skFirst " & p & " " & $pc & " " & escape(u) & " " &
                        $j & " native " & $nat2
            if bad.len > 30: break
    echo "  ", built, " languages, ", runs, " subjects, ", bad.len, " bad"
    checkpoint bad[0 ..< min(bad.len, 30)].join("\n")
    check built > 0
    check bad.len == 0

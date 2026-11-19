## RFC-0016 S8co (PRC-33 item 4, the automata): the shared run of
## `tsymex_0016_s8co_skipworld_a` and `_b`. Each search language of a listed
## limited pattern is compared with native PCRE's interpreter and the
## concrete call, word by word.
##
## The bound. The full product (11 patterns x limits {2..13} x both limits x
## both start classes, words up to five bytes) took about 1150 s. A run keeps,
## per pattern, only the limits whose native outcome over the corpus differs
## from the next lower kept limit's (the crossings), plus one language past
## the guess budget and one past `argCap`; words go up to four bytes, and the
## regression subjects past that are listed by name (`extra`).
import std/[strutils, monotimes, times, algorithm]
import ./s8bt_harness/[member, jit_corpus, limit_oracle]
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select

const
  patterns* = [
    "(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c",
    "a(*SKIP:X)b|(*MARK:X)a|c",
    "a(*SKIP:N)c|ab(*SKIP)d|b",
    "(?:a(*SKIP:N)c|ab(*SKIP)d)+|b",
    "a(*SKIP:N)(*SKIP:M)c|ab(*SKIP)d|.",
    "(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+",
    "a(?:(*SKIP:N)c|(*SKIP:M)d)|ab(*SKIP)q|b+",
    "(?:x(*SKIP:N)y|xa(*SKIP)b|(*MARK:N)a)+",
    "a+(*SKIP:N)c|ab(*SKIP)q|ab",
    "(a(*SKIP:N)c|ab(*SKIP)q|b)+c?",
    # a SKIP:NAME in a lower alternative whose continuation dies while a
    # higher thread still runs SKIP:NAMEs: the first guess is refuted
    "(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d"]

type
  Lang* = tuple[pat: int; kind: char; lims: seq[int]]
    ## `pat` is 1-based, `kind` is 'M' (LIMIT_MATCH) or 'R'
    ## (LIMIT_RECURSION).
  WorldRun* = object
    bad*, declined*, budgeted*, inherent*: seq[string]
    runs*, built*, errs*: int
    slowest*: seq[(int, string)]  ## (ms, language), the language's build and words

proc natExec(p, s: string; st: int): int =
  let r = initLimitOracle(p).execInterp(s, st, false)
  if r[0] == 1: r[1] - st else: r[0]

proc runLangs*(langs: openArray[Lang]; extra: openArray[string]): WorldRun =
  ## Every listed language against native and the concrete call over the
  ## words up to four bytes and `extra`.
  var subjects = words("abqxcd", 4)
  for e in extra: subjects.add e
  worldPeak = 0
  agendaPeak = 0
  for l in langs:
    let p = patterns[l.pat - 1]
    for lim in l.lims:
      let lk = (if l.kind == 'M': "LIMIT_MATCH" else: "LIMIT_RECURSION")
      let q = "(*" & lk & "=" & $lim & ")" & p
      let t0 = getMonoTime()
      let pr = parsePcre(q)
      if pr.status != psOk:
        result.declined.add q & ": does not parse"
        continue
      let n = buildNfa(pr, limitRoom = 0)
      if not n.ok:
        result.declined.add q & ": " & n.why
        continue
      if limitEffect(n)[0] == leUnknown: continue
      let nc = buildNfa(pr, limitRoom = 0, concrete = true)
      if not nc.ok:
        result.bad.add "concrete call declines " & q & ": " & nc.why
        continue
      for pc in [pcStart, pcOther]:
        let pre = prefixOf(pc)
        let noOcc = searchLangV(n, "co_world:" & q, skNoOcc, pc)
        let first = searchLangV(n, "co_world:" & q, skFirst, pc)
        if not (noOcc.ok and first.ok):
          let why = noOcc.why & first.why
          # The documented budgets: the guessing attempt's states
          # (`maxGuessStates`), its worlds (`maxWorlds`) and the automata's
          # size caps. A count past `argCap` is the inherent decline
          # (`staleWhy`, item 6b).
          if guessBudgetWhy in why or worldBudgetWhy in why or
             agendaBudgetWhy in why or "size cap" in why:
            result.budgeted.add q & " " & $pc & ": " & why
          elif staleWhy in why:
            result.inherent.add q & " " & $pc & ": " & why
          else:
            result.declined.add q & " " & $pc & ": " & why
          continue
        inc result.built
        for u in subjects:
          let subj = pre & u
          inc result.runs
          let nat = natExec(q, subj, pre.len)
          let (rc, a0, _) = pcreExec(nc, subj, pre.len, false)
          let got = (if rc == 1: a0 - pre.len else: rc)
          if got != nat:
            result.bad.add "concrete " & q & " " & escape(u) & ": " & $got &
                           " native " & $nat
          if nat < -1: inc result.errs
          if member(noOcc.re, toSyms(u)) != (nat != 1 and nat < 0):
            result.bad.add "skNoOcc " & q & " " & $pc & " " & escape(u) &
                           " native " & $nat
          for j in 0 .. u.len:
            let w = toSyms(u[0 ..< j]) & @[markSym] & toSyms(u[j .. ^1])
            if member(first.re, w) != (nat == j):
              result.bad.add "skFirst " & q & " " & $pc & " " & escape(u) &
                             " " & $j & " native " & $nat
          if result.bad.len > 30: return
      result.slowest.add ((getMonoTime() - t0).inMilliseconds.int, q)

proc report*(r: WorldRun): string =
  result = "  " & $r.built & " languages, " & $r.runs & " subjects, " &
    $r.errs & " native limit errors, " & $r.declined.len & " declined, " &
    $r.budgeted.len & " past a budget, " & $r.inherent.len &
    " past argCap, " & $r.bad.len & " bad, " & $worldPeak &
    " worlds at the peak, " & $agendaPeak & " items in the longest agenda"
  let slow = r.slowest.sorted(Descending)
  for t in slow[0 ..< min(slow.len, 8)]:
    result.add "\n  " & $t[0] & " ms " & t[1]
  for d in r.declined[0 ..< min(r.declined.len, 12)]:
    result.add "\n  declined " & d
  for d in r.budgeted: result.add "\n  budget " & d
  for d in r.inherent: result.add "\n  inherent " & d

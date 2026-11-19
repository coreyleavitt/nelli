## RFC-0016 S8co (PRC-33 item 4, the automata) -- a kept `ignore_skip_arg`
## under a limit, in the languages; patterns 1-5 (`_b` holds 6-11, the
## shared run is `s8co_skipworld.nim`). An attempt that starts with
## pcre_exec.c's `ignore_skip_arg` set skips the RMATCH of each SKIP:NAME it
## covers: one `match()` call fewer and its continuation one frame
## shallower. Which ones it covers is their run number, final only at the
## agenda's front. A concrete call guesses and re-runs (`SkipGuess`); the
## automata used to decline the pattern (`costStaleWhy`). Now a DFA state is
## a set of worlds, one per assignment of the guesses still open; a guess
## refuted at the front kills its worlds, and the outcome is the world of the
## guesses the concrete call would make (every open guess covered). Each
## search language is compared with native PCRE's interpreter and the
## concrete call, word by word, and the walker decides a symbolic call it
## used to decline.
import std/[unittest, re, strutils]
import ./s8co_skipworld
import nelli/smt/canonicalize
import nelli/symex
from ./s8cu_helpers import pinFind

const langs: seq[Lang] = @[
  (1, 'M', @[2, 5, 6, 8]), (1, 'R', @[2, 3, 4, 5, 6]),
  (2, 'M', @[2, 3, 4, 5]), (2, 'R', @[2, 3]),
  (3, 'M', @[2, 3, 4]), (3, 'R', @[2, 3]),
  (4, 'M', @[2, 5, 8]), (4, 'R', @[2, 3, 4, 5, 6, 8]),
  (5, 'M', @[2, 4]), (5, 'R', @[2, 4])]

proc worldSym(s: string) =
  if s.len == 4 and
     s.find(re"(*LIMIT_MATCH=5)(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c") == -1:
    symexTarget("co_world")

proc worldSymNo(s: string) =
  if s == "abab" and
     s.find(re"(*LIMIT_MATCH=5)(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c") != -1:
    symexTarget("co_world_no")

suite "S8co item 4: the automata read a kept ignore_skip_arg under a limit (1-5)":
  test "search languages against native and the concrete call":
    let r = runLangs(langs, [])
    echo r.report
    checkpoint r.bad[0 ..< min(r.bad.len, 30)].join("\n")
    check r.declined.len == 0
    check r.budgeted.len == 0
    check r.inherent.len == 0
    # At 7deb0b0b (before the worlds) 34 of these 66 languages built;
    # the rest declined with `costStaleWhy`. Now every one builds.
    check r.built == 66
    check r.bad.len == 0
    check r.errs > 0

  test "the walker decides a symbolic call":
    check parseInt(symexWalkerVersion) >= 397
    check "abab".find(re"(*LIMIT_MATCH=5)(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c") == -1
    check pinFind(worldSym, tLabel("co_world")).status == sxSat
    check pinFind(worldSymNo, tLabel("co_world_no")).status == sxUnsat

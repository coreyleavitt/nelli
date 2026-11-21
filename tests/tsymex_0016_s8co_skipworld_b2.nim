## RFC-0016 S8co (PRC-33 item 4, the automata) -- a kept `ignore_skip_arg`
## under a limit, in the languages; patterns 6-11 (`_a` holds 1-5 and states
## the model, the shared run is `s8co_skipworld.nim`). The worlds have a live
## producer here: `a(?:(*SKIP:N)c|(*SKIP:M)d)|...` guesses M while N's
## continuation holds the front, and `a+(*SKIP:N)c|...` runs a SKIP:N per
## repeat iteration, each guess closed once the next run moves its number
## past the count (`worldPeak`). The re-run regression subjects stand by
## name: `(*LIMIT_MATCH=8)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?` matches `aca` at 0
## with eight calls on the re-run, where the first run's agenda held nine
## before the match (the re-run slack in `capCosts`); and under
## `(*LIMIT_RECURSION=6)` `(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+` finds no
## match in `acab`, P11 under `=7` matches `acaa` at 0 and stops on `abxa`,
## each read only when a SKIP:NAME terminal a decided item cut stays in the
## agenda for the re-run's depths (`keepsCut`). `acaca` is P10 M10's.
## P9 under `=2` is the agenda's bound: its exit's calls pass the limit by
## two frames where one SKIP:N frame is all a re-run could lift, so the
## item decides and `capCosts` cuts after it (`Item.sk`); kept, one such
## item and one barrier per `a` grew the agenda with the subject, and no
## build finished. With the cut gone the language runs past `maxAgenda`
## and declines (`agendaBudgetWhy`), read here as past a budget.
##
## Part 2 of 3 of what was `tsymex_0016_s8co_skipworld_b` (patterns 6-11 in one
## run: 58 s on c with its compile, 194 s on the Windows leg, near its 240 s
## watchdog): patterns 9, 10 here. Per-part counts are below; the whole run's
## were 90 languages built, 2 past a budget (P11 R8), 2 past `argCap` (P9 R4).
import std/[unittest, strutils]
import ./s8co_skipworld
import nelli/smt/pcre_select

const langs: seq[Lang] = @[
  # P9 R2: the recursion cut's producer (above). P9 R4: past `argCap` (`a+(*SKIP:N)c`
  # runs one SKIP:N per `a` under LIMIT_RECURSION, which a single-byte repeat
  # never deepens).
  (9, 'M', @[2, 4]), (9, 'R', @[2, 4]),
  (10, 'M', @[2, 5, 7, 8, 9, 10]), (10, 'R', @[2, 3, 4, 5])]

suite "S8co item 4: the automata read a kept ignore_skip_arg under a limit (P9, P10)":
  test "search languages against native and the concrete call":
    let r = runLangs(langs, ["acaca"])
    echo r.report
    checkpoint r.bad[0 ..< min(r.bad.len, 30)].join("\n")
    check r.declined.len == 0
    check r.budgeted.len == 0
    check r.inherent.len == 2   # P9 R4, both start classes
    check r.built == 26   # the three parts' 46 + 26 + 18 are the whole run's 90
    check r.bad.len == 0
    check r.errs > 0

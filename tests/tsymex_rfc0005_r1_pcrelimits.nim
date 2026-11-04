## RFC-0005 review round 1, R1-03 / R1-05 / R1-22 (and RFC-0016 CRH-04):
## PCRE's compile-time limits.
##
## PCRE 8.45 (LINK_SIZE 2, the build Nim's `re` binds) rejects a pattern at
## `re(...)` when
##   * a group opens past a nesting depth of 250 ("parentheses are too
##     deeply nested", at the offset just past the 251st opener; an
##     option-only `(?i)` and an empty `(?!)` not followed by a quantifier
##     do not count), or
##   * its compiled code passes 65536 code units ("regular expression is
##     too large"), or the compile workspace overruns ("regular expression
##     is too complicated").
## The reader modelled none of them: 300 nested groups gave `sxSat "a"`,
## `(?:[a-z]){1700}|b` gave `sxSat "b"`, and a handler for the `RegexError`
## native always raises was a clean `sxUnsat` (R1-03). Counted groups were
## replicated before any size cap (R1-05: 200^3 nesting took 34 s and 5.7
## GB), and the reader's recursion and `codeSize` were unbounded (R1-22;
## CRH-04: a literal of 2600 nested groups).
##
## Now the nesting limit is a rejection with Nim's exact message, and a
## pattern whose compiled size or workspace the reader cannot show to be
## inside PCRE's limits is undecided (`psUnknown`, `seUnsupportedRegex`).
## Every row is checked against the real `re()` on this build.
import std/[unittest, strutils, re, times, macros, sugar]
import nelli
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import ./s8cu_helpers

proc nest(opener: string; n: int; body = "a"): string =
  repeat(opener, n) & body & repeat(')', n)

let
  Nest250 = nest("(", 250)
  Nest300 = nest("(", 300)

proc nativeRaises(p: string): (bool, string) =
  try:
    discard re(p)
    (false, "")
  except RegexError as e:
    (true, e.msg)

proc agrees(p: string; bad: var seq[string]) =
  ## The reader never contradicts `re()`: an accepted pattern is never
  ## `psRejected`, a rejected one never `psOk` / `psUnmodelled`, and a
  ## rejection carries Nim's exact message.
  let pr = parsePcre(p)
  let (raises, msg) = nativeRaises(p)
  let where = escape(if p.len > 60: p[0 ..< 60] & "..." else: p) & " (len " &
              $p.len & ") -> " & $pr.status & " " & pr.reason
  if raises:
    if pr.status in {psOk, psUnmodelled}:
      bad.add where & ": re() raises " & escape(msg.splitLines()[0])
    elif pr.status == psRejected and pr.errMsg != msg:
      bad.add where & ": " & escape(pr.errMsg.splitLines()[0]) &
              " but re(): " & escape(msg.splitLines()[0])
  elif pr.status == psRejected:
    bad.add where & ": re() accepts it"

proc corpus(): seq[string] =
  result = @[
    nest("(", 250), nest("(", 251), nest("(?:", 251), nest("x(a|", 251, "b"),
    nest("(?=", 251, ""), nest("(?>", 251, ""), nest("(?i:", 251, ""),
    nest("(?-i:", 251, ""), nest("(?!", 251, ""), nest("(?!", 252, ""),
    repeat("(?:", 250) & "(?!)" & repeat(')', 250),
    repeat("(?:", 250) & "(?!)*" & repeat(')', 250),
    repeat("(?:", 250) & "(?!){2}" & repeat(')', 250),
    repeat("(?:", 250) & "(?!){2" & repeat(')', 250),
    repeat("(?:", 250) & "(?i)" & repeat(')', 250),
    repeat("(?:", 250) & "(?i)(?:a)" & repeat(')', 250),
    repeat("(?:", 250) & "(?#c)(?:a)" & repeat(')', 250),
    repeat("(?:", 250) & "(*MARK:x)(?:a)" & repeat(')', 250),
    repeat("(?:", 250) & "()" & repeat(')', 250),
    repeat('(', 251) & "[a", repeat('(', 250) & "[a", repeat('(', 251) & "a**",
    "a**" & repeat('(', 251), repeat('(', 251),
    "(?:a){8000}", "(?:a){9000}", "(?:a){0,8000}", "(?:a){7000,}",
    "(?:[a-z]){1700}", "(?:[a-z]){1600}", "(?:[a-z]){0,1700}",
    "(?:[a-z]){1700}|b",
    "(?:(?:(?:a|b){200}|c){200}|d){200}", "(?:(?:a|b){60000}|c){60000}",
    "(?:a{65535}){6000}", "(?:(?:a|b){100}|c){40}",
    repeat('x', 32764), repeat('x', 32765), repeat('x', 70000),
    repeat("[ab](?:", 110) & repeat(')', 110),
    repeat("[ab](?:", 111) & repeat(')', 111),
    repeat("[a](?:", 250) & repeat(')', 250),
    repeat("[ab]+(?:", 250) & repeat(')', 250),
    "(*UTF)(?i)" & repeat("[\\x{100}-\\x{17f}](?:", 250) & repeat(')', 250),
    "(*UTF)(?i)[\\x{0}-\\x{10ffff}]", "(*UTF)(?i)[\\x{100}-\\x{17f}]{2000}",
    "(*UTF)(?i)(?:[\\x{100}-\\x{17f}]){2000}",
    "(?:a(?=b)){5000}", "(?:(a)\\1){4000}", "(?:(*MARK:" & repeat('m', 200) &
      ")){300}",
    nest("(", 2600), repeat('(', 100_000)]

suite "R1-03 / R1-05 / R1-22: PCRE's compile limits":

  test "the reader agrees with re() on PCRE's limits":
    var bad: seq[string]
    for p in corpus(): agrees(p, bad)
    for b in bad: checkpoint b
    check bad.len == 0

  test "at each family's native limit, the reader never accepts more":
    # For each family (an item under a repeat form, or nested under N
    # groups), the largest count `re()` accepts (`hiN`) and the largest
    # the reader decides (`hiM`): every count from just below `hiM` to
    # just past `hiN` must agree, and the reader must keep most of the
    # range.
    let items = @["a", "\\d", "\\p{L}", "[ab]", "[^a]", "(a)", "(?:a|bc)",
      "a{2,5}", "[ab]{3}", "(?:x(?=y))", "(a)\\1", "(*MARK:mm)a", "\\Qab\\E",
      "(?i)[a-z]", "(?i:k)", "(*UTF)\\x{10000}", "(*UTF)(?i)[\\x{100}-\\x{17f}]",
      "(*UTF)(?i)k", "(*UTF)[\\x{100}-\\x{200}\\h]", "[\\p{L}\\p{N}]",
      "(*UCP)[[:alpha:]\\w]", "x*+", "(?>ab)", "\\b", "(?:a)*", "(?:ab)++",
      "[ab]{2,3}+", "\\d{2,3}?", "\\p{L}{2,}", "(?<nm>a)", "(a(*ACCEPT))",
      "(*COMMIT)a", "(?:a(*THEN)b|c)", "(*UTF)(?i)\\x{3a3}", "(*UTF)(?i)s",
      "(*UTF)[^\\x{100}]", "(*UTF)[\\H]", "(*UTF)\\H", "(*UTF)[[:^alpha:]]",
      "(*UTF)(?i)[\\x{0}-\\x{10ffff}]", "(*UTF)[\\x{100}\\x{100}\\x{100}]",
      "(*UTF)(?i)[k\\x{212a}]", "[[:alpha:][:^digit:]]", "(?i)abc", "\\N",
      "^a$", "\\z", "(?#c)a", "(*UTF).", "[\\x00-\\xff]", "(?=a){2}", "(?!a)?", "(?=a){2}+",
      "(?:[ab])", "(?:x[\\p{L}\\p{N}])", "(?:a|[ab])", "(*PRUNE:nm)a",
      "(*UTF)(?i)(?:\\x{3a3}|[k\\x{212a}])"]
    let forms = @[("(?:", "){N}"), ("(?:", "){0,N}"), ("(?:", "){N,}"),
                  ("(?:", "){1,N}"), ("(", "){N}"), ("", "{N}")]
    proc split(it: string): (string, string) =
      for opt in ["(*UTF)", "(*UCP)"]:
        if it.startsWith(opt): return (opt, it[opt.len .. ^1])
      ("", it)
    type Family = tuple[name: string; top: int; at: proc (n: int): string]
    var fams: seq[Family]
    for it in items:
      let (pre, body) = split(it)
      for f in forms:
        if f[0] == "" and not (body.len <= 4 and body[0] != '('): continue
        capture pre, body, f:
          fams.add (pre & f[0] & body & f[1], 65535,
                    proc (n: int): string = pre & f[0] & body &
                                            f[1].replace("N", $n))
      # The compile workspace: `it` before each of N nested groups. Not for
      # the caseless all-code-point class: 20 deep, PCRE 8.45's own
      # compile crashes the process (probed), where the reader declines
      # from 5 deep.
      if "10ffff" in it: continue
      capture pre, body:
        fams.add (pre & "(" & body & "(?:)^N", 250,
                  proc (n: int): string =
                    pre & repeat(body & "(?:", n) & repeat(')', n))
    var bad: seq[string]
    for fam in fams:
      proc nativeOk(n: int): bool = not nativeRaises(fam.at(n))[0]
      proc modelOk(n: int): bool =
        parsePcre(fam.at(n)).status in {psOk, psUnmodelled}
      if not nativeOk(1): continue
      var lo = 1
      var hi = fam.top
      if nativeOk(hi): lo = hi
      while lo < hi:
        let m = (lo + hi + 1) div 2
        if nativeOk(m): lo = m else: hi = m - 1
      let hiN = lo
      lo = 0
      hi = min(hiN + 1, fam.top)
      while lo < hi:
        let m = (lo + hi + 1) div 2
        if modelOk(m): lo = m else: hi = m - 1
      let hiM = lo
      for n in max(hiM - 3, 1) .. min(hiN + 3, fam.top + 1):
        agrees(fam.at(n), bad)
      checkpoint fam.name & ": native " & $hiN & ", reader " & $hiM
      # Two thirds: the loosest family, the caseless all-code-point class
      # (its fold ranges counted before PCRE merges them), keeps 69%.
      if hiM * 3 < hiN * 2:
        bad.add fam.name & ": the reader decides up to " & $hiM &
                " of native's " & $hiN
    for b in bad: checkpoint b
    check bad.len == 0

  test "the nesting limit is a rejection with Nim's message":
    let pr = parsePcre(Nest300)
    check pr.status == psRejected
    check pr.errMsg == nativeRaises(Nest300)[1]
    check parsePcre(Nest250).status == psOk
    # CRH-04: 2600 nested groups, and 100,000 open parentheses, stop at the
    # 251st (no host recursion past it).
    check parsePcre(nest("(", 2600)).status == psRejected
    check parsePcre(repeat('(', 100_000)).status == psRejected

  test "patterns inside the limits stay decided":
    check parsePcre("(?:a){8000}").status == psOk
    check parsePcre("(?:[a-z]){1500}").status == psOk
    check parsePcre(repeat('x', 32000)).status == psOk
    check parsePcre(repeat("[a](?:", 250) & repeat(')', 250)).status == psOk

  test "R1-05: a pattern past PCRE's size is refused before it is expanded":
    let t0 = epochTime()
    let pr = parsePcre("(?:(?:(?:a|b){200}|c){200}|d){200}")
    check pr.status == psUnknown
    check parsePcre("(?:(?:a|b){60000}|c){60000}").status == psUnknown
    check epochTime() - t0 < 1.0

  test "R1-05: accepted repeat shapes build within the cap quickly":
    for p in ["(?:a{65535}){6000}", "(?:(?:a|b){100}|c){40}",
              "(?:a){8000}", "(?:[a-z]){1500}"]:
      let pr = parsePcre(p)
      checkpoint p
      check pr.status == psOk
      if pr.status != psOk: continue
      let t0 = epochTime()
      discard buildNfa(pr)
      discard buildNfa(pr, limitRoom = 0, concrete = true)
      discard buildNfa(pr, limitRoom = pr.groups, boundOnly = true)
      checkpoint p & ": " & $(epochTime() - t0) & " s"
      check epochTime() - t0 < 5.0

macro nestProc(name: untyped; n: static int; handler: static bool): untyped =
  ## A routine over `re(<n nested groups around "a">)` as a literal (a
  ## `const` would reach the walker as a symbol, not a literal): `handler`
  ## hits in `except RegexError`, else on a match.
  let lit = newLit("(".repeat(n) & "a" & ")".repeat(n))
  if handler:
    result = quote do:
      proc `name`(s: string) =
        try:
          if s.match(re(`lit`)): discard
        except RegexError:
          symexTarget("hit")
  else:
    result = quote do:
      proc `name`(s: string) =
        try:
          if s.match(re(`lit`)): symexTarget("hit")
        except RegexError:
          discard

nestProc(nest300Handler, 300, true)
nestProc(nest300Match, 300, false)
nestProc(nest250Match, 250, false)
nestProc(nest2600Handler, 2600, true)

proc big1700Handler(s: string) =
  try:
    if s.match(re"(?:[a-z]){1700}"): discard
  except RegexError:
    symexTarget("hit")

proc big1700Alt(s: string) =
  try:
    if s.match(re"(?:[a-z]){1700}|b"): symexTarget("hit")
  except RegexError:
    discard

proc big1700Opt(s: string) =
  try:
    if s.match(re"(?:[a-z]){0,1700}"): symexTarget("hit")
  except RegexError:
    discard

suite "R1-03: the walker's verdicts on PCRE's limits":

  test "300 nested groups raise RegexError":
    check native(nest300Handler("a")) == "hit"
    decides(nest300Handler, sxSat)      # was a clean sxUnsat
    check native(nest300Match("a")) == "ran"
    decides(nest300Match, sxUnsat)      # was sxSat "a"

  test "a pattern past PCRE's size is not decided":
    check native(big1700Handler("")) == "hit"
    declines(big1700Handler, seUnsupportedRegex)   # was a clean sxUnsat
    check native(big1700Alt("b")) == "ran"
    declines(big1700Alt, seUnsupportedRegex)       # was sxSat "b"
    check native(big1700Opt("")) == "ran"
    declines(big1700Opt, seUnsupportedRegex)       # was sxSat ""

  test "CRH-04: 2600 nested groups raise RegexError":
    check native(nest2600Handler("a")) == "hit"
    decides(nest2600Handler, sxSat)

  test "250 nested groups compile":
    check native(nest250Match("a")) == "hit"
    decides(nest250Match, sxSat)

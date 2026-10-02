## RFC-0005 (soundness channels) slice S8aw -- S8aq's remainder.
##
## Item 1 (the first suites below). `seqRangeFacts` emits the join "`L =
## seq.last_indexof(s, t)` is at least every found `str.indexof(s, t, i)`".
## Neither Z3 refutes its negation (twelve forms tried, up to 10M units),
## which S8aq took as a reason to decline it. A fact is sound iff it is
## TRUE of the theory; whether Z3 proves it is a completeness question. So
## the links are held to S8ai's bar (negation never SAT, true on every
## small ground instance) and the single-function ranges to S8v's strict
## one, and the truth of every link -- the join and S8ai's shipped
## pairwise, piece, contains, prefix and suffix links, which ship on the
## same argument and had never been checked beyond length 3 -- is
## enumerated exhaustively in Nim, against a reference of the SMT-LIB
## semantics that is itself checked against `strutils.find`/`rfind` and
## against Z3's own ground evaluation.
##
## Item 2.
##
## Regex `replace(s, re"...", by)` (std/re) replaces EVERY leftmost,
## non-overlapping PCRE match of the pattern, in PCRE's own match order
## (alternatives in order, quantifiers greedy). The walker lowered it to
## nim-z3's `replaceRe` behind `-d:z3WithSeqReplaceRe` -- off in every
## build, so every regex replace was a `seZ3VersionMissing` fresh stand-in
## and a claim the real op refutes came back `sxUnknown`, even on a fully
## concrete receiver. The gated branch was also the wrong operator twice
## over: `str.replace_re` replaces the FIRST match only, and SMT-LIB picks
## the SHORTEST leftmost match where PCRE's greedy `+` takes the longest
## (`"ff".replace(re"f+", "x")` is `"x"`, not `"xx"`). Z3 answers `unknown`
## on `str.replace_re{,_all}` even for concrete inputs (nim-z3's own note),
## so turning the define on would not have decided anything either.
##
## The lowering is now the walker's own, for the three pattern shapes whose
## PCRE match selection is fixed by the shape alone:
##   - a literal (every atom one byte): leftmost non-overlapping occurrences;
##   - a one-byte class (`[...]`, `\d \w \s \D \W \S`, `.`): every byte in it;
##   - a class or byte with `+`: every maximal run (greedy).
## Byte sets are computed by the walker from the pattern text with PCRE's
## own reading (`.` excludes `\n`, `\D` is the complement of `\d`, `\n` is
## the newline byte), not by the S6a membership parser. The result is
## unrolled position by position over the receiver: exactly as many
## positions as a receiver of known length has, and `regexReplaceUnroll`
## (16) for a symbolic one, where the value is exact only while the receiver is
## that short; past it the continuation forks onto its own path with a
## fresh value (`seZ3StringIncomplete`, `dcFreshSymbol`: replay-gated
## candidates, never a claim). Any other pattern shape is a scoped
## `seZ3StringIncomplete` decline naming the shape.
import std/[unittest, strutils, re]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

# ---- item 1: the join, decided ------------------------------------------------

const decls = """
(declare-const s String) (declare-const t String)
(declare-const i Int) (declare-const j Int)
"""

proc q(ctx: Z3Context; src: string): seq[Z3Bool] =
  parseSmt2String(ctx, decls & src)

proc stepOneC(ctx: Z3Context; roots: seq[Z3Bool]): Z3Status =
  let sv = querySolver(ctx, roots, 1_000_000'u, seqTheory = false)
  for f in seqRangeFacts(ctx, roots): sv.add f
  sv.check()

proc foundExceedsLast(s, t: string) =
  if t in s and s.find(t, 0) >= 0 and s.rfind(t) < s.find(t, 0):
    symexTarget("aw_found_exceeds_last")

proc foundFromIExceedsLast(s, t: string; i: int) =
  # A nonzero start: the join holds for every `i`, not only 0. (`find`
  # with a start outside 0..len(s) can raise, so it is called in range.)
  if i >= 0 and i <= s.len:
    let r = s.find(t, i)
    if r >= 0 and s.rfind(t) < r:
      symexTarget("aw_found_from_i_exceeds_last")

proc foundAtOrBeforeLast(s, t: string) =
  if t in s and s.find(t, 0) >= 0 and s.rfind(t) >= s.find(t, 0):
    symexTarget("aw_found_at_or_before_last")

suite "S8aw (1): step 1c joins seqRangeFacts to str.indexof":

  test "the join's query is UNSAT theory-free with the facts (step 1c)":
    # RED at 5ffc922 (S8aq pinned it `!= zsUnsat`: the link was declined).
    let ctx = newContext()
    let roots = q(ctx, """(assert (str.contains s t))
                          (assert (>= (str.indexof s t 0) 0))
                          (assert (< (seq.last_indexof s t) (str.indexof s t 0)))""")
    check stepOneC(ctx, roots) == zsUnsat

  test "from a free start too":
    let ctx = newContext()
    let roots = q(ctx, """(assert (>= (str.indexof s t i) 0))
                          (assert (< (seq.last_indexof s t) (str.indexof s t i)))""")
    check stepOneC(ctx, roots) == zsUnsat

  test "companion: a found index at or before L stays SAT":
    let ctx = newContext()
    let roots = q(ctx, """(assert (str.contains s t))
                          (assert (>= (str.indexof s t 0) 0))
                          (assert (>= (seq.last_indexof s t) (str.indexof s t 0)))""")
    check stepOneC(ctx, roots) == zsSat

  # The end-to-end pins run under a `seqQueryRLimit` too small for the
  # sequence theory's own search: the verdict is step 1c's (the facts),
  # not the theory's, and the default budget only spends ~20 s first.
  proc tightSeq(): SymexSettings =
    result = defaultSymexSettings()
    result.budget.seqQueryRLimit = 200_000

  test "end to end: a first index past the last is sxUnsat":
    # RED at 5ffc922: sxUnknown + beSolverUndef (S8aq (2)).
    let r = symexFind(foundExceedsLast, tLabel("aw_found_exceeds_last"), tightSeq())
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "end to end: from a symbolic start, sxUnsat":
    let r = symexFind(foundFromIExceedsLast, tLabel("aw_found_from_i_exceeds_last"),
                      tightSeq())
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "companion: a found index at or before L is reachable":
    let r = symexFind(foundAtOrBeforeLast, tLabel("aw_found_at_or_before_last"))
    checkpoint show(r.errors)
    check r.status == sxSat

# ---- item 1: every link is TRUE, by exhaustive enumeration ---------------------
#
# A reference of the SMT-LIB / Z3 semantics, over `occ(s, t, k)`: `t`
# occurs in `s` at `k` (`0 <= k`, `k + len(t) <= len(s)`, the bytes equal).
#   indexof(s, t, i) = min {k >= i | occ k} for 0 <= i <= len(s), else -1
#   last(s, t)       = max {k | occ k}, else -1 (an empty `t`: len(s))
#   at(s, k)         = s[k] for 0 <= k < len(s), else ""
#   substr(s, k, n)  = s[k ..< min(k + n, len(s))] for 0 <= k < len(s) and
#                      0 < n, else ""
# Both are checked below: against `strutils.find`/`rfind`, and against
# Z3's own ground evaluation of the same terms.

proc occ(s, t: string; k: int): bool =
  if k < 0 or k + t.len > s.len: return false
  for m in 0 ..< t.len:
    if s[k + m] != t[m]: return false
  true

proc refIndexOf(s, t: string; i: int): int =
  if i < 0 or i > s.len: return -1
  for k in i .. s.len:
    if occ(s, t, k): return k
  -1

proc refLast(s, t: string): int =
  for k in countdown(s.len, 0):
    if occ(s, t, k): return k
  -1

proc refAt(s: string; k: int): string =
  if k >= 0 and k < s.len: $s[k] else: ""

proc refSubstr(s: string; k, n: int): string =
  if k >= 0 and k < s.len and n > 0: s[k ..< min(k + n, s.len)] else: ""

proc words(alpha: string; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next

proc linkCounterexamples(hay, needles: seq[string]): seq[string] =
  ## Every link `seqRangeFacts` emits over one haystack and needle, as the
  ## proposition it states (the guards equating two ASTs are discharged:
  ## the haystacks and needles here ARE one), on the reference, for every
  ## start `i`, `j` and piece `k`, `n` in -1 .. len(s) + 1. Empty when every
  ## link holds on every tuple.
  var s, t: string
  var i, j, k, n: int
  proc bad(res: var seq[string]; cond: bool; what: string) =
    if not cond and res.len < 20:
      res.add what & " s=" & escape(s) & " t=" & escape(t) & " i=" & $i &
              " j=" & $j & " k=" & $k & " n=" & $n
  for hs in hay:
    for ts in needles:
      s = hs
      t = ts
      i = 0; j = 0; k = 0; n = 0
      let L = refLast(s, t)
      let lenS = s.len
      let lenT = t.len
      let cont = s.contains(t)
      let pre = s.startsWith(t)
      let suf = s.endsWith(t)
      # Range of `last` (S8v) and its links (S8ai).
      result.bad(L == -1 or (0 <= L and L + lenT <= lenS), "range last")
      result.bad((L >= 0) == cont, "last >= 0 iff contains")
      result.bad(not pre or L >= 0, "prefix -> last >= 0")
      result.bad(not suf or L == lenS - lenT, "suffix -> last = len s - len t")
      var rs = newSeq[int](lenS + 3)          # rs[x + 1] = indexof(s, t, x)
      for x in -1 .. lenS + 1: rs[x + 1] = refIndexOf(s, t, x)
      # Which pieces equal `t`, per (k, n): `at` and `substr` both.
      var pieceAt = newSeq[bool]((lenS + 3) * (lenS + 3))
      for kk in -1 .. lenS + 1:
        for nn in -1 .. lenS + 1:
          pieceAt[(kk + 1) * (lenS + 3) + nn + 1] =
            refSubstr(s, kk, nn) == t or refAt(s, kk) == t
      for ii in -1 .. lenS + 1:
        i = ii; j = 0; k = 0; n = 0
        let ri = rs[ii + 1]
        # Range of `indexof` (S8v).
        result.bad(ri == -1 or (0 <= ri and ii <= ri and ri + lenT <= lenS),
                   "range indexof")
        # Contains / prefix / suffix links (S8ae, S8ai).
        result.bad(not (ri >= 0) or cont, "indexof found -> contains")
        result.bad(not (cont and ii == 0) or ri >= 0, "contains -> found from 0")
        result.bad(not (pre and ii == 0) or ri == 0, "prefix -> found at 0")
        result.bad(not (suf and 0 <= ii and ii <= lenS - lenT) or
                   (ii <= ri and ri <= lenS - lenT), "suffix found from i")
        # The join (S8aw).
        result.bad(not (ri >= 0) or ri <= L, "join: found <= last")
        # Pairwise order (S8ai), from `0 <= i <= j`.
        for jj in -1 .. lenS + 1:
          j = jj
          if 0 <= ii and ii <= jj:
            let rj = rs[jj + 1]
            result.bad(not (ri >= jj) or rj == ri, "pairwise: r_i >= j -> r_j = r_i")
            result.bad(not (rj >= 0) or (0 <= ri and ri <= rj),
                       "pairwise: r_j found -> 0 <= r_i <= r_j")
        j = 0
        # Piece links (S8ae, S8ai): `str.at(s, k)` or `str.substr(s, k, n)`
        # equal to `t`.
        for kk in -1 .. lenS + 1:
          k = kk
          let inRange = 0 <= kk and kk < lenS
          for nn in -1 .. lenS + 1:
            n = nn
            if pieceAt[(kk + 1) * (lenS + 3) + nn + 1]:
              result.bad(cont, "piece -> contains")
              result.bad(not (inRange and 0 <= ii and ii <= kk) or
                         (0 <= ri and ri <= kk), "piece: found from i <= k, at most k")
              result.bad(not inRange or L >= kk, "piece: last >= k")

suite "S8aw (1): every link is true (exhaustive enumeration)":

  test "the reference is Nim's own strutils.find / rfind":
    # strutils.find(s, t, i) is `indexof` for 0 <= i <= len(s) (an empty
    # `t` is found at `i`); rfind(s, t) is `last` (an empty `t`: len(s)).
    var bad: seq[string]
    for s in words("ab", 6):
      for t in words("ab", 6):
        if strutils.rfind(s, t) != refLast(s, t) and bad.len < 5:
          bad.add "rfind " & s & " " & t
        for i in 0 .. s.len:
          if strutils.find(s, t, i) != refIndexOf(s, t, i) and bad.len < 5:
            bad.add "find " & s & " " & t & " " & $i
    checkpoint $bad
    check bad.len == 0

  test "the reference is Z3's own ground evaluation":
    # The links are facts about Z3's functions, so the reference must be
    # Z3's too: its rewriter folds each ground term to a numeral.
    let ctx = newContext()
    proc numTxt(v: int): string =
      if v < 0: "(- " & $(-v) & ")" else: $v
    var bad: seq[string]
    var checked = 0
    for s in words("ab", 4):
      for t in words("ab", 3):
        let ss = mkString(ctx, s)
        let tt = mkString(ctx, t)
        let lz = $wrap[Z3Int](ctx, ctx.checkErr Z3_simplify(ctx.raw,
          ctx.checkErr Z3_mk_seq_last_index(ctx.raw, ss.raw, tt.raw)))
        if lz != numTxt(refLast(s, t)) and bad.len < 10:
          bad.add "last " & s & " " & t & " z3=" & lz
        for i in -1 .. s.len + 1:
          let iz = $wrap[Z3Int](ctx, ctx.checkErr Z3_simplify(ctx.raw,
            ctx.checkErr Z3_mk_seq_index(ctx.raw, ss.raw, tt.raw,
                                         mkInt(ctx, i).raw)))
          inc checked
          if iz != numTxt(refIndexOf(s, t, i)) and bad.len < 10:
            bad.add "indexof " & s & " " & t & " " & $i & " z3=" & iz
    checkpoint $checked & " " & $bad
    check bad.len == 0

  test "alphabet {a, b}: haystacks and needles up to length 6":
    let ws = words("ab", 6)
    let cex = linkCounterexamples(ws, ws)
    checkpoint $cex
    check cex.len == 0

  test "alphabet {a, b, c}: haystacks up to length 5, needles up to 3":
    let cex = linkCounterexamples(words("abc", 5), words("abc", 3))
    checkpoint $cex
    check cex.len == 0

  test "the enumeration catches a broken link (a strict join)":
    var hit = false
    for s in words("ab", 3):
      for t in words("ab", 2):
        let r = refIndexOf(s, t, 0)
        if r >= 0 and not (r < refLast(s, t)): hit = true
    check hit

  test "the emitted join: exactly one link over S8v's terms, never refuted":
    # The terms of S8v's per-fact pin: one indexof, one last_indexof.
    let ctx = newContext()
    let roots = q(ctx, """(assert (>= (str.indexof s t i) (- 2)))
                          (assert (>= (seq.last_indexof s t) (- 2)))""")
    let alone = seqRangeFacts(ctx, @[roots[0]]).len +
                seqRangeFacts(ctx, @[roots[1]]).len
    let facts = seqRangeFacts(ctx, roots)
    check facts.len == alone + 1
    for f in facts:
      checkpoint $f
      check querySolver(ctx, @[not f], 1_000_000'u).check() != zsSat

# ---- concrete receivers decide ---------------------------------------------

proc litFirstOnly(s: string) =
  if s == "foofoo" and s.replace(re"foo", "bar") == "barfoo":
    symexTarget("aw_lit_first_only")

proc litAll(s: string) =
  if s == "foofoo" and s.replace(re"foo", "bar") == "barbar":
    symexTarget("aw_lit_all")

proc litOverlap(s: string) =
  # Leftmost, non-overlapping: "aaa" holds one "aa" (at 0), then "a".
  if s == "aaa" and s.replace(re"aa", "x") != "xa":
    symexTarget("aw_lit_overlap")

proc classDelete(s: string) =
  if s == "a1b2c3" and s.replace(re"\d", "") != "abc":
    symexTarget("aw_class_delete")

proc classDeleteHit(s: string) =
  if s == "a1b2c3" and s.replace(re"[0-9]", "") == "abc":
    symexTarget("aw_class_delete_hit")

proc runCollapse(s: string) =
  if s == "a  b\t\tc" and s.replace(re"\s+", " ") != "a b c":
    symexTarget("aw_run_collapse")

proc greedyRun(s: string) =
  # PCRE's `+` is greedy: one match covering "ff". SMT-LIB's shortest
  # leftmost match would give "xx".
  if s == "ff" and s.replace(re"f+", "x") == "xx":
    symexTarget("aw_greedy_shortest")

proc greedyRunHit(s: string) =
  if s == "ff" and s.replace(re"f+", "x") == "x":
    symexTarget("aw_greedy_hit")

proc dotNoNewline(s: string) =
  # PCRE's `.` (no DOTALL) never matches "\n".
  if s == "a\nb" and s.replace(re".", "x") == "xxx":
    symexTarget("aw_dot_newline")

proc dotNoNewlineHit(s: string) =
  if s == "a\nb" and s.replace(re".", "x") == "x\nx":
    symexTarget("aw_dot_newline_hit")

proc complementClass(s: string) =
  # `\D` is every byte but a digit (the S6a parser reads it as a literal D).
  if s == "a1D" and s.replace(re"\D", "") != "1":
    symexTarget("aw_complement")

suite "S8aw (2): a regex replace over a concrete receiver is decided":

  test "a literal: the first-occurrence-only result is sxUnsat":
    # RED at 5ffc922: sxUnknown (seZ3VersionMissing stand-in, replay-refuted).
    let r = symexFind(litFirstOnly, tLabel("aw_lit_first_only"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    check not hasKind(r.errors, seZ3VersionMissing)

  test "a literal: every occurrence replaced is sxSat":
    let r = symexFind(litAll, tLabel("aw_lit_all"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not hasKind(r.errors, seZ3VersionMissing)

  test "a literal: occurrences are leftmost and non-overlapping":
    let r = symexFind(litOverlap, tLabel("aw_lit_overlap"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "a one-byte class deleted: any other result is sxUnsat":
    let r = symexFind(classDelete, tLabel("aw_class_delete"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "companion: the class deleted is sxSat":
    let r = symexFind(classDeleteHit, tLabel("aw_class_delete_hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "a class run collapsed: any other result is sxUnsat":
    let r = symexFind(runCollapse, tLabel("aw_run_collapse"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "a greedy run is one match (SMT-LIB's shortest match is not PCRE's)":
    let r = symexFind(greedyRun, tLabel("aw_greedy_shortest"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let h = symexFind(greedyRunHit, tLabel("aw_greedy_hit"))
    checkpoint show(h.errors)
    check h.status == sxSat

  test "'.' does not match a newline":
    let r = symexFind(dotNoNewline, tLabel("aw_dot_newline"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let h = symexFind(dotNoNewlineHit, tLabel("aw_dot_newline_hit"))
    checkpoint show(h.errors)
    check h.status == sxSat

  test "\\D is the complement of \\d":
    let r = symexFind(complementClass, tLabel("aw_complement"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

# ---- symbolic receivers -----------------------------------------------------

proc deleteNeverGrows(s: string) =
  if s.len <= 6 and s.replace(re"[0-9]", "").len > s.len:
    symexTarget("aw_delete_grows")

proc expandWitness(s: string) =
  if s.len == 3 and s.replace(re"a", "xy") == "xyxyb":
    symexTarget("aw_expand_witness")

proc pastUnroll(s: string) =
  # Reachable only with a receiver longer than the unroll: the value there
  # is a fresh stand-in, so a model is a candidate, never a claim.
  if s.len > 40 and s.replace(re"a", "") == "b":
    symexTarget("aw_past_unroll")

suite "S8aw (2): a regex replace over a symbolic receiver":

  test "deletion never grows the string: sxUnsat":
    let r = symexFind(deleteNeverGrows, tLabel("aw_delete_grows"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "an expansion is solved for its receiver: sxSat with the witness":
    let r = symexFind(expandWitness, tLabel("aw_expand_witness"))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check r.witness[0] == "aab"

  test "past the unroll: a sound candidate, never a false sxSat or sxUnsat":
    # A tight sequence budget (S8v's precedent): the query holds the
    # unroll's per-position `str.at` terms over a receiver longer than the
    # unroll, which Z3 does not decide within the default 20M units either;
    # the verdict asked of it is only that it never claims.
    proc tight(): SymexSettings =
      result = defaultSymexSettings()
      result.budget.seqQueryRLimit = 2_000_000
    let r = symexFind(pastUnroll, tLabel("aw_past_unroll"), tight())
    checkpoint $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown}
    check hasKind(r.errors, seZ3StringIncomplete)
    if r.status == sxSat:
      check r.witness[0].len > 40
      check r.witness[0].replace(re"a", "") == "b"

# ---- shapes with no sound lowering: a scoped decline -------------------------

proc alternationOrder(s: string) =
  # PCRE tries `a` before `ab`: "ab" -> "xb". A leftmost-longest reading
  # would give "x".
  if s == "ab" and s.replace(re"a|ab", "x") == "x":
    symexTarget("aw_alternation")

proc alternationOrderHit(s: string) =
  if s == "ab" and s.replace(re"a|ab", "x") == "xb":
    symexTarget("aw_alternation_hit")

suite "S8aw (2): other pattern shapes decline, scoped and named":

  test "an alternation: the result PCRE never gives is not claimed":
    let r = symexFind(alternationOrder, tLabel("aw_alternation"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check hasKind(r.errors, seZ3StringIncomplete)
    var named = false
    for e in r.errors:
      if e.kind == seZ3StringIncomplete and "a|ab" in e.msg: named = true
    check named
    check not hasKind(r.errors, seZ3VersionMissing)

  test "companion: the result PCRE gives is reachable (replay-confirmed)":
    let r = symexFind(alternationOrderHit, tLabel("aw_alternation_hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

proc knownLength(n: int) =
  # A literal receiver: its length is a numeral, so the unroll is exact and
  # nothing is tainted.
  let t = "a1b22".replace(re"\d+", "#")
  if n == 1 and t != "a#b#":
    symexTarget("aw_known_length")

proc starDecline(s: string) =
  if s == "b" and s.replace(re"a*", "x") == "b":
    symexTarget("aw_star")

proc spaceDecline(s: string) =
  if s == "a b" and s.replace(re"a b", "x") == "a b":
    symexTarget("aw_space")

proc reversedRange(s: string) =
  if s.replace(re"[z-a]", "x") == "q":
    symexTarget("aw_reversed")

proc declineMsg(r: SymexResult; k: SymexErrorKind; frag: string): bool =
  for e in r.errors:
    if e.kind == k and frag in e.msg: return true
  false

suite "S8aw (2): exact on a known length; each decline names its construct":

  test "a receiver of known length is exact and untainted":
    let r = symexFind(knownLength, tLabel("aw_known_length"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    check r.errors.len == 0

  test "a quantifier that matches empty declines (empty-match semantics)":
    # Nim: "b".replace(re"a*", "x") == "xbx" -- the decline never claims.
    let r = symexFind(starDecline, tLabel("aw_star"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check declineMsg(r, seZ3StringIncomplete, "can match empty")

  test "whitespace outside a class declines (re vs rex is not in the IR)":
    let r = symexFind(spaceDecline, tLabel("aw_space"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check declineMsg(r, seZ3StringIncomplete, "whitespace")

  test "a reversed class range is PCRE's compile error: seUnsupportedRegex":
    let r = symexFind(reversedRange, tLabel("aw_reversed"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check declineMsg(r, seUnsupportedRegex, "out of order")

suite "S8aw: walker version floor":
  test "symexWalkerVersion >= 196":
    check parseInt(symexWalkerVersion) >= 196

## RFC-0016 0.10.0 review D3c-7: the string-lowering support leaf.
##
## The Z3 string machinery `runtime_strings.nim` (the Cluster S arm) and
## `runtime.nim` both read: `literalStringBytes`, `splitNeedle`, the
## `NotIn` forms and the index-split subsystem (`IndexSplit`, `lowerIndexSplit`,
## `indexSplitRoots` and the axioms they build). It is pure Z3 term building
## over strings and ints: it imports only `z3` and `./types` and names no
## `runtime.nim` symbol.
##
## A threadvar added here that holds a Z3 term of the run's context MUST be
## reset in `resetStringSupport`, which `resetSymexRunState` calls: a value
## left over from the previous run holds a freed context.
import std/tables
import std/options
import std/sets
import std/algorithm
import std/strutils
import z3
import ./types

proc literalStringBytes*(z: Z3String): tuple[ok: bool, s: string] =
  ## RFC-0005 S8cf. `z`'s bytes when it folds to a literal.
  let v = simplify(z)
  if not Z3_is_string(v.ctx.raw, v.raw): return
  for cp in getStringContents(v):
    if cp notin 0 .. 255: return
    result.s.add char(cp)
  result.ok = true

type IndexSplit* = object
  ## RFC-0005 S8ag. One `str.indexof(s, c, start)`, lowered (`iekStrFind`)
  ## to the fresh Int `ix` and the split `s = pre ++ x ++ c ++ post`
  ## (`indexSplitAxioms`). S8ag split a one-character literal needle only;
  ## RFC-0005 S8au splits every needle: a literal of any length, a
  ## computed (symbolic) one, and `seq.last_indexof(s, c)` (`rfind`,
  ## `last`: the split `s = pre ++ c ++ post`, `x` and `start` unused).
  ix*: Z3Int
  s*, c*: Z3String
  start*: Z3Int
  pre*, x*, post*: Z3String
  last*: bool
    ## RFC-0005 S8au: `ix` stands for `seq.last_indexof(s, c)` (`rfind`),
    ## not `str.indexof(s, c, start)`.
  found*, notFound*: Z3Bool
  built*: bool
    ## RFC-0005 S8ba: the split's axioms (`indexSplitAxioms`), built once,
    ## by the first query that reaches the split (`indexSplitRoots`).

var indexSplits* {.threadvar.}: seq[IndexSplit]
  ## RFC-0005 S8ag. Every split lowered in the running walk, in lowering
  ## order. Its axioms are not a pool asserted everywhere (as
  ## `stripDecompConds` is): `indexSplitRoots` adds the ones a query
  ## reaches, with the chain facts between them. Reset at `runSymexImpl`
  ## entry.

var indexSplitOf {.threadvar.}: tuple[ctx: Z3Context, ids: Table[int, int]]
  ## RFC-0005 S8ag. `ix`'s AST id -> its index in `indexSplits`, valid only
  ## in `ctx` (an AST id means nothing in another context).

var indexSplitCounter* {.threadvar.}: int
  ## RFC-0005 S8ag. Per-run unique-name counter for the splits' fresh
  ## constants (the `stripSynthCounter` precedent: two occurrences must not
  ## share a constant). Reset at `runSymexImpl` entry.

proc splitNeedle*(needle: Z3String): Z3String =
  ## RFC-0005 S8au. The needle a split is built over: the literal `needle`
  ## folds to (a char needle's `str.from_code(bv2nat(#x3a))` is ":"), or
  ## `needle` itself when it is computed. Folding keeps a literal's
  ## axioms in the literal forms (`NotIn`) Z3 decides fastest.
  let ctx = needle.ctx
  let f = ctx.checkErr Z3_simplify(ctx.raw, needle.raw)
  if Z3_is_string(ctx.raw, f): wrap[Z3String](ctx, f) else: needle

proc literalLen*(c: Z3String): int =
  ## RFC-0005 S8au. The length of `c` when it is a string literal, else -1.
  if Z3_is_string(c.ctx.raw, c.raw): int(Z3_get_string_length(c.ctx.raw, c.raw))
  else: -1

type NotInForm* = enum
  ## RFC-0005 S8au. How a split states "`c` occurs nowhere in `t`" for a
  ## literal needle `c`. The two are the same predicate; Z3 costs them
  ## differently, and the two Z3 versions nelli runs on disagree on which
  ## is cheaper (`notInFormFor`).
  nfRegex        ## `t in (allchar & ~c)*` (one character), else
                 ## `t in ~(all* ++ c ++ all*)`
  nfNotContains  ## `not str.contains(t, c)`

var notInFormOverride* {.threadvar.}: Option[NotInForm]
  ## RFC-0005 S8au. Test hook: when set, every literal split takes this
  ## form instead of `notInFormFor`'s per-version choice, so a suite can
  ## measure or differential-check either form on either Z3.

proc notInFormFor*(major, minor: int): NotInForm =
  ## RFC-0005 S8au. The form of "`c` notin `t`" for a literal needle, per
  ## the linked Z3 (S8ag's finding: the regex is far cheaper on 5.1, and
  ## required for round-6 B1-3 there; 4.13.4, the symex-mingw leg's Z3,
  ## pays more for it on the deepest pair-loop hits). Measured in-process
  ## on N36 and s1c, both Z3 versions (the RFC's S8au note): 5.x keeps the
  ## regex; 4.x takes `not contains`.
  if major >= 5: nfRegex else: nfNotContains

var linkedNotInForm {.threadvar.}: Option[NotInForm]
  ## RFC-0005 S8au: `notInFormFor` of the linked Z3, read once per thread.

proc notInForm*(): NotInForm =
  ## RFC-0005 S8au. The form a literal split takes in this process.
  if notInFormOverride.isSome: return notInFormOverride.get
  if linkedNotInForm.isNone:
    let v = z3Version()
    linkedNotInForm = some(notInFormFor(int(v.major), int(v.minor)))
  linkedNotInForm.get

type NotIn* = object
  ## RFC-0005 S8au. "`c` occurs nowhere in `t`" for one needle `c`, with
  ## its regex (a literal `c` under `nfRegex`) built once, up front: the
  ## order a query's terms are created in moves Z3's cost (`checkCapped`),
  ## and S8ag's one-character split built its regex before the split's
  ## other terms. Keeping that order keeps S8ag's measured costs.
  c: Z3String
  re: Option[Z3Regex[Z3String]]

proc notInOf*(c: Z3String): NotIn =
  ## RFC-0005 S8au. `NotIn` for the needle `c`. A literal `c` takes
  ## `notInForm`'s form: under `nfRegex` a one-character `c` is `t in
  ## (allchar & ~c)*` (S8ag's form, unchanged) and a longer one `t in
  ## ~(all* ++ c ++ all*)`, each exactly the strings without `c` as a
  ## substring; under `nfNotContains`, and for a computed `c` (a regex
  ## needs a literal), `not str.contains(t, c)`.
  let ctx = c.ctx
  let n = literalLen(c)
  result.c = c
  if n >= 1 and notInForm() == nfRegex:
    if n == 1:
      result.re = some(star(intersect(mkRegexAllChar[Z3String](ctx),
                                      complement(mkRegex(ctx, c)))))
    else:
      let anyS = star(mkRegexAllChar[Z3String](ctx))
      result.re = some(complement(concat(anyS, mkRegex(ctx, c), anyS)))

proc holds*(ni: NotIn; t: Z3String): Z3Bool =
  ## RFC-0005 S8au. `ni.c` occurs nowhere in `t` (for a non-empty `ni.c`).
  if ni.re.isSome: matches(t, ni.re.get) else: not contains(t, ni.c)

proc foldLit(ctx: Z3Context; t: Z3String): Z3String =
  ## RFC-0005 S8au. `t` simplified when it folds to a literal (a slice of
  ## a literal needle), else `t`.
  let f = ctx.checkErr Z3_simplify(ctx.raw, t.raw)
  if Z3_is_string(ctx.raw, f): wrap[Z3String](ctx, f) else: t

proc matchChars(ctx: Z3Context; s: Z3String; ix: Z3Int; c: Z3String;
                n: int): Z3Bool =
  ## RFC-0005 S8au. `s[ix + k] == c[k]` for each `k < n`, as `str.at`
  ## terms (the form a byte read `s[i + 1]` lowers to), for a literal
  ## needle of `2 <= n <= maxMatchChars` characters, else `true`. Implied
  ## by the found arm's `s = pre ++ x ++ c ++ post` (or `pre ++ c ++ post`)
  ## with `ix = len(pre ++ x)`: a restatement, so exact. Z3 4.13.4 does not
  ## relate a read past the match's first character to that word equation
  ## (`s.find("\r\n") = i, i >= 0, s[i + 1] != '\n'` ran out at 20M units
  ## on it, either `c notin t` form), and decides it with these. A
  ## one-character needle takes none: S8ag's split is kept term for term.
  const maxMatchChars = 16
  if n < 2 or n > maxMatchChars: return mkBool(ctx, true)
  # Each `c[k]` is read by folding `str.at` of the literal (not
  # `Z3_get_string`, which spells an escaped byte as its escape text; see
  # `evalStrBytes`).
  result = mkBool(ctx, true)
  for k in 0 ..< n:
    let at = wrap[Z3String](ctx, ctx.checkErr Z3_mk_seq_at(ctx.raw, s.raw,
                                                (ix + mkInt(ctx, k)).raw))
    let ck = foldLit(ctx, wrap[Z3String](ctx, ctx.checkErr Z3_mk_seq_at(
                                ctx.raw, c.raw, mkInt(ctx, k).raw)))
    result = result and (at == ck)

proc indexSplitAxioms*(sp: IndexSplit):
    tuple[found, notFound: Z3Bool] =
  ## RFC-0005 S8ag. The two axioms that make `sp.ix` equal to Z3's
  ## `str.indexof(sp.s, sp.c, sp.start)`. For a one-character `sp.c`:
  ##   found:    ix = -1, or ix >= 0 and s = pre ++ x ++ c ++ post and
  ##             len(pre) = start and ix = start + len(x) and c notin x
  ##   notFound: ix = -1 implies start < 0, or start > len(s), or c notin
  ##             s[start ..]
  ## Equivalence (the RFC's S8ag note has it in full): when `c` occurs in
  ## `s` at or after a `start` in `0 .. len(s)`, its first such position
  ## `r` gives the unique `ix = r` (pre = s[0 ..< start], x = s[start ..<
  ## r], post = s[r + 1 ..]), and `notFound` rules out `ix = -1`; when it
  ## does not, the found arm needs a `c` at or after `start` and is
  ## impossible, so `ix = -1`, which `notFound` allows. So every `(s,
  ## start)` has a model, and in every model `ix` is `str.indexof`'s value
  ## (including `start = len(s)`: `s[start ..]` is "", so -1).
  ##
  ## RFC-0005 S8au: any needle. For `n = len(c) >= 1` the gap condition
  ## is `c notin x ++ c[0 ..< n - 1]`: an earlier occurrence starting in
  ## `x` ends at most `n - 2` past it, inside `x` and the match's first
  ## `n - 1` characters (for `n = 1`, S8ag's `c notin x`). Conversely the
  ## first occurrence `r` gives `x = s[start ..< r]`, and `x ++ c[0 ..< n
  ## - 1] = s[start ..< r + n - 1]` holds no occurrence, since one would
  ## start before `r`. An empty `c` is found at `start` exactly when `0
  ## <= start <= len(s)` (SMT-LIB, and Nim's `find`); a computed needle
  ## takes that arm when its length is 0 and the split otherwise.
  ##
  ## `last` (`seq.last_indexof(s, c)`, Nim's `rfind`, which agree, empty
  ## needle included: `len(s)`):
  ##   found:    ix = -1, or ix >= 0 and s = pre ++ c ++ post and
  ##             len(pre) = ix and c notin c[1 ..] ++ post
  ##   notFound: ix = -1 implies c notin s
  ## A later occurrence starts past `ix`, inside `s[ix + 1 ..] = c[1 ..]
  ## ++ post`; the last one `r` gives `pre = s[0 ..< r]`, `post = s[r + n
  ## ..]`, and `s[r + 1 ..]` holds none.
  # The terms are created in S8ag's order for its one-character needle
  # (`NotIn`), and the empty-needle ones only for a needle that may be
  # empty: Z3's cost follows what the context holds and in what order
  # (`checkCapped`). Unused or reordered terms moved round-6 B1-1's SAT
  # hit, an S8ag split query unchanged in text, from 0.37M units to 7.7M
  # (Z3 5.1).
  let ctx = sp.s.ctx
  let zero = mkInt(ctx, 0)
  let minusOne = mkInt(ctx, -1)
  let lenS = len(sp.s)
  let n = literalLen(sp.c)
  let absent = notInOf(sp.c)
  proc lenC(): Z3Int =
    if n >= 0: mkInt(ctx, n) else: len(sp.c)
  var found, notFound: Z3Bool
  if sp.last:
    let rest = if n == 1: sp.post
               else: concat(foldLit(ctx, substr(sp.c, mkInt(ctx, 1),
                                               lenC() - mkInt(ctx, 1))),
                            sp.post)
    found = (sp.ix >= zero) and
      (sp.s == concat(sp.pre, concat(sp.c, sp.post))) and
      (len(sp.pre) == sp.ix) and absent.holds(rest) and
      matchChars(ctx, sp.s, sp.ix, sp.c, n)
    found = (sp.ix == minusOne) or found
    notFound = implies(sp.ix == minusOne, absent.holds(sp.s))
    if n >= 1: return (found: found, notFound: notFound)
    let emptyIx = sp.ix == lenS
    if n == 0: return (found: emptyIx, notFound: mkBool(ctx, true))
    let isEmpty = lenC() == zero
    return (found: (isEmpty and emptyIx) or ((not isEmpty) and found),
            notFound: isEmpty or notFound)
  let gap = if n == 1: sp.x
            else: concat(sp.x, foldLit(ctx, substr(sp.c, zero,
                                                   lenC() - mkInt(ctx, 1))))
  found = (sp.ix >= zero) and
    (sp.s == concat(sp.pre, concat(sp.x, concat(sp.c, sp.post)))) and
    (len(sp.pre) == sp.start) and (sp.ix == sp.start + len(sp.x)) and
    absent.holds(gap)
  if n >= 2: found = found and matchChars(ctx, sp.s, sp.ix, sp.c, n)
  found = (sp.ix == minusOne) or found
  notFound = implies(sp.ix == minusOne,
    (sp.start < zero) or (sp.start > lenS) or
    absent.holds(substr(sp.s, sp.start, lenS - sp.start)))
  if n >= 1: return (found: found, notFound: notFound)
  let emptyIx = sp.ix == ite((zero <= sp.start) and (sp.start <= lenS),
                             sp.start, minusOne)
  if n == 0: return (found: emptyIx, notFound: mkBool(ctx, true))
  let isEmpty = lenC() == zero
  (found: (isEmpty and emptyIx) or ((not isEmpty) and found),
   notFound: isEmpty or notFound)

proc indexSplitChain*(a, b: IndexSplit): Z3Bool =
  ## RFC-0005 S8ag. The chain fact between two splits of one haystack: when
  ## both find their needle and `b` starts just past `a`'s match, `b`'s
  ## prefix is `a`'s prefix through the match, and `a`'s suffix is `b`'s
  ## gap, needle and suffix. Valid: both sides are the prefix (suffix) of
  ## `s` of the same length. A scan chain (`readCString`'s next key starts
  ## at `p + 1`) needs it to be found quickly: without it Z3 relates the
  ## two decompositions of `s` only through a word equation.
  ## RFC-0005 S8au: "just past the match" is `a.ix + len(a.c)` (1 for
  ## S8ag's one-character needle). A computed needle may be empty, whose
  ## found arm does not decompose `s`; the fact is then guarded by both
  ## needles being non-empty, where (F) gives each decomposition.
  let ctx = a.s.ctx
  let zero = mkInt(ctx, 0)
  let na = literalLen(a.c)
  let lenA = if na >= 0: mkInt(ctx, na) else: len(a.c)
  var premise = (a.ix >= zero) and (b.ix >= zero) and
                (b.start == a.ix + lenA)
  if na < 0: premise = premise and (lenA > zero)
  if literalLen(b.c) < 0: premise = premise and (len(b.c) > zero)
  implies(premise,
          (b.pre == concat(a.pre, concat(a.x, a.c))) and
          (a.post == concat(b.x, concat(b.c, b.post))))

proc indexSplitLastLink*(a, b: IndexSplit): Z3Bool =
  ## RFC-0005 S8au. The link between an `rfind` split `a` (`a.last`) and a
  ## `find` split `b` of the same haystack and needle: a found `b` is an
  ## occurrence, so the last one is at or after it (`b.ix >= 0` implies
  ## `a.ix >= b.ix`; with an empty needle `b.ix` is `b.start <= len(s) =
  ## a.ix`). Valid, by the two splits' axioms (pinned on random instances
  ## in `tsymex_rfc0005_s8au_remainder` (4)). Without it Z3 relates the
  ## two decompositions of `s` only through a word equation: `i =
  ## s.rfind("ab"); i >= 0 and s.find("ab", i + 1) >= 0` took 10M units
  ## (485 s wall under load) to refute, and is linear with it.
  implies(b.ix >= mkInt(a.s.ctx, 0), a.ix >= b.ix)

proc lowerIndexSplit*(s, c: Z3String; start: Z3Int; last = false): Z3Int =
  ## RFC-0005 S8ag. A fresh Int standing for `str.indexof(s, c, start)`
  ## (RFC-0005 S8au: or, `last`, for `seq.last_indexof(s, c)`; any needle,
  ## `splitNeedle`'d by the caller), registered for `indexSplitRoots`.
  let ctx = s.ctx
  # RFC-0005 S8bl (item 2): a ground haystack and start (a string pinned
  # by `symexAssume(s == "lit")`, scanned from a ground offset) fold to
  # their numeral -- Z3's rewriter evaluates `str.indexof` of literals. The
  # split's word equations over a literal took Z3 up to the whole
  # `seqQueryRLimit` to refute an infeasible loop exit (B6-1-red, B6-6).
  # The folded term is the one the split stands for: `seq.last_indexof`
  # for `last` (`rfind`, which takes no start). Folding `str.indexof` there
  # turned `s.rfind("")` into `0` for ANY `s` (Z3 rewrites an empty needle
  # from offset 0 to 0): a false `sxUnsat` on `s.rfind("") == 2` and a
  # false hit on `s.rfind("") != s.len` (batch 6).
  let term = if last: lastIndexOf(s, c) else: indexOf(s, c, start)
  let folded = ctx.checkErr Z3_simplify(ctx.raw, term.raw)
  if Z3_is_numeral_ast(ctx.raw, folded):
    return wrap[Z3Int](ctx, folded)
  inc indexSplitCounter
  let tag = "__s8ag_ix" & $indexSplitCounter
  let sp = IndexSplit(ix: mkIntVar(ctx, tag), s: s, c: c, start: start,
                      pre: mkStringVar(ctx, tag & "_pre"),
                      x: mkStringVar(ctx, tag & "_x"),
                      post: mkStringVar(ctx, tag & "_post"),
                      last: last)
  if indexSplitOf.ctx != ctx:
    indexSplitOf = (ctx: ctx, ids: initTable[int, int]())
  indexSplitOf.ids[astId(ctx, sp.ix.raw)] = indexSplits.len
  indexSplits.add sp
  sp.ix

proc registeredIndexSplit*(ctx: Z3Context; a: RawZ3Ast): int =
  ## RFC-0005 S8ag. The `indexSplits` index of the split whose `ix` is `a`
  ## in `ctx`, or -1.
  if indexSplitOf.ctx != ctx: return -1
  indexSplitOf.ids.getOrDefault(astId(ctx, a), -1)

proc indexSplitRoots*(ctx: Z3Context; base: openArray[Z3Bool]): seq[Z3Bool] =
  ## RFC-0005 S8ag. The axioms of every split `base` reaches -- its `ix`
  ## occurs in `base`, or in the haystack, needle or start of a split
  ## already reached -- and the chain facts (`indexSplitChain`) between
  ## reached splits of one haystack. A split not reached is left out: its
  ## axioms mention only its own fresh constants beside terms the reached
  ## ones fix, and every value of those has an extension satisfying them,
  ## so leaving them out prunes no model and adds none of the query's.
  ##
  ## RFC-0005 S8au: the chain facts are between CONSECUTIVE reached
  ## `str.indexof` splits of one haystack (in lowering order), not every
  ## ordered pair: `n - 1` facts for `n` splits, where S8ag asserted
  ## `n (n - 1)`. Each fact is valid (implied by the two splits' axioms),
  ## so asserting any subset of them is exact; consecutive is the subset a
  ## scan chain needs. A query holds the splits of one path (the ones its
  ## own terms reach), lowered in program order, and a chained scan's
  ## next split starts at its predecessor's match: the one lowered just
  ## before it on that haystack.
  if indexSplitOf.ctx != ctx or indexSplits.len == 0: return
  var reached: seq[int]
  var isReached: HashSet[int]
  var seen: HashSet[int]
  var stack: seq[RawZ3Ast]
  for r in base: stack.add r.raw
  while true:
    while stack.len > 0:
      let t = stack.pop()
      let id = astId(ctx, t)
      if id in seen: continue
      seen.incl id
      if Z3_get_ast_kind(ctx.raw, t) != Z3_APP_AST: continue
      let k = indexSplitOf.ids.getOrDefault(id, -1)
      if k >= 0 and k notin isReached:
        isReached.incl k
        reached.add k
      let app = Z3_to_app(ctx.raw, t)
      for i in 0 ..< int(Z3_get_app_num_args(ctx.raw, app)):
        stack.add Z3_get_app_arg(ctx.raw, app, cuint(i))
    # A reached split's haystack, needle and start may hold further
    # splits (RFC-0005 S8au: a computed needle may be another find's
    # slice).
    var grew = false
    for k in reached:
      for t in [indexSplits[k].s.raw, indexSplits[k].c.raw,
                indexSplits[k].start.raw]:
        if astId(ctx, t) notin seen:
          stack.add t
          grew = true
    if not grew: break
  reached.sort()
  # RFC-0005 S8ba: the order a split's terms reach the context is fixed
  # here, once. The first query that reaches a split builds its axioms,
  # every newly reached split in lowering order and each in
  # `indexSplitAxioms`' fixed term order, before any chain or link fact;
  # later queries reuse them (`built`) and create none of its terms again.
  # Built eagerly at lowering instead, the axioms of splits no query
  # reaches sit in the context too, and Z3's cost follows what the context
  # holds (`checkCapped`): measured on Z3 5.1, that cost 4.6x the target
  # units on `r6_n36_raise_degrade`, 5.3x on `s1c_verdict` and 11x on
  # `s8au_remainder`, and turned one more S8ag (5) hit into a slow SAT.
  for k in reached:
    if not indexSplits[k].built:
      let ax = indexSplitAxioms(indexSplits[k])
      indexSplits[k].found = ax.found
      indexSplits[k].notFound = ax.notFound
      indexSplits[k].built = true
    result.add indexSplits[k].found
    result.add indexSplits[k].notFound
  var lastOn: Table[int, int]   ## haystack AST id -> latest reached split
  for k in reached:
    if indexSplits[k].last: continue
    let h = astId(ctx, indexSplits[k].s.raw)
    let prev = lastOn.getOrDefault(h, -1)
    if prev >= 0:
      result.add indexSplitChain(indexSplits[prev], indexSplits[k])
    lastOn[h] = k
  # RFC-0005 S8au: each reached `rfind` split with each reached `find`
  # split of the same haystack and needle (`indexSplitLastLink`; one fact
  # per such pair, and a query rarely holds more than one or two rfinds).
  for a in reached:
    if not indexSplits[a].last: continue
    let h = astId(ctx, indexSplits[a].s.raw)
    let n = astId(ctx, indexSplits[a].c.raw)
    for b in reached:
      if indexSplits[b].last: continue
      if astId(ctx, indexSplits[b].s.raw) == h and
         astId(ctx, indexSplits[b].c.raw) == n:
        result.add indexSplitLastLink(indexSplits[a], indexSplits[b])

# ---- RFC-0016 INT-57: an integer's rendering, decided without strings --------
#
# `$v` of a bit-vector `v` (`iekIntToStr`) is the Z3 term
# `ite(v < 0, "-" ++ str.from_int(-v), str.from_int(v))`. Its length, or a
# string order or equality between two such renderings, put to Z3 as string
# terms is decided by the sequence solver, whose step counter stopped
# advancing on `len($t) + t + 129 <= 3` (a 900 s kill under the pin settings,
# which run with no wall clock). Each is a function of `v` alone, and `v`
# ranges over at most 2^64 values whose decimal digits Nim renders with a
# leading `-` for a negative value (`$low(int)` is `-9223372036854775808`), so
# each is restated here as a bit-vector formula, exact for every value: the
# digit count is an `ite` chain over `v`'s powers-of-ten thresholds, and the
# byte order of two renderings is that of their magnitudes' digit strings,
# which is the order of `(m * 10^(L - digits(m)), m)` (the digit string padded
# on the right with zeros to `L` digits, its length breaking a tie: a shorter
# string equal so far is a prefix, and a prefix sorts first). `'-'` (0x2D)
# sorts before every digit. A term that is not a registered rendering keeps
# the string lowering.

type IntRender = object
  term: Z3String     ## the rendering (held: its address keys `intRenders`)
  v: Z3AnyAst        ## the bit-vector it renders
  width: int
  signed: bool

var intRenders {.threadvar.}: Table[uint, IntRender]
  ## RFC-0016 INT-57. Every `$v` of a bit-vector lowered this run, keyed by
  ## the rendering term's address (the entry holds the term, so the address
  ## is not reused while it is listed, as `intOfBV`'s are).

proc registerIntRender*(term: Z3String; v: Z3AnyAst; width: int;
                        signed: bool) =
  ## RFC-0016 INT-57. `term` is `$v`, `v` a `width`-bit bit-vector.
  if width notin [8, 16, 32, 64]: return
  intRenders[cast[uint](cast[pointer](term.raw))] =
    IntRender(term: term, v: v, width: width, signed: signed)

proc renderOf(t: Z3String): Option[IntRender] =
  let k = cast[uint](cast[pointer](t.raw))
  if k in intRenders and
     cast[pointer](intRenders[k].term.raw) == cast[pointer](t.raw):
    return some(intRenders[k])

proc digitCount(x: uint64): int =
  var y = x
  result = 1
  while y >= 10'u64:
    y = y div 10'u64
    inc result

proc pow10Text(k: int): string = "1" & repeat('0', k)

proc maxMagnitude(r: IntRender): uint64 =
  ## The largest magnitude `r` renders: `2^(w-1)` (`low`) signed, `2^w - 1`.
  if r.signed: 1'u64 shl (r.width - 1)
  elif r.width == 64: high(uint64)
  else: (1'u64 shl r.width) - 1

proc bvNum(ctx: Z3Context; text: string; width: int): Z3AnyAst =
  let s = ctx.checkErr Z3_mk_bv_sort(ctx.raw, cuint(width))
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw, text.cstring, s))

proc rbool(ctx: Z3Context; raw: RawZ3Ast): Z3Bool = wrap[Z3Bool](ctx, raw)

proc isNeg(ctx: Z3Context; r: IntRender): Z3Bool =
  if not r.signed: return mkBool(ctx, false)
  rbool(ctx, ctx.checkErr Z3_mk_bvslt(ctx.raw, r.v.raw,
                                      bvNum(ctx, "0", r.width).raw))

proc renderLen(ctx: Z3Context; r: IntRender): Z3Int =
  ## `len($v)`: the digit count of `v`'s magnitude, one more when negative.
  proc chain(ctx: Z3Context; top: int; below: proc (k: int): Z3Bool): Z3Int =
    result = mkInt(ctx, top)
    for k in countdown(top - 1, 1):
      result = ite(below(k), mkInt(ctx, k), result)
  let w = r.width
  let v = r.v
  if not r.signed:
    return chain(ctx, digitCount(maxMagnitude(r)), proc (k: int): Z3Bool =
      rbool(ctx, ctx.checkErr Z3_mk_bvult(ctx.raw, v.raw,
                                          bvNum(ctx, pow10Text(k), w).raw)))
  let posLen = chain(ctx, digitCount(maxMagnitude(r) - 1),
    proc (k: int): Z3Bool =
      rbool(ctx, ctx.checkErr Z3_mk_bvslt(ctx.raw, v.raw,
                                          bvNum(ctx, pow10Text(k), w).raw)))
  let negLen = chain(ctx, digitCount(maxMagnitude(r)),
    proc (k: int): Z3Bool =
      rbool(ctx, ctx.checkErr Z3_mk_bvsgt(ctx.raw, v.raw,
                                          bvNum(ctx, "-" & pow10Text(k), w).raw)))
  ite(isNeg(ctx, r), mkInt(ctx, 1) + negLen, posLen)

proc magnitude(ctx: Z3Context; r: IntRender; width: int): Z3AnyAst =
  ## `|v|` as an unsigned `width`-bit vector (`-low` is `2^(w-1)` unsigned).
  var m = r.v
  if r.signed:
    let neg = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_bvneg(ctx.raw, r.v.raw))
    m = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_ite(ctx.raw,
      isNeg(ctx, r).raw, neg.raw, r.v.raw))
  if width > r.width:
    m = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_zero_ext(ctx.raw,
      cuint(width - r.width), m.raw))
  m

proc lexKey(ctx: Z3Context; m: Z3AnyAst; L, width: int): Z3AnyAst =
  ## `m * 10^(L - digits(m))`: `m`'s digit string padded right to `L` digits.
  ## The pad `e = L - digits(m)` is a small bit-vector (an `ite` chain over
  ## `m`'s thresholds), and `m` is scaled by `10^(2^i)` for each set bit `i`
  ## of `e`: about `log2(L)` constant multiplications a side, not one per
  ## digit count. One full-width product per digit count (19 a side over two
  ## 64-bit renderings) stalled Z3's step counter on `$a < $b` alone, and
  ## narrowing each product to the bits its branch leaves `m` still took Z3
  ## 2.3 s on a bare solver against 0.5 s for this form. Every partial
  ## product divides the key, so none overflows `width`.
  const ew = 8
  var e = bvNum(ctx, "0", ew)
  for k in countdown(L - 1, 1):
    let below = rbool(ctx, ctx.checkErr Z3_mk_bvult(ctx.raw, m.raw,
                                         bvNum(ctx, pow10Text(k), width).raw))
    e = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_ite(ctx.raw, below.raw,
      bvNum(ctx, $(L - k), ew).raw, e.raw))
  let one = bvNum(ctx, "1", 1)
  result = m
  var i = 0
  while (1 shl i) <= L - 1:
    let bit = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_extract(ctx.raw, cuint(i),
                                                              cuint(i), e.raw))
    let isSet = rbool(ctx, ctx.checkErr Z3_mk_eq(ctx.raw, bit.raw, one.raw))
    let scaled = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_bvmul(ctx.raw,
      result.raw, bvNum(ctx, pow10Text(1 shl i), width).raw))
    result = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_ite(ctx.raw, isSet.raw,
                                                         scaled.raw, result.raw))
    inc i

proc renderCmp*(a, b: Z3String; op: IRBinop): Option[Z3Bool] =
  ## RFC-0016 INT-57. `a op b` (`==`, `!=`, `<`, `<=`, `>`, `>=`, the byte
  ## order Nim's `cmp` gives) when `a` and `b` are both renderings of
  ## bit-vectors, as a bit-vector formula; `none` otherwise.
  if op notin {bEq, bNe, bLt, bLe, bGt, bGe}: return
  let ra = renderOf(a)
  let rb = renderOf(b)
  if ra.isNone or rb.isNone: return
  if op in {bGt, bGe}:
    return renderCmp(b, a, if op == bGt: bLt else: bLe)
  let ctx = a.ctx
  let x = ra.get
  let y = rb.get
  let L = max(digitCount(maxMagnitude(x)), digitCount(maxMagnitude(y)))
  # bits for `10^L - 1` (a padded key) and one to spare
  let width = (L * 33220 + 9999) div 10000 + 1
  let mx = magnitude(ctx, x, width)
  let my = magnitude(ctx, y, width)
  let nx = isNeg(ctx, x)
  let ny = isNeg(ctx, y)
  let sameMag = rbool(ctx, ctx.checkErr Z3_mk_eq(ctx.raw, mx.raw, my.raw))
  if op in {bEq, bNe}:
    let eq = (nx == ny) and sameMag
    return some(if op == bEq: eq else: not eq)
  let kx = lexKey(ctx, mx, L, width)
  let ky = lexKey(ctx, my, L, width)
  let keyLt = rbool(ctx, ctx.checkErr Z3_mk_bvult(ctx.raw, kx.raw, ky.raw))
  let keyEq = rbool(ctx, ctx.checkErr Z3_mk_eq(ctx.raw, kx.raw, ky.raw))
  let tie = if op == bLt:
              rbool(ctx, ctx.checkErr Z3_mk_bvult(ctx.raw, mx.raw, my.raw))
            else:
              rbool(ctx, ctx.checkErr Z3_mk_bvule(ctx.raw, mx.raw, my.raw))
  let lex = keyLt or (keyEq and tie)
  some(ite(nx and not ny, mkBool(ctx, true),
           ite(ny and not nx, mkBool(ctx, false), lex)))

const z3OpIte = 0x104
  ## `Z3_OP_ITE` in `z3_api.h`'s `Z3_decl_kind` (`Z3_OP_TRUE` 0x100, `FALSE`,
  ## `EQ`, `DISTINCT`, `ITE`), the same in every Z3 nelli links. nim-z3's
  ## `Z3DeclKindFFI` declares only the proof rules, so the kind is read as its
  ## ordinal (`heap_model.nim` does the same).

proc isIteApp*(ctx: Z3Context; t: RawZ3Ast): bool =
  ## RFC-0016 INT-57. `t` is an application of Z3's `ite`, by its declaration
  ## kind, not its display name.
  if Z3_get_ast_kind(ctx.raw, t) != Z3_APP_AST: return false
  let app = Z3_to_app(ctx.raw, t)
  Z3_get_app_num_args(ctx.raw, app) == 3 and
    ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app))) == z3OpIte

proc litCases(t: Z3String; budget: var int):
    Option[seq[tuple[c: Z3Bool, s: string]]] =
  ## The literal values `t` takes, each with its condition, when `t` is a
  ## tree of `ite`s over string literals (a merged `$b`, `$e`); `none` past
  ## `budget` leaves or at any other term.
  let ctx = t.ctx
  let lit = literalLen(t)
  if lit >= 0:
    let bytes = literalStringBytes(t)
    if not bytes.ok: return
    dec budget
    if budget < 0: return
    return some(@[(c: mkBool(ctx, true), s: bytes.s)])
  if not isIteApp(ctx, t.raw): return
  let (_, args) = unpackApp(t)
  let c = asZ3Bool(args[0])
  let th = litCases(wrap[Z3String](ctx, args[1].raw), budget)
  if th.isNone: return
  let el = litCases(wrap[Z3String](ctx, args[2].raw), budget)
  if el.isNone: return
  var res: seq[tuple[c: Z3Bool, s: string]]
  for x in th.get: res.add (c: c and x.c, s: x.s)
  for x in el.get: res.add (c: (not c) and x.c, s: x.s)
  some(res)

proc isConcatApp(ctx: Z3Context; t: RawZ3Ast): bool =
  ## RFC-0016 INT-57. `t` is a string concatenation (`str.++`), by its
  ## declaration kind. `Z3_OP_SEQ_CONCAT` has no fixed ordinal across the Z3
  ## builds nelli links (it follows an unnumbered run of the enum), so the
  ## kind is read off a concatenation built here.
  if Z3_get_ast_kind(ctx.raw, t) != Z3_APP_AST: return false
  let app = Z3_to_app(ctx.raw, t)
  if Z3_get_app_num_args(ctx.raw, app) < 2: return false
  let probe = mkStringVar(ctx, "__int57_cat_a") & mkStringVar(ctx, "__int57_cat_b")
  let pk = Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw,
                                                     Z3_to_app(ctx.raw, probe.raw)))
  Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app)) == pk

proc strLenOpt(t: Z3String): Option[Z3Int] =
  ## `len(t)` without the string when `t` is a rendering (`renderLen`), a
  ## literal, or an `ite` tree over those; a concatenation with such a part
  ## (`"ab" & $t`, `s.add $t`) is the sum of its parts' lengths, the others
  ## kept as `str.len` (the theory's own identity); `none` otherwise.
  let ctx = t.ctx
  let r = renderOf(t)
  if r.isSome: return some(renderLen(ctx, r.get))
  let lit = literalLen(t)
  if lit >= 0: return some(mkInt(ctx, lit))
  if isConcatApp(ctx, t.raw):
    let (_, parts) = unpackApp(t)
    var any = false
    var sum = mkInt(ctx, 0)
    for i, part in parts:
      let ps = wrap[Z3String](ctx, part.raw)
      let o = strLenOpt(ps)
      if o.isSome and literalLen(ps) < 0: any = true
      let l = if o.isSome: o.get else: len(ps)
      sum = if i == 0: l else: sum + l
    if any: return some(sum)
    return
  if not isIteApp(ctx, t.raw): return
  let (_, args) = unpackApp(t)
  let th = strLenOpt(wrap[Z3String](ctx, args[1].raw))
  if th.isNone: return
  let el = strLenOpt(wrap[Z3String](ctx, args[2].raw))
  if el.isNone: return
  some(ite(asZ3Bool(args[0]), th.get, el.get))

proc strLenOf*(t: Z3String): Z3Int =
  ## RFC-0016 INT-57. `len(t)`, restated without the string when `t` is a
  ## rendering of a bit-vector or an `ite` tree over renderings and
  ## literals (`strLenOpt`), else `str.len(t)`. Exact either way.
  let o = strLenOpt(t)
  if o.isSome: o.get else: len(t)

proc litCmp*(a, b: Z3String; op: IRBinop): Option[Z3Bool] =
  ## RFC-0016 INT-57. `a op b` by cases when each of `a` and `b` takes one
  ## of a few literal values (`litCases`; a merged `$b` or `$e`, at most 16
  ## pairs), the order Nim's `cmp` gives decided here; `none` otherwise.
  if op notin {bEq, bNe, bLt, bLe, bGt, bGe}: return
  if literalLen(a) >= 0 and literalLen(b) >= 0: return
  var budget = 4
  let ca = litCases(a, budget)
  if ca.isNone: return
  budget = 4
  let cb = litCases(b, budget)
  if cb.isNone: return
  var res = mkBool(a.ctx, false)
  for x in ca.get:
    for y in cb.get:
      let c = cmp(x.s, y.s)
      let holds = case op
        of bEq: c == 0
        of bNe: c != 0
        of bLt: c < 0
        of bLe: c <= 0
        of bGt: c > 0
        else: c >= 0
      if holds: res = res or (x.c and y.c)
  some(res)

proc resetStringSupport*() =
  ## The per-run reset of the split registry. `notInFormOverride` is a test
  ## hook and `linkedNotInForm` a probe of the linked Z3 (the same in every
  ## run), so neither is reset.
  indexSplits = @[]                      ## RFC-0005 S8ag: reset indexof splits
  indexSplitOf = (ctx: Z3Context(nil), ids: initTable[int, int]())  ## RFC-0005 S8ag
  indexSplitCounter = 0                  ## RFC-0005 S8ag: reset split fresh-name counter
  intRenders = initTable[uint, IntRender]()  ## RFC-0016 INT-57: the run's renderings

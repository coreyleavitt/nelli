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

proc resetStringSupport*() =
  ## The per-run reset of the split registry. `notInFormOverride` is a test
  ## hook and `linkedNotInForm` a probe of the linked Z3 (the same in every
  ## run), so neither is reset.
  indexSplits = @[]                      ## RFC-0005 S8ag: reset indexof splits
  indexSplitOf = (ctx: Z3Context(nil), ids: initTable[int, int]())  ## RFC-0005 S8ag
  indexSplitCounter = 0                  ## RFC-0005 S8ag: reset split fresh-name counter

## RFC-0005 (soundness channels) slice S8ai -- S8ae's remainder.
##
## `checkCapped`'s step 1c checks a query that step 1 found UNSAT under the
## `maxSeqLen` caps with no sequence theory, plus `seqRangeFacts`: facts
## each valid in the theory. It checks them first without the caps (an
## UNSAT is the query's own), then with them (an UNSAT is the cap's: a
## decline, with no sequence-theory search, RFC-0005 S8r / S8v / S8ae).
##
## (1) S8ae's links between two functions were syntactic: a needle or
##     haystack matched only through the same AST. A needle equal to
##     another through a chain of equalities (`y = t`), a haystack equal to
##     another, or a computed term equal to a literal got no link, so a
##     query refuted only through the relation stayed a cap decline. The
##     links now match by the query's equality classes, each guarded by the
##     equality it rests on, so every fact stays valid in the theory.
## (2) No fact related `str.replace_all`, regex membership, `str.from_int`,
##     `str.indexof` from a nonzero start (the converse direction) or word
##     equations (`x = a ++ b`) to anything. Each now has its own valid
##     facts, and the validity check is shown to catch a broken one.
## (3) A query holding a `seq.last_indexof` skipped step 1c and went to
##     the uncapped step 3, the one place the uncapped sequence theory still
##     ran. It now takes step 1c, with `last_indexof` links, first.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

const decls = """
(declare-const s String) (declare-const t String) (declare-const u String)
(declare-const x String) (declare-const y String) (declare-const z String)
(declare-const a String) (declare-const b String) (declare-const r String)
(declare-const n Int) (declare-const i Int) (declare-const j Int)
"""

proc q(ctx: Z3Context; src: string): seq[Z3Bool] =
  ## The assertions of `src`, over the constants of `decls` (the same ASTs
  ## `mkStringVar` / `mkIntVar` build for those names).
  parseSmt2String(ctx, decls & src)

proc slen(ctx: Z3Context; s: Z3String): Z3Int =
  wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_length(ctx.raw, s.raw))

proc stepOneC(ctx: Z3Context; roots: seq[Z3Bool]; caps: seq[Z3Bool] = @[]):
    Z3Status =
  ## The query as step 1c poses it: no sequence theory, with the facts
  ## (built from the query alone, as `checkCapped` does), and the caps.
  let s = querySolver(ctx, roots, 1_000_000'u, seqTheory = false)
  for f in seqRangeFacts(ctx, roots): s.add f
  for c in caps: s.add c
  s.check()

proc capAt(ctx: Z3Context; names: varargs[string]): seq[Z3Bool] =
  for nm in names: result.add slen(ctx, mkStringVar(ctx, nm)) <= mkInt(ctx, 128)

proc freeConsts(ctx: Z3Context; f: Z3Bool): seq[Z3AnyAst] =
  ## The uninterpreted Int / sequence constants of `f`, each once.
  var seen: seq[int]
  var stack = @[toAnyAst(f)]
  while stack.len > 0:
    let t = stack.pop()
    if getAstKind(t) != akApp: continue
    let args = unpackApp(t).args
    if args.len == 0 and getSortKind(t) in {skInt, skSeq} and
       not Z3_is_string(ctx.raw, t.raw):
      let id = astId(ctx, t.raw)
      if id notin seen:
        seen.add id
        result.add t
    for a in args: stack.add a

proc holdsOnSmallDomain(ctx: Z3Context; f: Z3Bool): string =
  ## "" when `f` evaluates to `true` (Z3's own rewriter on ground terms)
  ## for every string over {"a", "\xff"} of length <= 3 and every integer
  ## in -1..4 substituted for its constants; else the first instance that
  ## does not.
  var strs = @[""]
  var frontier = @[""]
  for _ in 1 .. 3:
    var next: seq[string]
    for w in frontier:
      for c in ["a", "\xff"]: next.add w & c
    strs.add next
    frontier = next
  let vars = freeConsts(ctx, f)
  if vars.len == 0: return ""
  var froms, tos: seq[RawZ3Ast]
  for v in vars:
    froms.add v.raw
    tos.add v.raw
  proc go(k: int): string =
    if k == vars.len:
      let g = ctx.checkErr Z3_simplify(ctx.raw, ctx.checkErr Z3_substitute(
        ctx.raw, f.raw, cuint(froms.len),
        cast[ptr UncheckedArray[RawZ3Ast]](froms[0].addr),
        cast[ptr UncheckedArray[RawZ3Ast]](tos[0].addr)))
      let txt = $Z3_ast_to_string(ctx.raw, g)
      return (if txt == "true": "" else: txt)
    if getSortKind(vars[k]) == skInt:
      for v in -1 .. 4:
        tos[k] = mkInt(ctx, v).raw
        let r = go(k + 1)
        if r.len > 0: return r
    else:
      for w in strs:
        tos[k] = mkString(ctx, w).raw
        let r = go(k + 1)
        if r.len > 0: return r
    ""
  go(0)

proc factFlaw(ctx: Z3Context; f: Z3Bool; domain: seq[Z3Bool] = @[]): string =
  ## "" when `f` passes both validity checks against the linked Z3's own
  ## semantics: its negation (beside the byte-domain roots `domain`) is
  ## never SAT with the sequence theory, and it is `true` on every small
  ## ground instance (`holdsOnSmallDomain`). Otherwise what failed.
  let r = querySolver(ctx, domain & @[not f], 1_000_000'u).check()
  let cex = holdsOnSmallDomain(ctx, f)
  if r == zsSat or cex.len > 0:
    return $f & " -> " & $r & ", ground: " & cex
  ""

proc invalidFacts(ctx: Z3Context; roots: seq[Z3Bool];
                  domain: seq[Z3Bool] = @[]): tuple[n: int, bad: seq[string]] =
  ## Each fact `seqRangeFacts` emits for `roots` must hold in every model
  ## of the query, so a theory-free UNSAT stays the query's own.
  let facts = seqRangeFacts(ctx, roots)
  result.n = facts.len
  for f in facts:
    let flaw = factFlaw(ctx, f, domain)
    if flaw.len > 0: result.bad.add flaw

# ---- (1) semantic links: equal through the query's equality classes -------

proc needleByEquality(s, t: string) =
  if t == ":" and s.find(t) > 200 and ":" notin s:
    symexTarget("s8ai_needle_eq")

proc needleByEqualityFound(s, t: string) =
  if t == ":" and s.find(t) > 5 and ":" in s:
    symexTarget("s8ai_needle_eq_found")

suite "S8ai (1): step 1c's links follow the query's equality classes":

  test "a needle equal through one equality is linked":
    let ctx = newContext()
    let roots = q(ctx, """(assert (> (str.indexof s y 0) 200)) (assert (= y t))
                          (assert (not (str.contains s t)))""")
    check stepOneC(ctx, roots) == zsUnsat

  test "a needle equal through a chain of equalities is linked":
    let ctx = newContext()
    let roots = q(ctx, """(assert (> (str.indexof s y 0) 200)) (assert (= y z))
                          (assert (= t z)) (assert (not (str.contains s t)))""")
    check stepOneC(ctx, roots) == zsUnsat

  test "a haystack equal to another is linked":
    let ctx = newContext()
    let roots = q(ctx, """(assert (> (str.indexof x ":" 0) 200)) (assert (= x s))
                          (assert (not (str.contains s ":")))""")
    check stepOneC(ctx, roots) == zsUnsat

  test "a computed needle equal to a literal is linked":
    let ctx = newContext()
    let roots = q(ctx, """(assert (> (str.indexof s (str.++ "a" "b") 0) 200))
                          (assert (not (str.contains s "ab")))""")
    check stepOneC(ctx, roots) == zsUnsat

  test "a piece equal to the needle through a chain is contained":
    let ctx = newContext()
    let roots = q(ctx, """(assert (> (str.len s) 150)) (assert (= (str.at s 140) y))
                          (assert (= y ":")) (assert (not (str.contains s ":")))""")
    check stepOneC(ctx, roots) == zsUnsat

  test "companion: no equality, no link (SAT)":
    let ctx = newContext()
    let roots = q(ctx, """(assert (> (str.indexof s y 0) 200))
                          (assert (not (= y t))) (assert (not (str.contains s t)))""")
    check stepOneC(ctx, roots) == zsSat

  test "end to end: t == \":\" and s.find(t) > 200 and \":\" notin s is sxUnsat":
    let r = symexFind(needleByEquality, tLabel("s8ai_needle_eq"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "companion: t == \":\" and s.find(t) > 5 and \":\" in s is sxSat":
    let r = symexFind(needleByEqualityFound, tLabel("s8ai_needle_eq_found"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "each guarded link is valid in the sequence theory":
    let ctx = newContext()
    let roots = q(ctx, """
      (assert (>= (str.indexof s y j) (- 5))) (assert (= y z)) (assert (= z t))
      (assert (= x s)) (assert (or (str.contains x t) (str.prefixof t s)))
      (assert (or (str.suffixof y x) (= (str.at s i) z)))""")
    let (count, bad) = invalidFacts(ctx, roots)
    checkpoint bad.join("; ")
    check count >= 17
    check bad.len == 0

# ---- (2) new facts: replace_all, regex, from_int, indexof from i, words ----

suite "S8ai (2): replace_all, regex, from_int, nonzero starts, word equations":

  test "str.replace_all: same-length pieces keep the length":
    let ctx = newContext()
    check stepOneC(ctx, q(ctx, """(assert (= r (str.replace_all s "a" "b")))
                   (assert (> (str.len r) (str.len s)))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, """(assert (= r (str.replace_all s t u)))
                   (assert (= (str.len t) (str.len u)))
                   (assert (not (= (str.len r) (str.len s))))""")) == zsUnsat

  test "str.replace_all: growth is bounded by the literal lengths":
    let ctx = newContext()
    let base = """(assert (= r (str.replace_all s "a" "bb")))"""
    check stepOneC(ctx, q(ctx, base & """
                   (assert (> (str.len r) (* 2 (str.len s))))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, base & """
                   (assert (< (str.len r) (str.len s)))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, base & """
                   (assert (= (str.len r) (* 2 (str.len s))))""")) == zsSat

  test "str.replace_all: no occurrence leaves the string; past the cap":
    let ctx = newContext()
    check stepOneC(ctx, q(ctx, """(assert (= r (str.replace_all s ":" ";")))
                   (assert (not (str.contains s ":"))) (assert (not (= r s)))""")) == zsUnsat
    let far = q(ctx, """(assert (> (str.len (str.replace_all s ":" ";")) 300))""")
    check stepOneC(ctx, far, capAt(ctx, "s")) == zsUnsat
    check stepOneC(ctx, far) == zsSat

  test "str.in_re: a membership bounds the length":
    let ctx = newContext()
    let m = """(assert (str.in_re s (re.loop (re.range "a" "z") 2 5)))"""
    check stepOneC(ctx, q(ctx, m & "(assert (> (str.len s) 5))")) == zsUnsat
    check stepOneC(ctx, q(ctx, m & "(assert (< (str.len s) 2))")) == zsUnsat
    check stepOneC(ctx, q(ctx, m & "(assert (= (str.len s) 5))")) == zsSat
    let cat = """(assert (str.in_re s (re.++ (str.to_re "ab")
                   (re.union (str.to_re "x") (re.+ (re.range "0" "9"))))))"""
    check stepOneC(ctx, q(ctx, cat & "(assert (< (str.len s) 3))")) == zsUnsat
    check stepOneC(ctx, q(ctx, cat & "(assert (> (str.len s) 200))")) == zsSat
    # Past the cap: a word of at least 200 letters.
    let far = q(ctx, """(assert (str.in_re s (re.++ (re.loop (re.range "a" "z") 200 200)
                          re.all)))""")
    check stepOneC(ctx, far, capAt(ctx, "s")) == zsUnsat
    check stepOneC(ctx, far) == zsSat

  test "str.from_int: its length follows the value":
    let ctx = newContext()
    let base = "(assert (= x (str.from_int n)))"
    check stepOneC(ctx, q(ctx, base & """(assert (>= n 0)) (assert (< n 1000))
                   (assert (> (str.len x) 3))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, base & """(assert (< n 0))
                   (assert (> (str.len x) 0))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, base & """(assert (>= n 100))
                   (assert (< (str.len x) 3))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, base & """(assert (>= n 0))
                   (assert (not (= (str.to_int x) n)))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, base & """(assert (>= n 100)) (assert (< n 1000))
                   (assert (= (str.len x) 3))""")) == zsSat
    # A 64-bit value has at most 20 digits.
    check stepOneC(ctx, q(ctx, base & """(assert (< n 18446744073709551616))
                   (assert (> (str.len x) 20))""")) == zsUnsat

  test "str.indexof from a nonzero start: the converse direction":
    let ctx = newContext()
    check stepOneC(ctx, q(ctx, """(assert (>= (str.indexof s ":" 0) 5))
                   (assert (= (str.indexof s ":" 5) (- 1)))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, """(assert (>= (str.indexof s ":" 7) 0))
                   (assert (= (str.indexof s ":" 3) (- 1)))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, """(assert (str.suffixof ":" s))
                   (assert (>= (str.len s) 10))
                   (assert (= (str.indexof s ":" 4) (- 1)))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, """(assert (>= (str.indexof s ":" 0) 5))
                   (assert (= (str.indexof s ":" 6) (- 1)))""")) == zsSat

  test "word equations: a part's occurrence is the whole's":
    let ctx = newContext()
    let w = "(assert (= x (str.++ a b)))"
    check stepOneC(ctx, q(ctx, w & """(assert (str.contains a ":"))
                   (assert (not (str.contains x ":")))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, """(assert (= x (str.++ a ":" b)))
                   (assert (not (str.contains x ":")))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, w & """(assert (str.contains x ":"))
                   (assert (not (str.contains a ":")))
                   (assert (not (str.contains b ":")))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, w & """(assert (str.prefixof "ab" a))
                   (assert (not (str.prefixof "ab" x)))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, w & """(assert (str.suffixof "ab" b))
                   (assert (not (str.suffixof "ab" x)))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, w & """(assert (str.contains a ":"))
                   (assert (= (str.indexof x ":" 0) (- 1)))""")) == zsUnsat
    # Companion: a 2-byte needle can straddle the parts.
    check stepOneC(ctx, q(ctx, w & """(assert (str.contains x "ab"))
                   (assert (not (str.contains a "ab")))
                   (assert (not (str.contains b "ab")))""")) == zsSat

  test "each new fact is valid in the sequence theory":
    let ctx = newContext()
    let roots = q(ctx, """
      (assert (= r (str.replace_all s t u))) (assert (str.contains s t))
      (assert (= y (str.replace_all s "a" "\u{ff}\u{ff}")))
      (assert (= z (str.replace_all s "aa" "\u{ff}")))
      (assert (str.in_re x (re.++ (str.to_re "a") (re.loop (re.range "a" "b") 1 2))))
      (assert (= b (str.from_int n))) (assert (>= (str.to_int b) (- 3)))
      (assert (>= (str.indexof s t i) (- 3))) (assert (>= (str.indexof s t j) (- 3)))
      (assert (str.suffixof t s))""")
    let (count, bad) = invalidFacts(ctx, roots)
    checkpoint bad.join("; ")
    check count >= 40
    check bad.len == 0

  test "each word-equation fact is valid in the sequence theory":
    let ctx = newContext()
    let roots = q(ctx, """
      (assert (= x (str.++ a b))) (assert (= y (str.++ a "a" b)))
      (assert (or (str.contains x t) (str.contains a t) (str.contains b t)))
      (assert (or (str.prefixof t a) (str.prefixof t x) (str.suffixof t b)
                  (str.suffixof t x) (str.contains y "a")))
      (assert (>= (str.indexof x t i) (- 3))) (assert (>= (str.indexof y "a" j) (- 3)))""")
    let (count, bad) = invalidFacts(ctx, roots)
    checkpoint bad.join("; ")
    check count >= 31
    check bad.len == 0

  test "the validity check catches a broken fact of each kind":
    # Each is one of the facts above with its bound or direction broken.
    let ctx = newContext()
    let mutants = q(ctx, """
      (assert (=> (<= (str.len t) (str.len u))
                  (<= (str.len (str.replace_all s t u)) (str.len s))))
      (assert (=> (str.in_re x (re.loop (re.range "a" "b") 1 3)) (<= (str.len x) 2)))
      (assert (=> (>= n 0) (>= (str.len (str.from_int n)) 2)))
      (assert (=> (and (<= 0 j) (<= j i) (>= (str.indexof s t i) 0))
                  (>= (str.indexof s t j) (str.indexof s t i))))
      (assert (=> (str.contains (str.++ a b) t)
                  (or (str.contains a t) (str.contains b t))))
      (assert (=> (>= (seq.last_indexof s t) 0)
                  (< (+ (seq.last_indexof s t) (str.len t)) (str.len s))))""")
    check mutants.len == 6
    for m in mutants:
      let flaw = factFlaw(ctx, m)
      checkpoint $m
      check flaw.len > 0

# ---- (3) seq.last_indexof takes step 1c --------------------------------------

proc rfindPastCap(s: string) =
  if s.rfind(':') > 200 and ':' notin s:
    symexTarget("s8ai_rfind_notin")

proc rfindSuffix(s: string) =
  if s.len > 150 and s.endsWith(":") and s.rfind(':') != s.len - 1:
    symexTarget("s8ai_rfind_suffix")

proc rfindFound(s: string) =
  if s.rfind(':') > 3 and ':' in s:
    symexTarget("s8ai_rfind_found")

suite "S8ai (3): a query holding seq.last_indexof takes step 1c":

  test "last_indexof links: contains, pieces, suffixes":
    let ctx = newContext()
    check stepOneC(ctx, q(ctx, """(assert (> (seq.last_indexof s ":") 200))
                   (assert (not (str.contains s ":")))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, """(assert (str.contains s ":"))
                   (assert (= (seq.last_indexof s ":") (- 1)))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, """(assert (> (str.len s) 10))
                   (assert (= (str.at s 7) ":"))
                   (assert (< (seq.last_indexof s ":") 7))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, """(assert (str.suffixof ":" s))
                   (assert (not (= (seq.last_indexof s ":") (- (str.len s) 1))))""")) == zsUnsat
    check stepOneC(ctx, q(ctx, """(assert (> (seq.last_indexof s ":") 3))
                   (assert (str.contains s ":"))""")) == zsSat

  test "each last_indexof link is valid in the sequence theory":
    let ctx = newContext()
    let roots = q(ctx, """
      (assert (>= (seq.last_indexof s t) (- 3))) (assert (str.contains s t))
      (assert (or (str.prefixof t s) (str.suffixof t s) (= (str.at s i) t)))
      (assert (>= (str.indexof s t j) (- 3)))""")
    let (count, bad) = invalidFacts(ctx, roots)
    checkpoint bad.join("; ")
    check count >= 19
    check bad.len == 0

  test "end to end: rfind > 200 and notin is decided by step 1c":
    # Under a budget too small for the uncapped step 3, only step 1c's
    # facts decide it; step 3's decline says the uncapped query "was not
    # decided".
    proc tight(): SymexSettings =
      result = defaultSymexSettings()
      result.budget.seqQueryRLimit = 2_000
    let r = symexFind(rfindPastCap, tLabel("s8ai_rfind_notin"), tight())
    checkpoint show(r.errors)
    check r.status == sxUnsat
    for e in r.errors: check "was not decided" notin e.msg

  # UNSAT on its own, through one last_indexof link. Under a budget too
  # small for the uncapped step 3, only step 1c's facts decide it. RED at
  # 58e52af: "the uncapped query (it holds a seq.last_indexof) was not
  # decided". (`s[7] == ':' and rfind < 7`, and `':' in s and rfind < 0`
  # on Z3 4.13.4, are not pinned end to end: at this budget step 1 itself
  # is canceled, so step 1c is not reached. Their links are pinned above.)
  template decidedBy1c(fn: typed; label: string) =
    proc tight(): SymexSettings =
      result = defaultSymexSettings()
      result.budget.seqQueryRLimit = 2_000
    let r = symexFind(fn, tLabel(label), tight())
    checkpoint show(r.errors)
    check r.status == sxUnsat
    for e in r.errors: check "was not decided" notin e.msg

  test "end to end: endsWith and rfind != len - 1 is decided by step 1c":
    decidedBy1c(rfindSuffix, "s8ai_rfind_suffix")

  test "companion: rfind > 3 and in is sxSat":
    let r = symexFind(rfindFound, tLabel("s8ai_rfind_found"))
    checkpoint show(r.errors)
    check r.status == sxSat

suite "S8ai: walker version floor":
  test "symexWalkerVersion >= 182":
    check parseInt(symexWalkerVersion) >= 182

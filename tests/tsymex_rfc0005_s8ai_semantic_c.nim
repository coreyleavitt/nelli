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
## (2) is `tsymex_rfc0005_s8ai_semantic_b`: its validity checks ran the file
## past the 60 s per-file budget on Windows.
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8ai_semantic`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 69 s).

include ./s8ai_helpers

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
  # on Z3 4.13.4, were not pinned end to end here: at this budget step 1
  # itself is canceled, so step 1c was not reached. Their links are
  # pinned above; both are now pinned end to end too, by RFC-0005 S8aq,
  # which gives step 1c a path that does not depend on step 1 reaching
  # UNSAT -- `tsymex_rfc0005_s8aq_remainder.nim`, suite "S8aq (1)".)
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

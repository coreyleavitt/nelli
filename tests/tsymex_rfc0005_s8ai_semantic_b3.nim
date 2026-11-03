## RFC-0005 (soundness channels) slice S8ai, part (2): facts for
## `str.replace_all`, regex membership, `str.from_int`, `str.indexof` from a
## nonzero start and word equations. The header is
## `tsymex_rfc0005_s8ai_semantic`, split from it in RFC-0005 batch 8.
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8ai_semantic_b`, `tsymex_rfc0005_s8ai_semantic_b2`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 70 s).

include ./s8ai_helpers

# ---- (2) new facts: replace_all, regex, from_int, indexof from i, words ----

suite "S8ai (2): replace_all, regex, from_int, nonzero starts, word equations":
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

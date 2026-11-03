## RFC-0005 (soundness channels) slice S8ai, part (2): facts for
## `str.replace_all`, regex membership, `str.from_int`, `str.indexof` from a
## nonzero start and word equations. The header is
## `tsymex_rfc0005_s8ai_semantic`, split from it in RFC-0005 batch 8.
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8ai_semantic_b`, `tsymex_rfc0005_s8ai_semantic_b3`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 70 s).

include ./s8ai_helpers

# ---- (2) new facts: replace_all, regex, from_int, indexof from i, words ----

suite "S8ai (2): replace_all, regex, from_int, nonzero starts, word equations":
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

## RFC-0005 (soundness channels) slice S8ai, part (2): facts for
## `str.replace_all`, regex membership, `str.from_int`, `str.indexof` from a
## nonzero start and word equations. The header is
## `tsymex_rfc0005_s8ai_semantic`, split from it in RFC-0005 batch 8.
include ./s8ai_helpers

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

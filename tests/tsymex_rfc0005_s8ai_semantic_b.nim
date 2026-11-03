## RFC-0005 (soundness channels) slice S8ai, part (2): facts for
## `str.replace_all`, regex membership, `str.from_int`, `str.indexof` from a
## nonzero start and word equations. The header is
## `tsymex_rfc0005_s8ai_semantic`, split from it in RFC-0005 batch 8.
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8ai_semantic_b2`, `tsymex_rfc0005_s8ai_semantic_b3`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 70 s).

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

## RFC-0005 (soundness channels) slice S8cn, item 1 -- step 1d can turn a
## decline into `sxUnsat`, so it is held to adversarial pins.
##
## Step 1d (batch 8) answers UNSAT when the query with no sequence theory, plus
## the facts, has no model breaking a cap: every real model keeps to the caps,
## and step 1 refuted those. It stands on two things, each pinned here against
## native runs:
##   - `not all` is the negation of EVERY cap (a query that bounds one string
##     and leaves another past the cap must not answer);
##   - every fact is valid in Nim's byte-faithful string model (a fact that cut
##     a real model would refute the query's own past-the-cap model). The audit
##     is in the RFC's "As landed (S8cn)"; each family is checked here under
##     `invalidFacts`, over strings that hold `\x00` and `\xff`.
## Each query below reaches step 1d (the step table says so), on both Z3s. The
## pins were green when written: the two mutations named in the RFC's note turn
## them red (a false `sxUnsat`).
##
## RFC-0005 S8cm: part 4 of 6 of this suite, with `tsymex_rfc0005_s8cn_step1d`,
## `tsymex_rfc0005_s8cn_step1d_b`, `tsymex_rfc0005_s8cn_step1d_c`,
## `tsymex_rfc0005_s8cn_step1d_e`, `tsymex_rfc0005_s8cn_step1d_f`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 118 s).
import std/[re, tables]
include s8ai_helpers

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8cn_step1d needs -d:symexQueryStats (its .nim.cfg)".}

suite "S8cn (1): every family of facts, under `invalidFacts`":

  template allValid(src: string; domain: seq[Z3Bool] = @[]) =
    block:
      let ctx = newContext()
      let roots = q(ctx, src)
      let res = invalidFacts(ctx, roots, domain)
      checkpoint src
      checkpoint res.bad.join("\n")
      check res.n > 0
      check res.bad.len == 0


  test "replace_all":
    allValid("""(assert (= (str.len (str.replace_all s t u)) 1))
      (assert (str.contains s t))""")
    allValid("""(assert (= (str.len (str.replace_all s "aa" "a")) 1))""")
    allValid("""(assert (= (str.len (str.replace_all s "a" "aa")) 1))""")
    allValid("""(assert (= (str.len (str.replace_all s "" "a")) 1))""")

  test "from_int, to_int":
    allValid("""(assert (= (str.from_int n) x))
      (assert (>= (str.to_int x) 0))""")

  test "regex length bounds":
    allValid("""(assert (str.in_re s (re.++ (str.to_re "ab") (re.opt (str.to_re "c")))))""")
    allValid("""(assert (str.in_re s (re.union (str.to_re "a") (str.to_re "bcd"))))""")
    allValid("""(assert (str.in_re s ((_ re.loop 1 3) (str.to_re "ab"))))""")
    allValid("""(assert (str.in_re s ((_ re.^ 2) (re.range "a" "b"))))""")
    allValid("""(assert (str.in_re s (re.+ (str.to_re "ab"))))""")
    allValid("""(assert (str.in_re s (re.inter (re.* re.allchar) (str.to_re "ab"))))""")

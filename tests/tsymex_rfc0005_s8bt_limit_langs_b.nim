## RFC-0005 S8bt (item 3) -- a `(*LIMIT_MATCH=)` / `(*LIMIT_RECURSION=)`
## between 0 and PCRE's default, symbolically: the attempt's languages
## (`lkErrM`, `lkErrR`, `lkMark`, `lkNone`), the search's (`skErrM`,
## `skErrR` and their marked forms, `skNoOcc`, `skFirst`) and the step
## table's `replace` against the concrete reference (`pcreExec`, pinned
## against libpcre by `tsymex_rfc0005_s8bt_limit`), in every start
## variant; the Z3 `replace` term; and the walker's verdicts.
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8bt_limit_langs`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 60 s).
import std/[unittest, strutils, times, re]
import z3
import nelli/symex
import nelli/smt/types
import nelli/smt/[pcre_syntax, pcre_select, regex_parser]
import nelli/smt/pcre_engine
import ./s8bt_harness/[member, stepref, limit_oracle]
import ./s8cu_helpers

proc findErrTarget(s: string) =
  if s.len <= 4 and s.find(re"(*LIMIT_MATCH=6)(?:a|b)*c") == -8:
    symexTarget("bt_limit_find_err")

proc findNeverTarget(s: string) =
  # libpcre: no subject of length 6 or less makes this call an error.
  if s.len <= 6 and s.find(re"(*LIMIT_MATCH=4)a+b") == -8:
    symexTarget("bt_limit_find_never")

proc findOkTarget(s: string) =
  if s.len <= 6 and s.find(re"(*LIMIT_MATCH=4)a+b") == 1:
    symexTarget("bt_limit_find_ok")

proc matchLenTarget(s: string) =
  if s.len <= 4 and s.matchLen(re"(*LIMIT_RECURSION=3)(?:a|b)*c") == -21:
    symexTarget("bt_limit_matchlen")

proc matchLenNeverTarget(s: string) =
  # libpcre: no subject of length 4 or less makes this call an error.
  if s.len <= 4 and s.matchLen(re"(*LIMIT_RECURSION=2)a+b|ab") == -21:
    symexTarget("bt_limit_matchlen_never")

proc replaceTarget(s: string) =
  if s.len == 1 and s.replace(re"(*LIMIT_MATCH=6)(?:a|b)*c", "-") == "-":
    symexTarget("bt_limit_replace")

proc replaceConcreteTarget(s: string) =
  # The same call on the subject that reaches it: "c" is "-" under the limit.
  if s == "c" and s.replace(re"(*LIMIT_MATCH=6)(?:a|b)*c", "-") == "-":
    symexTarget("bt_limit_replace_c")

proc replaceErrTarget(s: string) =
  # A limit error ends `replace` as a miss does: the subject comes back
  # ("ac" is "-" without the limit).
  if s == "ac" and s.replace(re"(*LIMIT_MATCH=6)(?:a|b)*c", "-") != "ac":
    symexTarget("bt_limit_replace_err")

suite "S8bt: a limit between, through the walker":

  template verdict(sut: untyped; label: string; want = sxSat) =
    let t1 = epochTime()
    let r = symexFind(sut, tLabel(label))
    echo "  ", label, ": ", r.status, " ", formatFloat(epochTime() - t1,
                                                       ffDecimal, 1), " s"
    check r.status == want

  test "an anchored call: sxSat, and sxUnsat where libpcre has none":
    verdict(matchLenTarget, "bt_limit_matchlen")
    verdict(matchLenNeverTarget, "bt_limit_matchlen_never", sxUnsat)

  # An unanchored call on the JIT (the Windows legs): its own accounting.
  test "unanchored calls: on the interpreter, and on the JIT":
    if pcreSearchEngine() == peInterp:
      verdict(findErrTarget, "bt_limit_find_err")
      verdict(findOkTarget, "bt_limit_find_ok")
      verdict(findNeverTarget, "bt_limit_find_never", sxUnsat)
      # A subject that is free but for its length: Z3 5.1 finds "c", Z3 4.13.4
      # in the query's own context (S8bp) through step 1e (RFC-0005 S8cn).
      verdict(replaceTarget, "bt_limit_replace")
      # RFC-0016 PRC-27: the same verdict as an exact K9 pin (the witness
      # replays natively through std/re).
      discard pinExact(replaceTarget, cellKey(faCallShape, "pcre/limitReplace"),
                       tLabel("bt_limit_replace"),
                       domain = sampled(["", "a", "c", "ac", "bc"]))
      verdict(replaceConcreteTarget, "bt_limit_replace_c")
      check "c".replace(re"(*LIMIT_MATCH=6)(?:a|b)*c", "-") == "-"
      verdict(replaceErrTarget, "bt_limit_replace_err", sxUnsat)
    else:
      # RFC-0005 S8cf (item 3): read off `count_match`'s sites. Up to 4 bytes the
      # JIT stays under this limit: native says so, and so does the walker.
      let rx = re"(*LIMIT_MATCH=6)(?:a|b)*c"
      var stops = 0
      var fr = @[""]
      for _ in 0 .. 4:
        var nx: seq[string]
        for w in fr:
          if find(w, rx) == -8: inc stops
          for c in "abc": nx.add w & c
        fr = nx
      check stops == 0
      verdict(findErrTarget, "bt_limit_find_err", sxUnsat)
      verdict(replaceErrTarget, "bt_limit_replace_err", sxSat)

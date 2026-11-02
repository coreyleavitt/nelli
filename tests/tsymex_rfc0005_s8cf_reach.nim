## RFC-0005 S8cf (items 1, 2; SOUNDNESS) -- `pcre_select.limitReach` against
## native PCRE: a subject no longer than the bound the model states never
## makes std/re report a limit.
import std/[unittest, re, strutils]
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select

proc reach(p: string): LimitReach = limitReach(parsePcre(p, false))

suite "S8cf: limitReach":
  test "patterns whose calls do not grow with the subject":
    for p in ["a", "a*", "[ab]+", "a|b", "abc", "a{2,5}", "x*?", "a*b"]:
      checkpoint p
      check reach(p).never

  test "patterns whose calls grow":
    for p in [".*b", "[ab]*a", "(a|b)*c", "(a|a)*[bc]", "(?:ab)+c"]:
      checkpoint p
      check not reach(p).never

  test "exponential patterns have a short bound":
    let r = reach("(a|a)*[bc]")
    checkpoint $r.safe
    check r.safe < 30
    check r.safe >= 10

  test "native: no limit error at the bound":
    for p in ["(a|a)*[bc]", "(a|aa)*[bc]", "(a|b|ab)*[cd]", "a*a*a*a*[bc]",
              "(a*)*[bc]", "(a+)+[bc]", "(?:a|a)*?[bc]"]:
      let r = reach(p)
      let rx = re(p)
      checkpoint p & " safe " & $r.safe
      check not r.never
      for n in [r.safe, max(r.safe - 1, 0)]:
        let got = find('a'.repeat(n), rx)
        check got >= -1

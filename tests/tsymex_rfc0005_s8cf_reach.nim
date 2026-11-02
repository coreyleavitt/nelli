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

  test "native: stacks at the bound, on mixed subjects":
    # RFC-0005 S8cf (item 2): a group's frames, and the JIT's own stack (-27).
    # Past the frame budget the interpreter's stack ends in SIGSEGV, so a bound
    # past it stops this test.
    for p in ["(a|b)*c", "(a)*c", "(?:a|b)*c", "(?:ab)*c", "(?:ab)+c", "(a|b)+c",
              "(ab|a)*c", "(?:ab|a)+c", "(?:a|b)*?c", "(a|b){2,}c"]:
      let r = reach(p)
      let rx = re(p)
      checkpoint p & " safe " & $r.safe & " never " & $r.never
      if r.never: continue
      check r.safe >= 8
      let n = r.safe
      for s in ['a'.repeat(n), "ab".repeat(n div 2), "aab".repeat(n div 3),
                'a'.repeat(n - 1) & 'c', 'b'.repeat(n)]:
        check s.len <= n
        check find(s, rx) >= -1
        check matchLen(s, rx) >= -1

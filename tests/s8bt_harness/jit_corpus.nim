## RFC-0005 S8bt -- the JIT corpus: patterns whose unanchored calls PCRE
## 8.37's JIT (the Windows legs' library) runs with its own start-of-match
## scan (`pcre_jit.nim`), shared by the oracle harness (`jit_oracle.nim`,
## run against a JIT build of 8.37 and its interpreter build) and the test
## (`tsymex_rfc0005_s8bt_jit*.nim`).
import std/strutils

const known212* = [
  r"(*ANY)\s(*SKIP)(?:ab|a)", r"(*ANY)\s(*SKIP)(?:a|ab)",
  r"(*ANY)\s(*SKIP).", r"(*ANY)\s(*SKIP)[ab]", r"(*ANY)\s(*SKIP)a",
  r"(*ANY)\s(*SKIP)a+", r"(*ANY)\s(*SKIP)b", r"(*ANY)\s(?:ab|a)(*ACCEPT)",
  r"(*ANY)\s(?:ab|a)(*COMMIT)", r"(*ANY)\s(?:ab|a)(*MARK:A)",
  r"(*ANY)\s(?:ab|a)(*PRUNE)", r"(*ANY)\s(?:ab|a)(*PRUNE:A)",
  r"(*ANY)\s(?:ab|a)(*SKIP)", r"(*ANY)\s(?:ab|a)(*SKIP:A)",
  r"(*ANY)\s(?:ab|a)(*THEN)", r"(*ANY)\s(?:ab|a)(*THEN:A)",
  r"(*ANY)\s(?:a|ab)(*ACCEPT)", r"(*ANY)\s(?:a|ab)(*COMMIT)",
  r"(*ANY)\s(?:a|ab)(*MARK:A)", r"(*ANY)\s(?:a|ab)(*PRUNE)",
  r"(*ANY)\s(?:a|ab)(*PRUNE:A)", r"(*ANY)\s(?:a|ab)(*SKIP)",
  r"(*ANY)\s(?:a|ab)(*SKIP:A)", r"(*ANY)\s(?:a|ab)(*THEN)",
  r"(*ANY)\s(?:a|ab)(*THEN:A)", r"(*ANY)\sa(*ACCEPT)", r"(*ANY)\sa(*COMMIT)",
  r"(*ANY)\sa(*MARK:A)", r"(*ANY)\sa(*PRUNE)", r"(*ANY)\sa(*PRUNE:A)",
  r"(*ANY)\sa(*SKIP)", r"(*ANY)\sa(*SKIP:A)", r"(*ANY)\sa(*THEN)",
  r"(*ANY)\sa(*THEN:A)", r"(*ANY)\sa+(*ACCEPT)", r"(*ANY)\sa+(*COMMIT)",
  r"(*ANY)\sa+(*MARK:A)", r"(*ANY)\sa+(*PRUNE)", r"(*ANY)\sa+(*PRUNE:A)",
  r"(*ANY)\sa+(*SKIP)", r"(*ANY)\sa+(*SKIP:A)", r"(*ANY)\sa+(*THEN)",
  r"(*ANY)\sa+(*THEN:A)", r"(*ANY)\sb(*ACCEPT)", r"(*ANY)\sb(*COMMIT)",
  r"(*ANY)\sb(*MARK:A)", r"(*ANY)\sb(*PRUNE)", r"(*ANY)\sb(*PRUNE:A)",
  r"(*ANY)\sb(*SKIP)", r"(*ANY)\sb(*SKIP:A)", r"(*ANY)\sb(*THEN)",
  r"(*ANY)\sb(*THEN:A)", r"(*ANYCRLF)(?:\s(?:a|ab)a?)+",
  r"(*ANYCRLF)\s(*SKIP)(?:ab|a)", r"(*ANYCRLF)\s(*SKIP)(?:a|ab)",
  r"(*ANYCRLF)\s(*SKIP).", r"(*ANYCRLF)\s(*SKIP)[ab]",
  r"(*ANYCRLF)\s(*SKIP)a", r"(*ANYCRLF)\s(*SKIP)a+", r"(*ANYCRLF)\s(*SKIP)b",
  r"(*ANYCRLF)\s(?:ab|a)(*ACCEPT)", r"(*ANYCRLF)\s(?:ab|a)(*COMMIT)",
  r"(*ANYCRLF)\s(?:ab|a)(*MARK:A)", r"(*ANYCRLF)\s(?:ab|a)(*PRUNE)",
  r"(*ANYCRLF)\s(?:ab|a)(*PRUNE:A)", r"(*ANYCRLF)\s(?:ab|a)(*SKIP)",
  r"(*ANYCRLF)\s(?:ab|a)(*SKIP:A)", r"(*ANYCRLF)\s(?:ab|a)(*THEN)",
  r"(*ANYCRLF)\s(?:ab|a)(*THEN:A)", r"(*ANYCRLF)\s(?:a|ab)(*ACCEPT)",
  r"(*ANYCRLF)\s(?:a|ab)(*COMMIT)", r"(*ANYCRLF)\s(?:a|ab)(*MARK:A)",
  r"(*ANYCRLF)\s(?:a|ab)(*PRUNE)", r"(*ANYCRLF)\s(?:a|ab)(*PRUNE:A)",
  r"(*ANYCRLF)\s(?:a|ab)(*SKIP)", r"(*ANYCRLF)\s(?:a|ab)(*SKIP:A)",
  r"(*ANYCRLF)\s(?:a|ab)(*THEN)", r"(*ANYCRLF)\s(?:a|ab)(*THEN:A)",
  r"(*ANYCRLF)\sa(*ACCEPT)", r"(*ANYCRLF)\sa(*COMMIT)",
  r"(*ANYCRLF)\sa(*MARK:A)", r"(*ANYCRLF)\sa(*PRUNE)",
  r"(*ANYCRLF)\sa(*PRUNE:A)", r"(*ANYCRLF)\sa(*SKIP)",
  r"(*ANYCRLF)\sa(*SKIP:A)", r"(*ANYCRLF)\sa(*THEN)",
  r"(*ANYCRLF)\sa(*THEN:A)", r"(*ANYCRLF)\sa+", r"(*ANYCRLF)\sa+(*ACCEPT)",
  r"(*ANYCRLF)\sa+(*COMMIT)", r"(*ANYCRLF)\sa+(*MARK:A)",
  r"(*ANYCRLF)\sa+(*PRUNE)", r"(*ANYCRLF)\sa+(*PRUNE:A)",
  r"(*ANYCRLF)\sa+(*SKIP)", r"(*ANYCRLF)\sa+(*SKIP:A)",
  r"(*ANYCRLF)\sa+(*THEN)", r"(*ANYCRLF)\sa+(*THEN:A)", r"(*ANYCRLF)\sb",
  r"(*ANYCRLF)\sb(*ACCEPT)", r"(*ANYCRLF)\sb(*COMMIT)",
  r"(*ANYCRLF)\sb(*MARK:A)", r"(*ANYCRLF)\sb(*PRUNE)",
  r"(*ANYCRLF)\sb(*PRUNE:A)", r"(*ANYCRLF)\sb(*SKIP)",
  r"(*ANYCRLF)\sb(*SKIP:A)", r"(*ANYCRLF)\sb(*THEN)",
  r"(*ANYCRLF)\sb(*THEN:A)", r"(*CRLF)(*NO_START_OPT)\s(*SKIP)(?:ab|a)",
  r"(*CRLF)(*NO_START_OPT)\s(*SKIP)(?:a|ab)",
  r"(*CRLF)(*NO_START_OPT)\s(*SKIP)[ab]",
  r"(*CRLF)(*NO_START_OPT)\s(*SKIP)a", r"(*CRLF)(*NO_START_OPT)\s(*SKIP)a+",
  r"(*CRLF)(*NO_START_OPT)\s(*SKIP)b",
  r"(*CRLF)(*NO_START_OPT)\sb*(*SKIP)a|x?", r"(*CRLF)(?:\sa+)+",
  r"(*CRLF).(?:ab|a)", r"(*CRLF).(?:ab|a)(*ACCEPT)",
  r"(*CRLF).(?:ab|a)(*COMMIT)", r"(*CRLF).(?:ab|a)(*MARK:A)",
  r"(*CRLF).(?:ab|a)(*PRUNE)", r"(*CRLF).(?:ab|a)(*PRUNE:A)",
  r"(*CRLF).(?:ab|a)(*SKIP)", r"(*CRLF).(?:ab|a)(*SKIP:A)",
  r"(*CRLF).(?:ab|a)(*THEN)", r"(*CRLF).(?:ab|a)(*THEN:A)",
  r"(*CRLF).(?:a|ab)(*ACCEPT)", r"(*CRLF).(?:a|ab)(*COMMIT)",
  r"(*CRLF).(?:a|ab)(*MARK:A)", r"(*CRLF).(?:a|ab)(*PRUNE)",
  r"(*CRLF).(?:a|ab)(*PRUNE:A)", r"(*CRLF).(?:a|ab)(*SKIP)",
  r"(*CRLF).(?:a|ab)(*SKIP:A)", r"(*CRLF).(?:a|ab)(*THEN)",
  r"(*CRLF).(?:a|ab)(*THEN:A)", r"(*CRLF).a(*ACCEPT)", r"(*CRLF).a(*COMMIT)",
  r"(*CRLF).a(*MARK:A)", r"(*CRLF).a(*PRUNE)", r"(*CRLF).a(*PRUNE:A)",
  r"(*CRLF).a(*SKIP)", r"(*CRLF).a(*SKIP:A)", r"(*CRLF).a(*THEN)",
  r"(*CRLF).a(*THEN:A)", r"(*CRLF).a+(*ACCEPT)", r"(*CRLF).a+(*COMMIT)",
  r"(*CRLF).a+(*MARK:A)", r"(*CRLF).a+(*PRUNE)", r"(*CRLF).a+(*PRUNE:A)",
  r"(*CRLF).a+(*SKIP)", r"(*CRLF).a+(*SKIP:A)", r"(*CRLF).a+(*THEN)",
  r"(*CRLF).a+(*THEN:A)", r"(*CRLF).b(*ACCEPT)", r"(*CRLF).b(*COMMIT)",
  r"(*CRLF).b(*MARK:A)", r"(*CRLF).b(*PRUNE)", r"(*CRLF).b(*PRUNE:A)",
  r"(*CRLF).b(*SKIP)", r"(*CRLF).b(*SKIP:A)", r"(*CRLF).b(*THEN)",
  r"(*CRLF).b(*THEN:A)", r"(*CRLF)\s(*SKIP)(?:ab|a)",
  r"(*CRLF)\s(*SKIP)(?:a|ab)", r"(*CRLF)\s(*SKIP)[ab]", r"(*CRLF)\s(*SKIP)a",
  r"(*CRLF)\s(*SKIP)a+", r"(*CRLF)\s(*SKIP)b", r"(*CRLF)\s(?:ab|a)(*ACCEPT)",
  r"(*CRLF)\s(?:ab|a)(*COMMIT)", r"(*CRLF)\s(?:ab|a)(*MARK:A)",
  r"(*CRLF)\s(?:ab|a)(*PRUNE)", r"(*CRLF)\s(?:ab|a)(*PRUNE:A)",
  r"(*CRLF)\s(?:ab|a)(*SKIP)", r"(*CRLF)\s(?:ab|a)(*SKIP:A)",
  r"(*CRLF)\s(?:ab|a)(*THEN)", r"(*CRLF)\s(?:ab|a)(*THEN:A)",
  r"(*CRLF)\s(?:a|ab)(*ACCEPT)", r"(*CRLF)\s(?:a|ab)(*COMMIT)",
  r"(*CRLF)\s(?:a|ab)(*MARK:A)", r"(*CRLF)\s(?:a|ab)(*PRUNE)",
  r"(*CRLF)\s(?:a|ab)(*PRUNE:A)", r"(*CRLF)\s(?:a|ab)(*SKIP)",
  r"(*CRLF)\s(?:a|ab)(*SKIP:A)", r"(*CRLF)\s(?:a|ab)(*THEN)",
  r"(*CRLF)\s(?:a|ab)(*THEN:A)", r"(*CRLF)\sa(*ACCEPT)",
  r"(*CRLF)\sa(*COMMIT)", r"(*CRLF)\sa(*MARK:A)", r"(*CRLF)\sa(*PRUNE)",
  r"(*CRLF)\sa(*PRUNE:A)", r"(*CRLF)\sa(*SKIP)", r"(*CRLF)\sa(*SKIP:A)",
  r"(*CRLF)\sa(*THEN)", r"(*CRLF)\sa(*THEN:A)", r"(*CRLF)\sa+(*ACCEPT)",
  r"(*CRLF)\sa+(*COMMIT)", r"(*CRLF)\sa+(*MARK:A)", r"(*CRLF)\sa+(*PRUNE)",
  r"(*CRLF)\sa+(*PRUNE:A)", r"(*CRLF)\sa+(*SKIP)", r"(*CRLF)\sa+(*SKIP:A)",
  r"(*CRLF)\sa+(*THEN)", r"(*CRLF)\sa+(*THEN:A)", r"(*CRLF)\sb(*ACCEPT)",
  r"(*CRLF)\sb(*COMMIT)", r"(*CRLF)\sb(*MARK:A)", r"(*CRLF)\sb(*PRUNE)",
  r"(*CRLF)\sb(*PRUNE:A)", r"(*CRLF)\sb(*SKIP)", r"(*CRLF)\sb(*SKIP:A)",
  r"(*CRLF)\sb(*THEN)", r"(*CRLF)\sb(*THEN:A)"
]
  ## The 212 patterns of S8bj's tri-oracle (56764 verb patterns) on which
  ## the 8.37 JIT and interpreter differ.

const
  jitConventions* = ["", "(*CRLF)", "(*ANYCRLF)", "(*ANY)", "(*CR)"]
  jitHeads* = ["ab", "aba", "\\r\\na", "\\ra", "\\na", "a\\r", "\\sa",
    "\\s\\s", ".a", ".[ab]", "[ab]a", "a.b", "(?i)ab", "a{3}", "a{2}b",
    "\\s{2}", "(?:ab|ba)a", "(?:a|b)ab", "(a)ba", "a?ba", "a+ba",
    "(?:\\r|\\n)a", "(?:\\r\\n|a)b", "[^a]a", "\\Sa", "ab|ba", "a(?:b|\\r)a",
    "\\s[ab]"]
  jitTails* = ["", "(*SKIP)", "(*COMMIT)", "(*PRUNE)", "(*SKIP)a",
    "(*MARK:A)(*SKIP:A)", "(*SKIP:A)b|."]
  jitLongHeads* = ["abab", "a\\r\\na", "\\r\\nab", "abc|abd", "(?:ab|ba)ab",
    "a.ab", "\\sab", "(?i)aba"]

proc jitCorpus*(): seq[string] =
  ## The short-subject corpus: every head with every tail under every
  ## newline convention, then the 212 known patterns.
  for cv in jitConventions:
    for h in jitHeads:
      for t in jitTails:
        result.add cv & h & t
  for p in known212:
    if p notin result: result.add p

proc jitLongCorpus*(): seq[string] =
  ## Longer prefixes (the scan's skip table needs at least three known
  ## positions), for subjects up to length 5.
  for cv in ["", "(*CRLF)", "(*ANY)"]:
    for h in jitLongHeads:
      for t in ["", "(*SKIP)"]:
        result.add cv & h & t

proc words*(alpha: string; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next

const
  shortAlpha* = "ab\r\n"
  shortLen* = 3
  longAlpha* = "ab\r\n"
  longLen* = 5

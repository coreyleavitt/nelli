## RFC-0005 S8bt (item 3) -- the corpus of `match()`'s call accounting: the
## pattern classes the walker reads (literals, classes, types, the dot;
## their greedy, lazy and counted repeats, with and without the
## auto-possessification pcre_compile.c applies; groups with and without
## captures and alternatives, their repeats; anchors; the verbs), shared by
## the tests (`tsymex_rfc0005_s8bt_limit*.nim`).

proc limitCorpus*(): seq[string] =
  const atoms = ["a", "[ab]", "\\s", ".", "b"]
  const reps = ["", "*", "+", "?", "*?", "+?", "??", "{2}", "{1,3}",
                "{0,2}?", "{2,}"]
  # One repeated item, then a tail (the tail decides auto-possessification).
  for a in atoms:
    for r in reps:
      for tail in ["", "a", "b", "\\s", "(?:a|b)", "$", "(*SKIP)b",
                   "(*COMMIT)a", "(*PRUNE)a", "(*MARK:A)b"]:
        result.add a & r & tail
  # Groups.
  const groups = ["(?:ab|a)", "(ab|a)", "(?:a|b|ab)", "(a|(b))", "(?:a)",
                  "(a)", "(?:a|)", "(?:a*)", "(a?)", "(?:a(*THEN)b|a)"]
  const greps = ["", "*", "+", "?", "*?", "+?", "??", "{2}", "{0,2}",
                 "{1,3}?", "{2,}"]
  for g in groups:
    for r in greps:
      for tail in ["", "b", "a", "(*COMMIT)b"]:
        result.add g & r & tail
  # Alternatives at the top level, anchors, verbs.
  for p in ["a|b", "ab|a|b", "a|b(*THEN)c|ab", "^a|b", "a$|b", "(?m)^b",
            "(*COMMIT)a|b", "a(*SKIP)b|.", "a(*PRUNE)b|.", "(*MARK:A)a|b",
            "a(*MARK:A)(*SKIP:A)b|.", "(*THEN)a|b", "a+?b|a*b", "(?:a|b)*b",
            "(?:a+|b)*c", "(?:(a)|b)+", "x*", "\\s*\\s", "[^a]*a",
            "(*CRLF)\\s+a|b", "(*ANY).*b", "a(*ACCEPT)b|c"]:
    result.add p
  # A SKIP:NAME without its MARK: the attempt re-runs from a fresh count,
  # ignoring the SKIP:NAMEs it passed (no RMATCH, one frame higher).
  for p in ["a(*SKIP:A)b|.", "a+(*SKIP:A)b|a", "(?:a(*SKIP:A)b|a)+c|.",
            "a(*SKIP:B)(?:b|c)d|ab|.", "(*MARK:A)a(*SKIP:A)b|a(*SKIP:B)c|.",
            "a(*SKIP:A)a(*SKIP:B)b|a+", "(?:a|b)(*SKIP:A)\\s|b",
            "a(*SKIP:A)(?:b(*SKIP:B)c|b)|.", "(a)(*SKIP:A)b|(.)",
            "a*(*SKIP:A)b|a*", "(?:a(*SKIP:A))*b|."]:
    result.add p

proc limitSubjects*(): seq[string] =
  ## Every word over `ab \r\n` up to length 3, and a few longer runs.
  const alpha = "ab \n"
  result = @[""]
  var cur = @[""]
  for n in 1 .. 3:
    var nx: seq[string]
    for w in cur:
      for c in alpha: nx.add w & c
    result.add nx
    cur = nx
  for w in ["aaaaaaab", "abababab", "bbbbbbba", "aaaa\r\nbbbb", "aaaaaaaaaa"]:
    result.add w

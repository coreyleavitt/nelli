## RFC-0005 S8bt -- the JIT oracle harness. Prints, for every pattern of
## the JIT corpus (`jit_corpus.nim`), std/re's unanchored results: `find`
## and `findBounds`' `last` at every start, `replace(s, re, "-")`, and (the
## capture corpus) `findBounds`' groups. Run once against PCRE 8.37 built
## with the JIT and once against its interpreter build; the lines that
## differ are `jit837-delta.txt`.
##   jit_oracle short|long|utf|caps
import std/[re, strutils, os]
import ./jit_corpus

let mode = (if paramCount() >= 1: paramStr(1) else: "short")
let pats = case mode
  of "long": jitLongCorpus()
  of "utf": jitUtfCorpus()
  of "caps": jitCapCorpus()
  else: jitCorpus()
let subjects = case mode
  of "long": words(longAlpha, longLen)
  of "utf": utfSubjects()
  else: words(shortAlpha, shortLen)
for p in pats:
  echo "P\t", escape(p)
  let rx = re(p)
  for s in subjects:
    for st in 0 .. s.len:
      echo "C\t", escape(s), "\t", st, "\t", find(s, rx, st), "\t",
           findBounds(s, rx, st).last
      if mode == "caps":
        var b: array[4, tuple[first, last: int]]
        for i in 0 ..< b.len: b[i] = (first: -9, last: -9)
        let r = findBounds(s, rx, b, st)
        var f = @[$r.first, $r.last]
        for x in b: f.add $x.first & ":" & $x.last
        echo "K\t", escape(s), "\t", st, "\t", f.join(" ")
    if mode in ["short", "utf"]:
      echo "R\t", escape(s), "\t", escape(replace(s, rx, "-"))

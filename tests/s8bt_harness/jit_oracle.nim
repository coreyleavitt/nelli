## RFC-0005 S8bt -- the JIT oracle harness. Prints, for every pattern of
## the JIT corpus (`jit_corpus.nim`), std/re's unanchored results: `find`
## and `findBounds`' `last` at every start, and `replace(s, re, "-")`.
## Run once against PCRE 8.37 built with the JIT and once against its
## interpreter build; the cells that differ are `jit837-delta.txt`.
##   jit_oracle short|long
import std/[re, strutils, os]
import ./jit_corpus

let long = paramCount() >= 1 and paramStr(1) == "long"
let pats = (if long: jitLongCorpus() else: jitCorpus())
let subjects = (if long: words(longAlpha, longLen) else: words(shortAlpha, shortLen))
for p in pats:
  echo "P\t", escape(p)
  let rx = re(p)
  for s in subjects:
    for st in 0 .. s.len:
      echo "C\t", escape(s), "\t", st, "\t", find(s, rx, st), "\t",
           findBounds(s, rx, st).last
    if not long:
      echo "R\t", escape(s), "\t", escape(replace(s, rx, "-"))

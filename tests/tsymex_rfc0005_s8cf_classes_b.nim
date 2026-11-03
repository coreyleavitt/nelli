## RFC-0005 S8cf (item 7) -- UTF classes on libpcre 8.37. A negated escape
## reads the same on 8.37 and 8.45; a lone `(*UCP)` POSIX class reads with
## 8.37's `[:punct:]` (the symbols below 256); only a `[:graph:]`, `[:print:]`,
## `[:punct:]` or negated ascii / cntrl / xdigit beside another item declines.
## Each class is compared with the running library at every code point below
## U+0180 and at the wide samples.
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8cf_classes`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 66 s).

import std/[unittest, re, strutils, unicode]
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine

proc punctCent(s: string) =
  if s == "\xc2\xa2" and s.matchLen(re"(*UTF)(*UCP)[[:punct:]]") == 2:
    symexTarget("cf_cls_cent")

proc punctCentNo(s: string) =
  if s == "\xc2\xa2" and s.matchLen(re"(*UTF)(*UCP)[[:punct:]]") == -1:
    symexTarget("cf_cls_cent_no")

proc beside(s: string) =
  if s == "\xc2\xa2" and s.matchLen(re"(*UTF)(*UCP)[[:punct:]_]") == 2:
    symexTarget("cf_cls_beside")

suite "S8cf: UTF classes":
  test "the walker reads [:punct:] as the running library does":
    let takes = "\xc2\xa2".matchLen(re"(*UTF)(*UCP)[[:punct:]]") == 2
    check takes == pcreOlderThan(8, 45)
    check symexFind(punctCent, tLabel("cf_cls_cent")).status ==
      (if takes: sxSat else: sxUnsat)
    check symexFind(punctCentNo, tLabel("cf_cls_cent_no")).status ==
      (if takes: sxUnsat else: sxSat)

  test "a special POSIX class beside another item declines on 8.37 only":
    let st = symexFind(beside, tLabel("cf_cls_beside")).status
    if pcreOlderThan(8, 45):
      check st == sxUnknown
    else:
      check "\xc2\xa2".matchLen(re"(*UTF)(*UCP)[[:punct:]_]") == -1
      check st == sxUnsat

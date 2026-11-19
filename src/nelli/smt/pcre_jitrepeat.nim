## RFC-0016 S8co (PRC-33 item 5). PCRE 8.37's JIT folds runs of identical
## brackets (pcre_jit_compile.c's `detect_repeat`, called by
## `set_private_data_ptrs` at every OP_BRA / OP_CBRA in code order) into one
## compiled copy with a counter:
##   * OP_EXACT: three or more identical brackets in a row, closed by OP_KET;
##     the copy runs `count` times and calls `count_match` at the end of each;
##   * OP_UPTO / OP_MINUPTO: a bracket followed by a chain of nested optional
##     copies of it (OP_BRAZERO / OP_BRAMINZERO, OP_BRA wrapping all but the
##     last, at least one wrapper); the bracket becomes an OP_KETRMAX /
##     OP_KETRMIN loop of `count` iterations. When the run before the chain
##     is longer than one, the run's last bracket starts the loop and the
##     rest of the run is tried as OP_EXACT (three or more), else left alone.
## Identity is byte identity of the compiled code, so a literal duplicate
## (`(?:ab)(?:ab)(?:ab)`), the copies pcre_compile.c makes for a repeat and
## the copies a following repeat's chain holds all join a run; copies that
## auto-possessification compiled differently (`Possess`) do not.
## RFC-0016 S8co (PRC-33 item 4c): `detect_repeat` reads bytes, not the
## pattern, so the code is read as a token per opcode (`Tok`, pcre_compile.c's
## layout of every repeat: its copies, OP_BRAZERO, the OP_BRA wrappers of a
## chain) and the scan runs over the tokens. A literal `(?:(?:ab)(?:ab)?)`
## behind OP_BRAZERO is then the wrapper `(?:ab){1,3}`'s chain holds, and
## `(?:(?:ab){2})` the same bracket as `(?:(?:ab)(?:ab))`.
## A fold that starts at a bracket behind OP_BRAZERO or OP_SKIPZERO is a JIT
## defect: the zero bracket's code is generated for the whole fold, and the
## native call crashes (probed on 8.37 with the JIT: `(?:ab)?(?:ab)(?:ab)` on
## "abab" is SIGSEGV). `crash` names it, and the caller declines.
##
## Pure Nim. The addresses are `pcre_code.codeSize`'s layout, the one the
## automaton builder (`pcre_select.nim`) passes as `base`.

import std/[sets, tables]
import ./pcre_syntax
import ./pcre_code
import ./pcre_possess

type
  UptoFold* = object
    ## An OP_UPTO / OP_MINUPTO loop started at a bracket: its iterations (the
    ## bracket itself first, then the chain's copies) and their addresses.
    lazy*: bool
    iters*: seq[tuple[x: Rx, base: int]]

  JitFolds* = object
    exact*: HashSet[int]          ## brackets in an OP_EXACT fold: a
                                  ## `count_match` at the end of each
    upto*: Table[int, UptoFold]   ## the bracket an OP_UPTO / OP_MINUPTO
                                  ## loop starts at
    absorbed*: HashSet[int]       ## repeats (their address) with no
                                  ## mandatory copy whose code is the chain
                                  ## of a loop started before them
    crash*: string                ## a fold behind a zero bracket (declined)

  TokKind = enum
    tkOpen      ## OP_BRA / OP_CBRA (an OP_SBRA for a looping copy)
    tkClose     ## OP_KET, or OP_KETRMAX / OP_KETRMIN (`ket`)
    tkAlt       ## OP_ALT
    tkZero      ## OP_BRAZERO / OP_BRAMINZERO (`lazy`)
    tkSkipZero  ## OP_SKIPZERO
    tkAtom      ## any other item (its code compared by `sameCode`)

  KetKind = enum
    kPlain, kMax, kMin  ## OP_KET, OP_KETRMAX, OP_KETRMIN

  Tok = object
    kind: TokKind
    x: Rx          ## tkOpen: the bracket (nil: a chain's OP_BRA wrapper);
                   ## tkAtom: the item
    base: int      ## tkOpen / tkAtom: the address
    cap: int       ## tkOpen: the capture number (0: OP_BRA)
    ket: KetKind   ## tkOpen / tkClose: how the bracket closes
    lazy: bool     ## tkZero: OP_BRAMINZERO
    close: int     ## tkOpen: its tkClose's index
    item: int      ## tkZero: the address of the repeat it is
                   ## the first unit of (no mandatory copy), else -1

proc sameCode(a: Rx; ab: int; b: Rx; bb: int; p: Possess): bool =
  ## Whether the items `a` at address `ab` and `b` at `bb` (not brackets)
  ## compile to the same code units, with the same repeats possessified.
  if a.kind != b.kind or a.cap != b.cap: return false
  case a.kind
  of rxSet, rxChars:
    if a.op != b.op or a.ch != b.ch or a.ci != b.ci or a.crlfDot != b.crlfDot or
       a.clist != b.clist or a.clistNot != b.clistNot or a.pname != b.pname or
       a.pnot != b.pnot or a.negType != b.negType or a.xNot != b.xNot or
       a.xMap != b.xMap or a.xProp != b.xProp: return false
    if a.kind == rxSet: a.bytes == b.bytes else: a.cps == b.cps
  of rxRep:
    a.lo == b.lo and a.hi == b.hi and a.lazy == b.lazy and
      not a.sub.isGroup and not b.sub.isGroup and
      sameCode(a.sub, ab + 1, b.sub, bb + 1, p) and
      ((ab in p.addrs) == (bb in p.addrs))
  of rxCat, rxAlt: false
  of rxBol, rxEol: a.multi == b.multi
  of rxEolAbs: true
  of rxAccept: a.open == b.open
  of rxVerb: a.verb == b.verb and a.name == b.name

proc flatItems(t: var seq[Tok]; items: seq[Rx]; base: int)

proc flatGroup(t: var seq[Tok]; x: Rx; base: int; ket = kPlain) =
  ## A bracket at `base`: its alternatives' tokens between its open and
  ## close.
  let o = t.len
  t.add Tok(kind: tkOpen, x: x, base: base, cap: x.cap, ket: ket)
  var a = base + 1
  for k, br in groupAlts(x):
    if k > 0: t.add Tok(kind: tkAlt)
    t.flatItems(branchItems(br), a)
    a += branchSize(br) + 1
  t[o].close = t.len
  t.add Tok(kind: tkClose, ket: ket)

proc flatItems(t: var seq[Tok]; items: seq[Rx]; base: int) =
  ## A branch's items as pcre_compile.c lays them out: a group repeat is
  ## `lo` copies, then OP_SKIPZERO and one (`{0}`), one looping copy
  ## (OP_BRAZERO before it when `lo` is 0), or `hi - lo` nested optional
  ## copies, each behind OP_BRAZERO / OP_BRAMINZERO and all but the last in
  ## an OP_BRA wrapper.
  var a = base
  for it in items:
    case it.kind
    of rxCat, rxAlt:
      t.flatGroup(it, a)
    of rxRep:
      if not it.sub.isGroup:
        t.add Tok(kind: tkAtom, x: it, base: a)
      else:
        let sub = it.sub
        let sz = codeSize(sub)
        let b0 = a + 1
        if it.hi == 0:
          t.add Tok(kind: tkSkipZero)
          t.flatGroup(sub, b0)
        elif it.hi < 0:
          for i in 0 ..< it.lo - 1: t.flatGroup(sub, b0 + i * sz)
          if it.lo == 0: t.add Tok(kind: tkZero, lazy: it.lazy, item: a)
          t.flatGroup(sub, b0 + (max(it.lo, 1) - 1) * sz,
                      (if it.lazy: kMin else: kMax))
        else:
          for i in 0 ..< it.lo: t.flatGroup(sub, b0 + i * sz)
          var wraps: seq[int]
          for i in it.lo ..< it.hi:
            t.add Tok(kind: tkZero, lazy: it.lazy,
                      item: (if i == 0: a else: -1))
            if i < it.hi - 1:
              wraps.add t.len
              t.add Tok(kind: tkOpen, base: -1)
            t.flatGroup(sub, b0 + i * sz)
          for k in countdown(wraps.high, 0):
            t[wraps[k]].close = t.len
            t.add Tok(kind: tkClose)
    else:
      t.add Tok(kind: tkAtom, x: it, base: a)
    a += codeSize(it)

proc same(t: seq[Tok]; i, j: int; p: Possess): bool =
  ## Whether the brackets opened at `i` and `j` are the same code units
  ## (`detect_repeat`'s length test and `memcmp`).
  if t[i].kind != tkOpen or t[j].kind != tkOpen: return false
  let n = t[i].close - i
  if t[j].close - j != n: return false
  for k in 0 .. n:
    let a = t[i + k]
    let b = t[j + k]
    if a.kind != b.kind: return false
    case a.kind
    of tkOpen:
      if a.cap != b.cap or a.ket != b.ket: return false
    of tkClose:
      if a.ket != b.ket: return false
    of tkZero:
      if a.lazy != b.lazy: return false
    of tkAtom:
      if codeSize(a.x) != codeSize(b.x) or
         not sameCode(a.x, a.base, b.x, b.base, p): return false
    of tkAlt, tkSkipZero: discard
  true

proc zeroWhy(fold: string; z: Tok): string =
  "8.37's JIT folds identical brackets into " & fold & " starting behind " &
    (if z.kind == tkSkipZero: "OP_SKIPZERO"
     elif z.lazy: "OP_BRAMINZERO"
     else: "OP_BRAZERO") &
    " (pcre_jit_compile.c's detect_repeat compiles the whole fold under " &
    "the zero bracket; the native call crashes or runs the wrong copies)"

const wrapperWhy = "8.37's JIT folds a repeat's OP_BRA wrapper into an " &
  "OP_UPTO loop as one of its copies (detect_repeat compares bytes; the " &
  "automaton has no bracket of its own for a wrapper)"

proc chainAfter(t: seq[Tok]; i, next, hi: int; p: Possess;
                copies: var seq[int]): int =
  ## `detect_repeat`'s OP_UPTO / OP_MINUPTO test after the run of the
  ## bracket opened at `i` (`next`: the token after the run): the chain's
  ## copies (each wrapper's, then the last one) and the token after the
  ## wrappers' OP_KETs, -1 when there is no chain.
  copies.setLen 0
  if next >= hi or t[next].kind != tkZero: return -1
  let lazy = t[next].lazy
  var c = next
  while c + 2 < hi and t[c].kind == tkZero and t[c].lazy == lazy and
        t[c + 1].kind == tkOpen and t[c + 1].cap == 0 and same(t, i, c + 2, p):
    copies.add c + 2
    c = t[c + 2].close + 1
  if copies.len == 0 or c + 1 >= hi or t[c].kind != tkZero or
     t[c].lazy != lazy or not same(t, i, c + 1, p): return -1
  var e = t[c + 1].close + 1
  for _ in 0 ..< copies.len:
    if e >= hi or t[e].kind != tkClose or t[e].ket != kPlain: return -1
    inc e
  copies.add c + 1
  e

proc scan(f: var JitFolds; t: seq[Tok]; lo, hi: int; p: Possess) =
  ## `set_private_data_ptrs` over the tokens `lo ..< hi`: `detect_repeat`
  ## at each bracket in code order. A fold's first bracket is compiled (its
  ## contents are scanned); the copies after it are not, and run as that
  ## bracket does, so their contents' folds are read as its are (the
  ## automaton compiles each copy at its own address).
  var i = lo
  while i < hi:
    if t[i].kind != tkOpen or t[i].ket != kPlain:
      inc i
      continue
    # detect_repeat: a run of identical brackets ...
    var run = @[i]
    var next = t[i].close + 1
    while next < hi and same(t, i, next, p):
      run.add next
      next = t[next].close + 1
    var mins = run.len
    var copies: seq[int]
    let chainEnd = (if mins == 2: -1 else: chainAfter(t, i, next, hi, p, copies))
    var returned = false   # detect_repeat's result: a fold from `i`
    if chainEnd >= 0:
      # ... then a chain of nested optional copies: the run's last bracket
      # starts the loop.
      let last = run[^1]
      var fold = UptoFold(lazy: t[next].lazy)
      for k in @[last] & copies:
        if t[k].x == nil:
          if f.crash.len == 0: f.crash = wrapperWhy
          return
        fold.iters.add (t[k].x, t[k].base)
      f.upto[t[last].base] = fold
      if t[next].item >= 0: f.absorbed.incl t[next].item
      if mins == 1: returned = true
      else: dec mins
    if not returned and mins >= 3:
      for k in 0 ..< mins: f.exact.incl t[run[k]].base
      returned = true
    if returned and i > 0 and t[i - 1].kind in {tkZero, tkSkipZero} and
       f.crash.len == 0:
      f.crash = zeroWhy((if run.len == 1: "OP_UPTO" else: "OP_EXACT"),
                        t[i - 1])
    if i > 0 and t[i - 1].kind == tkSkipZero:
      # OP_SKIPZERO's bracket is never compiled: its folds are never run.
      i = t[i].close + 1
      continue
    if chainEnd < 0 and not returned:
      inc i
      continue
    # Every bracket of the run and the chain runs as the first one does.
    f.scan(t, i + 1, t[i].close, p)
    for k in run[1 .. ^1] & copies: f.scan(t, k + 1, t[k].close, p)
    i = (if chainEnd >= 0: chainEnd else: t[run[^1]].close + 1)

proc jitFolds*(root: Rx; p: Possess): JitFolds =
  ## The folds 8.37's JIT makes in a reading's code (`root` at address 0,
  ## as `pcre_select.buildNfa` compiles it).
  var t: seq[Tok]
  var a = 1
  for k, br in groupAlts(root):
    if k > 0: t.add Tok(kind: tkAlt)
    t.flatItems(branchItems(br), a)
    a += branchSize(br) + 1
  result.scan(t, 0, t.len, p)

proc jitFoldDecline*(root: Rx; p: Possess): string =
  ## Why 8.37's JIT's folds of `root` are not read, "" when they are: a fold
  ## behind a zero bracket (the native call crashes or runs the fold where
  ## the zero bracket's alternative belongs). Auto-possessification decides
  ## which copies are identical, and `p` types every property the reader
  ## accepts (`pcre_possess.propType` is total over them), so no fold is
  ## left unread next to one (RFC-0016 S8co, PRC-33 item 4b).
  jitFolds(root, p).crash

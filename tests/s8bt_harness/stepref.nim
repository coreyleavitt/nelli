## RFC-0005 S8bj, S8bt -- a direct interpreter of the agenda's step table
## (`pcre_select.stepTable`) inside the search loop of the automaton's
## engine: pcre_exec.c's (the start-of-match scan, the CRLF start skip) or
## PCRE 8.37's JIT's (its prefix scan, no CRLF start skip at a SKIP's
## landing, the bumpalong by a UTF-8 lead byte's length).
import std/tables
import nelli/smt/[pcre_syntax, pcre_select, pcre_jit, pcre_engine]

proc finalNl(n: Nfa; s: string; j: int): bool =
  let rest = s.len - j
  (rest == 1 and s[j] in nlBytes(n.nl)) or
    (nlPair(n.nl) and rest == 2 and s[j] == '\r' and s[j + 1] == '\n')

proc runRef(n: Nfa; t: StepTable; s: string; x, st0: int): (LeafKind, int) =
  ## The table's attempt at `x`: its outcome and position.
  var st = st0
  var regs: seq[int]
  for j in x .. s.len:
    let row = t.rows[st]
    let lf =
      if j == s.len: row.atEnd
      elif finalNl(n, s, j): row.nll[ord(s[j])]
      else: row.other[ord(s[j])]
    case lf.kind
    of lfNext:
      var nr: seq[int]
      for m in lf.regMap: nr.add(if m < 0: j else: regs[m])
      regs = nr
      st = lf.next
    of lfMatch, lfSkip:
      return (lf.kind, (if lf.reg < 0: j else: regs[lf.reg]))
    else:
      return (lf.kind, 0)
  raiseAssert "runRef: no leaf at the end"

proc execRef*(n: Nfa; t: StepTable; s: string; start: int;
              ne: bool): (int, int) =
  ## The engine's loop over the table's attempts.
  let jit = n.engine == peJit837
  var x = start
  while true:
    if jit and n.jit.on and not n.anchoredPat: x = n.jit.scanFrom(s, x)
    else:
      while not created(n, s, x, start): inc x
    let pc = canonPc0(n, classAt(s, x))
    let elig = n.hasNeverSkip and x > start and x < s.len and
               s[x - 1] == '\r' and s[x] == '\n' and n.skipActive
    let (k, pos) = runRef(n, t, s, x, t.start[(pc, ne and x == start, elig)])
    var next: int
    var landed = false
    case k
    of lfMatch: return (x, pos)
    of lfCommit: return (-1, 0)
    of lfSkip:
      landed = pos > x
      next = (if landed: pos else: x + 1)
    else: next = x + 1
    if n.utf and not landed:
      if jit:
        if x < s.len:
          let c = ord(s[x])
          next = min(s.len, x + 1 + (if c >= 0xF0: 3 elif c >= 0xE0: 2
                                     elif c >= 0xC0: 1 else: 0))
      else:
        while next < s.len and (ord(s[next]) and 0xC0) == 0x80: inc next
    if n.anchoredPat or next > s.len: return (-1, 0)
    x = next
    if not (jit and landed) and x > start and s[x - 1] == '\r' and
       x < s.len and s[x] == '\n' and n.skipActive:
      inc x

proc replaceRef*(n: Nfa; t: StepTable; s, by: string): string =
  var prev = 0
  var ne = false
  while prev < s.len:
    let (a, b) = execRef(n, t, s, prev, ne)
    ne = false
    if a < 0: break
    result.add s[prev ..< a]
    result.add by
    if a == b: ne = true
    prev = b
  result.add s[min(prev, s.len) .. ^1]

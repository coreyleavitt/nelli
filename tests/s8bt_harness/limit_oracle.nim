## RFC-0005 S8bt (item 3) -- the libpcre oracle of `match()`'s call
## accounting: the least `match_limit` (`match_limit_recursion`) under which
## an unanchored `pcre_exec` from `start` does not fail with
## PCRE_ERROR_MATCHLIMIT (PCRE_ERROR_RECURSIONLIMIT), on the interpreter
## (studied without the JIT, as std/re studies). pcre_exec.c resets the count
## for each attempt, so the call fails with the error exactly when the limit
## is below that least value (the attempts it makes do not depend on the
## limit): the value is the largest number of `match()` calls (the deepest
## `match()` nesting, plus one) of an attempt it makes.
import pcre

type LimitOracle* = object
  code: ptr Pcre
  extra: ptr ExtraData
  own: ExtraData

proc initLimitOracle*(p: string): LimitOracle =
  var err: cstring
  var off: cint
  result.code = pcre.compile(p.cstring, 0, addr err, addr off, nil)
  doAssert result.code != nil, p
  result.extra = pcre.study(result.code, 0, addr err)
  if result.extra != nil: result.own = result.extra[]

proc rcWith(o: LimitOracle; s: string; start: int; lim: int;
            recursion: bool; anchored: bool): cint =
  var ex = o.own
  if recursion:
    ex.flags = ex.flags or EXTRA_MATCH_LIMIT_RECURSION
    ex.match_limit_recursion = clong(lim)
  else:
    ex.flags = ex.flags or EXTRA_MATCH_LIMIT
    ex.match_limit = clong(lim)
  var ov: array[30, cint]
  # std/re's calls without a `matches` argument: an ovector of 3 (no room
  # for a group).
  pcre.exec(o.code, addr ex, s.cstring, cint(s.len), cint(start),
            (if anchored: pcre.ANCHORED else: 0), addr ov[0], 3)

proc threshold*(o: LimitOracle; s: string; start: int; recursion = false;
                anchored = false; cap = 100_000): int =
  ## The least limit without the error (`cap + 1`: none up to `cap`).
  let errc = (if recursion: pcre.ERROR_RECURSIONLIMIT
              else: pcre.ERROR_MATCHLIMIT)
  if o.rcWith(s, start, cap, recursion, anchored) == errc: return cap + 1
  var lo = 0
  var hi = cap
  while lo < hi:
    let mid = (lo + hi) div 2
    if o.rcWith(s, start, mid, recursion, anchored) == errc: lo = mid + 1
    else: hi = mid
  lo

proc execInterp*(o: LimitOracle; s: string; start: int;
                 anchored = false; notEmptyAtStart = false): (int, int, int) =
  ## The call itself on the interpreter, with the pattern's own limits:
  ## `(rc, first, end)`.
  var ov: array[30, cint]
  var opts: cint = (if anchored: pcre.ANCHORED else: 0)
  if notEmptyAtStart: opts = opts or pcre.NOTEMPTY_ATSTART
  # std/re's calls without a `matches` argument: an ovector of 3.
  let rc = pcre.exec(o.code, o.extra, s.cstring, cint(s.len), cint(start),
                     opts, addr ov[0], 3)
  if rc < 0: (int(rc), 0, 0) else: (1, int(ov[0]), int(ov[1]))

proc replaceInterp*(o: LimitOracle; s, by: string): string =
  ## std/re's `replace` loop over the interpreter.
  var prev = 0
  var ne = false
  while prev < s.len:
    let (rc, a, b) = o.execInterp(s, prev, false, ne)
    ne = false
    if rc < 0: break
    result.add s[prev ..< a]
    result.add by
    if a == b: ne = true
    prev = b
  result.add s[min(prev, s.len) .. ^1]

## Round-6 B7r2 (path-scope rider) -- walker v88.
##
## B7's SECOND ATTEMPT (docs/rfc/0001-chapulin-hardening.handoff.md, the
## "⛔ B7 SECOND ATTEMPT" grind-log bullet) isolated two blockers standing
## between B6's `readOptions` pair-loop closed form and a unified,
## end-to-end decode twin:
##
##   BLOCKER B7-1 -- B6's closed form (`iekStrInOptionRegion`) proves ONLY
##   in its own pinned SUT's exact unconditional top-level shape. THREE
##   independently-sufficient breakers were isolated against the real
##   `readOptions`/`decodeOackTwin` shapes: (a) wrapping the loop in an
##   `if`/`elif` dispatch, (b) following it with variant construction, and
##   (c) calling it via a helper proc (rather than inlining).
##
##   BLOCKER B7-2 -- a `case`-match over scanned string content with an
##   `else: raise` arm (`parseMode`'s own shape) poisons a DISJOINT sibling
##   branch of a multi-branch dispatch.
##
## The RFC's own design section frames a SINGLE unifying architecture for
## all four ("branch-scoped classified degrade": catch a construct-gap
## exception at the `isIf`/`isWhile`/`isCall` walk boundary, taint only
## that branch's own path via SND-1, let siblings keep their real
## verdicts). THIS SLICE FOUND, empirically, that (a) and (b) share ONE
## SPECIFIC root cause UNRELATED to that architecture, (c) is a second,
## independent, ALSO specific root cause, and the general "branch-scoped
## degrade" architecture itself -- needed for B7-2 and for full sibling-
## branch survival in general -- is BLOCKED on this engine's C backend by
## a confirmed soundness hazard. See `symexWalkerVersion`'s own doc
## comment (`canonicalize.nim`) for the full root-cause writeup of all
## three findings, and the handoff's BLOCKER entry for the escalation.
##
## ---- What THIS FILE pins -----------------------------------------------
##
## 1. BLOCKER B7-1(a)/(b) root cause: B6's closed form needs its
##    start/bound operands `svInt`-represented (the CR-17 discipline);
##    `collectIntOffsetParams`'s existing promotion only traces a loop
##    counter back to a FORMAL PARAM through a bare-symbol rebind --
##    chapulin's own `decodeOackTwin` shape seeds the counter from a
##    LITERAL (`var pos = 2`, straight after a header-length check), which
##    has no param to trace to and so stayed BV-allocated, failing CR-17
##    regardless of whether the loop was if-wrapped or followed by
##    construction. FIXED via a companion parse-time collector,
##    `collectIntOffsetLiteralLocals` (`dsl_parser.nim`) + the new
##    `IRStmt.isLet.lIsIntOffsetLocal` field: a literal's value is already
##    known at parse time, so `svInt`-representing it carries none of a
##    param's def-use tracing risk. Pinned below: SAT past the 5-iteration
##    k-unroll horizon for BOTH the if-wrapped (B7-1a) and
##    construction-followed (B7-1b) shapes -- a REAL capability upgrade,
##    not a graceful degrade.
##
## 2. BLOCKER B7-1(c) root cause: a DIFFERENT, independent gap. Bug #2's
##    per-field scoped-decline placeholder (`isUnsupportedFieldPlaceholder`)
##    was scoped to declared OBJECT/VARIANT RECORD FIELDS only
##    (`classifyObjectRecordFields`) -- a BARE local/param/call-RETURN of
##    an unsupported-element seq type (e.g. `readOptions`'s own
##    `seq[(string,string)]` RETURN TYPE) still hit `allocateSeqDataRaw`'s
##    unconditional raise the moment a caller merely BOUND the call's
##    result, even when immediately discarded -- poisoning the WHOLE
##    caller. FIXED by generalizing `allocateSym`'s `itSeq` arm to take the
##    SAME placeholder branch whenever `not isBackedSeqElemTy(seqElemTy)`,
##    regardless of field-vs-bare origin, plus a NEW walk-time read-guard
##    at `isIndex`'s `svSeq` case (SND-1 taint on an ACTUAL indexed read of
##    such a placeholder -- the read-safety companion `dsl_parser.nim`'s
##    existing `nnkDotExpr` interception cannot cover for a bare value,
##    which has no static field-access site). Pinned below: reachability
##    past a call-boundary `seq[(string,string)]`-returning helper, AND
##    the full opOack-faithful composite (dispatch + call + construction).
##
## 3. BLOCKER B7-2 -- **CLOSED 2026-09-01, `cac15e6` (walker v124).** This
##    pin was written as a trip-wire asserting the BROKEN behavior, so that
##    a fix would turn it red rather than let it go silently stale. It went
##    red. It now asserts the FIXED behavior; the paragraph below is kept
##    because the diagnosis-vs-prescription split is the lesson.
##
##    The mechanism named here originally was RIGHT -- `feUnsupportedExprKind`
##    on case-as-expression -- but the prescription was wrong. It did NOT
##    need the general branch-scoped-degrade architecture (which this slice
##    separately found unsound to implement via `try`/`except` around the
##    walker's recursive `walk()` calls; that finding still stands and now
##    lives in RFC-0005). `case` as a STATEMENT was always modelled; only
##    the EXPRESSION form lacked a `parseExpr` arm. The whole-run poisoning
##    was a CONSEQUENCE, not a separate defect: the declining proc is a
##    CALLEE, parsed whole-proc at registration time BEFORE any path exists,
##    so a parse-time decline has no path to scope to. That is precisely why
##    this slice's own path-scoping fixed items 1-2 above and bounced off
##    this one. Fixed by the A-normalisation M5 (walker v50->51) already
##    applied to the `nnkIfExpr` sibling: hoist a temp, emit the case AS A
##    STATEMENT, read the temp back.
##
## 4. A genuinely-unmodeled whole-proc shape still declines (never a
##    crash) -- the standing "walker never crashes" invariant, unaffected
##    by this slice's two fixes.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type TftpDecodeError = object of CatchableError

proc readCStringByteSeq(data: seq[byte], offset: int): (string, int) =
  ## B4's accumulating-scan shape, `seq[byte]` receiver -- chapulin's own
  ## `readCString`, called twice per `readOptions` pair-loop iteration.
  var acc = ""
  var i = offset
  while i < data.len:
    if data[i] == 0'u8:
      return (acc, i + 1)
    acc.add char(data[i])
    i.inc
  raise newException(TftpDecodeError, "unterminated string at offset " & $offset)

proc readU16Twin(data: seq[byte], offset: int): uint16 =
  if offset + 2 > data.len:
    raise newException(TftpDecodeError, "short read at offset " & $offset)
  result = (uint16(data[offset]) shl 8) or uint16(data[offset + 1])

proc readOptionsTwinLike(data: seq[byte], offset: int): seq[(string, string)] =
  ## Real `readOptions`/`readOptionsTwin` shape: RETURNS the accumulated
  ## pairs via `result.add` (not a local `pairs` var) -- this is exactly
  ## what BLOCKER B7-1(c)'s call boundary needs (a callee whose declared
  ## RETURN TYPE is the unsupported-element seq).
  var pos = offset
  while pos < data.len:
    let (key, nextPos) = readCStringByteSeq(data, pos)
    if key.len == 0:
      break
    let (val, finalPos) = readCStringByteSeq(data, nextPos)
    result.add (key, val)
    pos = finalPos

type PacketKind = enum pkFixed, pkOack
type Packet = object
  case kind: PacketKind
  of pkFixed: fixedField: int
  of pkOack: oackOptions: seq[(string, string)]

suite "symex round-6 B7r2 -- version floor":
  test "walker version floor >= 88 (B7r2: literal-seeded int-offset locals + generalized call-boundary seq placeholder)":
    check parseInt(symexWalkerVersion) >= 88

  test "render version floor >= 11 (unchanged -- no witness-content change this slice)":
    check parseInt(renderAsChoicesVersion) >= 11

suite "symex round-6 B7r2 -- BLOCKER B7-1(a): if-wrapped pair-loop now proves (was CR-17 classified decline)":

  test "B7r2-1a: pair-loop inside `if dispatch: <loop> else: discard`, literal-seeded offset, one pair past the k-unroll horizon -> sxSat via the region-membership fast path":
    ## `symexTarget` sits AFTER the loop, inside the SAME `if` arm --
    ## reaching it at all, past 5 real k-unroll iterations, is only
    ## possible via the closed form (a plain k-unroll would exhaust
    ## `maxLoopUnwind` first, per `tsymex_r6_b6_optionregion.nim`'s own
    ## B6-1-red trip-wire methodology).
    proc sut(data: seq[byte], dispatch: bool): int =
      symexAssume(data.len == 16)
      symexAssume(
        data[0] == byte('a') and data[1] == byte('a') and data[2] == 0'u8 and
        data[3] == byte('b') and data[4] == byte('b') and data[5] == 0'u8 and
        data[6] == byte('c') and data[7] == byte('c') and data[8] == 0'u8 and
        data[9] == byte('d') and data[10] == byte('d') and data[11] == 0'u8 and
        data[12] == byte('e') and data[13] == byte('e') and data[14] == 0'u8 and
        data[15] == 0'u8)
      if dispatch:
        var pos = 2
        var opts: seq[(string, string)] = @[]
        while pos < data.len:
          let (key, nextPos) = readCStringByteSeq(data, pos)
          if key.len == 0:
            break
          let (val, finalPos) = readCStringByteSeq(data, nextPos)
          opts.add (key, val)
          pos = finalPos
        symexTarget("b7r2_1a_done")
        result = 1
      else:
        result = 2
    let r = symexFind(sut, tLabel("b7r2_1a_done"))
    check r.status == sxSat

  test "B7r2-1a-red trip-wire: the SAME wrapped shape with a non-`.len` bound now proves sxSat -- genuine concrete-replay reachability, not a fast-path or budget artifact":
    ## ADJUDICATED GENUINE (diagnosis round after bea6921, walker v110):
    ## this pin's ORIGINAL `sxUnknown` was an artifact of `iekSeqAdd`'s
    ## pre-N47 raw raise, not of the non-`.len` bound denying the loop a
    ## fast-path/closed-form recognition as the pin's own name/doc claimed.
    ## `opts: seq[(string, string)]` (tuple element -- `iekSeqAdd`'s
    ## "unsupported elem kind" arm) is mutated via `opts.add (key, val)`
    ## inside this SAME loop; pre-N47 that was a bare `raise
    ## newException(ValueError, ...)` which, whenever the walker's path
    ## exploration touched it on ANY path, unwound to `runSymexImpl`'s
    ## outermost catch-all and WHOLE-RUN-POISONED the entire result to
    ## `sxUnknown` -- discarding even an UNRELATED path that had already
    ## (or would otherwise) reach `symexTarget` via genuine concrete
    ## replay. N47 (walker v109) converted that raw raise to an in-band,
    ## PATH-SCOPED degrade; post-fix, the poisoning is confined to the one
    ## path that actually executes `opts.add`, and ADR-0012's sxSat-wins
    ## precedence lets a genuine `sxSat` from another path stand.
    ##
    ## The genuine reachability itself needs no fast path at all: the
    ## `symexAssume`d content pins `data[2] == 0'u8`, so `dispatch = true`'s
    ## FIRST `readCStringByteSeq(data, 2)` call returns an EMPTY key
    ## immediately (offset 2 holds the terminator) -- `if key.len == 0:
    ## break` fires after exactly ONE real loop iteration, well inside
    ## `maxLoopUnwind` (5), reaching `symexTarget` by ordinary k-unroll
    ## BEFORE `opts.add` (reached only on a non-empty-key iteration) is
    ## ever called on the `dispatch=true` branch that hits the target.
    ## Verified below by replaying the witness through the real
    ## `readCStringByteSeq` helper (the same witness-replay style
    ## `tsymex_r6_b7r_bytescan.nim`'s "-cross" tests use), not merely by
    ## trusting the solver's reported status.
    ##
    ## Kept as a trip-wire in spirit: pinned EXACTLY `sxSat` (not `>=` or a
    ## loose "not unknown"), so a future regression that reintroduces
    ## whole-run poisoning (or otherwise loses this path) flips it loudly.
    proc sut(data: seq[byte], dispatch: bool): int =
      symexAssume(data.len == 16)
      symexAssume(
        data[0] == byte('a') and data[1] == byte('a') and data[2] == 0'u8 and
        data[3] == byte('b') and data[4] == byte('b') and data[5] == 0'u8 and
        data[6] == byte('c') and data[7] == byte('c') and data[8] == 0'u8 and
        data[9] == byte('d') and data[10] == byte('d') and data[11] == 0'u8 and
        data[12] == byte('e') and data[13] == byte('e') and data[14] == 0'u8 and
        data[15] == 0'u8)
      if dispatch:
        let n = data.len
        var pos = 2
        var opts: seq[(string, string)] = @[]
        while pos < n:
          let (key, nextPos) = readCStringByteSeq(data, pos)
          if key.len == 0:
            break
          let (val, finalPos) = readCStringByteSeq(data, nextPos)
          opts.add (key, val)
          pos = finalPos
        symexTarget("b7r2_1a_red_done")
        result = 1
      else:
        result = 2
    let r = symexFind(sut, tLabel("b7r2_1a_red_done"))
    check r.status == sxSat
    # Witness-replay justification: the `symexAssume`s pin `data` exactly, so
    # the witness must reproduce them, and replaying the real helper confirms
    # the FIRST key read is genuinely empty -- the concrete mechanism that
    # reaches the target in 1 real iteration, independent of any fast path.
    let (data, dispatch) = r.witness
    check dispatch == true
    check data.len == 16
    check data == @[97'u8, 97, 0, 98, 98, 0, 99, 99, 0, 100, 100, 0, 101, 101, 0, 0]
    let (firstKey, _) = readCStringByteSeq(data, 2)
    check firstKey.len == 0

suite "symex round-6 B7r2 -- BLOCKER B7-1(b): pair-loop followed by construction now reaches its target (was CR-17 classified decline)":

  test "B7r2-1b: literal-seeded pair-loop, UNCONDITIONAL (no if-wrap), followed by variant construction -> the post-construction target is reachable":
    ## Mirrors chapulin's `decodeOackTwin` arm shape exactly: the loop's
    ## own locals (`pos`/`opts`) are NEVER read after construction --
    ## `opts` is discarded, matching B6's own committed scope ("the
    ## no-defect proof for the whole option arm WITHOUT MODELING THE
    ## FOLD"). A small (one-pair) region keeps the query cheap while still
    ## exercising construction immediately after a closed-form-eligible
    ## loop.
    proc sut(data: seq[byte]): Packet =
      symexAssume(data.len == 4)
      symexAssume(data[0] == byte('a') and data[1] == byte('a') and
                  data[2] == 0'u8 and data[3] == 0'u8)
      var pos = 0
      var opts: seq[(string, string)] = @[]
      while pos < data.len:
        let (key, nextPos) = readCStringByteSeq(data, pos)
        if key.len == 0:
          break
        let (val, finalPos) = readCStringByteSeq(data, nextPos)
        opts.add (key, val)
        pos = finalPos
      result = Packet(kind: pkOack, oackOptions: @[])
      symexTarget("b7r2_1b_done")
    let r = symexFind(sut, tLabel("b7r2_1b_done"))
    check r.status == sxSat

suite "symex round-6 B7r2 -- BLOCKER B7-1(c): call-boundary seq[(string,string)]-returning helper no longer poisons its caller":

  test "B7r2-1c: caller binds+discards a helper's seq[(string,string)] RETURN, then constructs -- target past the call is reachable (was seNestedSeqUnsupported whole-run poison)":
    proc callerSut(data: seq[byte]): Packet =
      if data.len < 2:
        raise newException(TftpDecodeError, "short")
      let opts = readOptionsTwinLike(data, 2)
      discard opts
      result = Packet(kind: pkOack, oackOptions: @[])
      symexTarget("b7r2_1c_done")
    let r = symexFind(callerSut, tLabel("b7r2_1c_done"))
    check r.status == sxSat

  test "B7r2-1c companion: a genuine defect on a CLEAN sibling of the SAME caller (never touching the seq[(string,string)] call) is still found -- the generalized placeholder allocates rather than raising, so it never reaches this unrelated path either":
    proc callerSut2(data: seq[byte]): Packet =
      if data.len < 2:
        raise newException(TftpDecodeError, "short")
      let wireOp = readU16Twin(data, 0)
      if wireOp == 6:
        let opts = readOptionsTwinLike(data, 2)
        discard opts
        result = Packet(kind: pkOack, oackOptions: @[])
      else:
        discard data[99999]   # unconditional, always-unguarded -- a real IndexDefect
    let r = symexFind(callerSut2, tIndexError())
    check r.status == sxRaised

suite "symex round-6 B7r2 -- opOack-faithful composite (dispatch + call-boundary readOptions + variant construction), chapulin's real decodeOackTwin shape, end-to-end":

  test "B7r2-composite: header check + opcode range check + `if wireOp == 6:` dispatch + call-boundary readOptions + construction -> the post-construction target is reachable":
    proc decodeOackTwinLike(data: seq[byte]): Packet =
      if data.len < 2:
        raise newException(TftpDecodeError, "packet too short")
      let wireOp = readU16Twin(data, 0)
      if wireOp < 1 or wireOp > 6:
        raise newException(TftpDecodeError, "invalid opcode")
      if wireOp == 6:
        let opts = readOptionsTwinLike(data, 2)
        discard opts   # B6 scope: option-region CONTENT (the fold) is never modeled.
        result = Packet(kind: pkOack, oackOptions: @[])
        symexTarget("b7r2_composite_done")
      else:
        discard
    let r = symexFind(decodeOackTwinLike, tLabel("b7r2_composite_done"))
    check r.status == sxSat

  test "B7r2-composite sibling: a genuine IndexDefect on a DISJOINT arm of the SAME composite proc is still found (the wireOp==6 arm's own machinery never poisons it)":
    proc decodeOackTwinLike2(data: seq[byte]): Packet =
      if data.len < 2:
        raise newException(TftpDecodeError, "packet too short")
      let wireOp = readU16Twin(data, 0)
      if wireOp < 1 or wireOp > 6:
        raise newException(TftpDecodeError, "invalid opcode")
      if wireOp == 6:
        let opts = readOptionsTwinLike(data, 2)
        discard opts
        result = Packet(kind: pkOack, oackOptions: @[])
      elif wireOp == 3:
        discard data[99999]
      else:
        discard
    let r = symexFind(decodeOackTwinLike2, tIndexError())
    check r.status == sxRaised

suite "symex round-6 B7r2 -- BLOCKER B7-2 (case/else-raise sibling poisoning): CLOSED `cac15e6` (walker v124), now pinned at the FIXED behavior":

  test "B7r2-2: a case-match with else-raise over scanned content no longer poisons a DISJOINT sibling branch -- the sibling's own target is reachable, and no case-as-expression decline is emitted":
    proc parseModeLike(s: string): int =
      case s.toLowerAscii
      of "octet": 1
      of "netascii": 2
      else: raise newException(TftpDecodeError, "unknown transfer mode: " & s)
    proc sut(wireOp: int, modeStr: string, blockNum: int) =
      if wireOp == 1:
        let m = parseModeLike(modeStr)
        discard m
      elif wireOp == 3:
        # Disjoint from wireOp==1's parseModeLike call -- structurally
        # unrelated to case-as-expression / scanned-string content.
        if blockNum == 5:
          symexTarget("b7r2_2_sibling_reached")
    let r = symexFind(sut, tLabel("b7r2_2_sibling_reached"))
    ## Verified against this EXACT SUT (including `s.toLowerAscii`, which the
    ## minimal r7 repro omits) via a standalone probe at walker v124 —
    ## `tsymex_r6_b7r2_pathscope` itself cannot run on Linux/podman, so the
    ## assertion below was changed on measured evidence, not inference.
    check r.status == sxSat
    ## The old trip-wire asserted the case-as-expression decline was PRESENT.
    ## Invert it: its continued absence is now the property worth pinning, so
    ## a regression that reintroduces the parse-time decline flips this red.
    for e in r.errors:
      check not (e.kind == feUnsupportedExprKind and "nnkCaseStmt" in e.msg)

suite "symex round-6 B7r2 -- regression: a genuinely-unmodeled whole-proc shape still declines (never a crash), unaffected by this slice":

  test "B7r2-regress: Table[string, seq[int]] (unsupported value type) still classifies cleanly":
    ## Unrelated to either fix landed this slice (int-offset locals /
    ## generalized seq placeholder) -- a live control confirming the
    ## standing "walker never crashes" invariant still holds after this
    ## slice's two changes.
    proc sut(x: int): bool =
      var t: Table[string, seq[int]]
      t["k"] = @[x]
      result = t["k"].len > 0
    let r = symexFind(sut, tIndexError())
    check r.status == sxUnknown
    check r.errors.len > 0

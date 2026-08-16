## Round-6 B1 (+B1a) — string-backed `seq[byte]` params (ADR-0028 Leg 1).
##
## `ParseCtx.stringBackedParams` (`collectStringBackedByteSeqParams`,
## `dsl_parser.nim`) recognizes a `seq[byte]` PARAM as string-backed when
## some loop in its consuming proc body matches the canonical scan-idiom
## SHAPE (`tryMatchScanIdiomShape` — the SAME predicate
## `tryRecognizeScanIdiom` uses, extracted so classifier and recognizer
## share one check by construction) with a byte-range literal delimiter,
## minus any param with a mutation site. Such a param allocates via the
## itString machinery (`allocateSym`) instead of the array `itSeq`
## machinery; `parseExpr`'s bracket/call-form `[]`/`.len` dispatch for an
## `itSeq` receiver routes a string-backed one through `iekStrSubstr`/
## `iekStrAt`/`iekStrLen` (the SAME IR kinds a declared-`string` receiver
## uses) instead of the array `iekSeqSlice`/`isIndex`/`iekSeqLen` IR.
##
## Pre-B1, `iekSeqSlice`'s lowering hard-requires `svSeq` and the `isIndex`/
## `iekSeqLen` walker arms hard-`doAssert`/bare-`raise` on anything other
## than the array/table/set kinds they knew about — so a representation
## mismatch between a param's DECLARED `itSeq` type and its (post-B1)
## ACTUAL `svString` allocation is a live crash surface unless the walker
## itself gains `svString` support. This file pins BOTH halves: the
## parse-time dispatch (SUT 1's `data[4 .. ^1]`/`data.len` directly on the
## string-backed param) AND the walk-time totality backstop (SUT 1's
## `payload.len`/`payload[0]` on a LOCAL derived from the slice — its
## declared type is still `seq[byte]`, so ITS OWN dispatch stays the
## ordinary array IR, and only the `isIndex`/`iekSeqLen` walker arms'
## new `svString` support makes it prove instead of crash).
##
## Witness-rendering note (flagged for review, out of B1's stated scope):
## a string-backed param's model value lands in `RawWitness.strVals` at
## extraction time (`extractLeaf`'s `svString` arm), but the GENERATED
## reader for a `seq[byte]`-declared param (`emitTyAndReader`, `symex.nim`)
## calls `readSeqUInt8`, which reads `RawWitness.seqLens`/`.uintVals` —
## absent for a string-backed param. `readSeqUInt8` degrades GRACEFULLY
## (`if w.seqLens.hasKey(name): ... else: 0` — an empty `seq[byte]`, not a
## KeyError/crash), so this is a wrong-but-harmless witness for that one
## param, not a §0 crash-totality violation; mirrors the pre-existing,
## deliberately out-of-scope CR-2c `seq[Object]` witness-reader gap noted
## at the A6 exit gate. This file therefore asserts `status` only, never
## `.witness` content, for string-backed SUTs.
##
## Walker version: 77 -> 78 (verdict-changing: previously-crashing shapes
## on a string-backed `seq[byte]` param now resolve to real verdicts).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# SUT 1 — the opData-style shape: a scan loop (triggers string-backing) plus
# a `data[4 .. ^1]` slice bound to a local, then `.len`/`[]` on that local.
# Pre-B1: the slice itself already worked (iekSeqSlice on plain svSeq, B1
# didn't exist), but under B1's representation swap `data`'s consuming loop
# now allocates it `svString` — proving the slice AND the local's `.len`/`[]`
# reads requires the full B1 mechanism (parser dispatch for `data` itself,
# walker backstop for the derived local `payload`).
# ---------------------------------------------------------------------------

proc opDataStyleSlice(data: seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  let payload = data[4 .. ^1]
  if payload.len > 3 and payload[0] == 42'u8:
    symexTarget("opdata_slice_sat")

proc opDataStyleSliceIndexUnsafe(data: seq[byte]) =
  ## Same shape, but the `[]` read is UNGUARDED — proves the `isIndex`
  ## walker backstop's OOB-defect fork over an `svString` receiver is
  ## REACHABLE and CORRECT (a real `IndexDefect` is findable), not just
  ## non-crashing. (A whole-frontier UNSAT "never IndexDefects" proof was
  ## considered instead but, AT THE TIME B1 landed, hit an UNRELATED
  ## limitation: the consuming scan loop was never lifted to a closed form
  ## for a `seq[byte]` receiver — B1a deliberately did not widen
  ## `tryRecognizeScanIdiom` for it, only the slice/index/len OPS changed
  ## representation — so it always k-unrolled. Round-6 B7-rider (walker
  ## v87) LATER widened the receiver gate on all four scan recognizers,
  ## including this file's own `opDataStyleSlice`/`opDataStyleSliceIndexUnsafe`
  ## loop (a genuine Q1/B0 shape) — so this SUT's leading scan now lifts to
  ## the closed form too. That is orthogonal to what THIS pin checks
  ## (`payload[0]`'s own OOB-defect reachability, from a SEPARATE,
  ## slice-derived array-modeled local, unaffected either way) and does not
  ## change this test's own verdict; kept as a SAT-only pin (not upgraded to
  ## the whole-frontier UNSAT proof) since `maxLoopUnwind`'s own doc comment
  ## still applies to any OTHER unrecognized-shape loop in the corpus:
  ## raising the bound does not help an unresolved SYMBOLIC-trip-count loop
  ## decide an UNSAT query — "decidability, not budget".)
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  let payload = data[4 .. ^1]
  discard payload[0]

# ---------------------------------------------------------------------------
# SUT 2 — `data.len` directly on the string-backed param itself (the
# `iekStrLen` PARSER dispatch, not the walker backstop — `data` is a bare
# symbol in `ctx.stringBackedParams`, unlike SUT 1's derived `payload`).
# ---------------------------------------------------------------------------

proc dataLenStringBacked(data: seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  if data.len == 37:
    symexTarget("data_len_sat")

# ---------------------------------------------------------------------------
# SUT 3 — mutation-fallback: `data` has the SAME qualifying scan loop, but
# also a `.add` mutation site — `scanShapeReceiverMutated` must exclude it
# from string-backing (Z3 String is immutable), so it stays array-modeled
# (plain `svSeq`) and every existing seq operation (the scan loop's reads,
# `.add`, `.len`, `[]`) keeps working exactly as it did pre-B1.
# ---------------------------------------------------------------------------

proc mutatedByteSeqStaysArray(data: var seq[byte]) =
  ## `data` has the SAME qualifying scan loop as SUT 1/2, but ALSO a `.add`
  ## mutation site — `scanShapeReceiverMutated` must exclude it from
  ## string-backing. `iekSeqAdd`'s mutation lowering only models width-64
  ## seq elements today (a PRE-EXISTING gap, unrelated to B1 — `seq[byte]`
  ## `.add` was never modeled; confirmed via the no-loop diagnostic below,
  ## which hits the IDENTICAL gap with no string-backing candidacy at all)
  ## — caught by the outermost Defect/CatchableError net
  ## (`weInternalWalkerFault`), never a crash. If the exclusion regressed
  ## (data wrongly promoted string-backed despite the `.add` site), `data`
  ## would allocate `svString`, and `iekSeqAdd`'s OWN `doAssert recv.kind ==
  ## svSeq` would fire instead — a DIFFERENT, distinguishable message this
  ## test pins on by content, not just by status.
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  data.add(9'u8)
  if data.len > 0 and data[0] == 42'u8:
    symexTarget("mutated_stays_array")

# DIAGNOSTIC (no scan loop -> never a string-backed candidate at all):
# the pre-existing `iekSeqAdd` width-8 gap in isolation — the GROUND TRUTH
# `mutatedByteSeqStaysArray` above is compared against.
proc addMutationNoLoopDiagnostic(data: var seq[byte]) =
  data.add(9'u8)
  if data.len > 0 and data[0] == 42'u8:
    symexTarget("add_no_loop_sat")

# ---------------------------------------------------------------------------
# SUT 4 — regression guard: a param with NO qualifying consuming loop stays
# ordinary array-modeled (B1a's predicate never fires), and a param whose
# scan loop compares against something other than a byte-range literal
# delimiter (out of the collector's `litOk` acceptance) likewise stays
# array-modeled. Neither shape existed pre-B1 either; both must keep
# resolving exactly as before (no behavior change for unaffected params).
# ---------------------------------------------------------------------------

proc noConsumingLoop(data: seq[byte]) =
  if data.len > 0 and data[0] == 42'u8:
    symexTarget("no_consuming_loop_sat")

suite "symex round-6 B1 — string-backed seq[byte] params":

  test "B1-1: data[4 .. ^1] on a string-backed param proves SAT (was a crash pre-B1)":
    let r = symexFind(opDataStyleSlice, tLabel("opdata_slice_sat"))
    check r.status == sxSat

  test "B1-2: an unguarded payload[0] read finds a real IndexDefect (isIndex svString backstop is sound)":
    let r = symexFind(opDataStyleSliceIndexUnsafe, tIndexError())
    check r.status == sxRaised

  test "B1-3: data.len on a string-backed param proves SAT (iekStrLen parser dispatch)":
    let r = symexFind(dataLenStringBacked, tLabel("data_len_sat"))
    check r.status == sxSat

  test "B1-4: a mutated seq[byte] param stays array-modeled (pre-existing add-width gap, not the string-mismatch fault)":
    let r = symexFind(mutatedByteSeqStaysArray, tLabel("mutated_stays_array"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check "unsupported width" in r.errors[0].msg
    check "receiver not svSeq" notin r.errors[0].msg

  test "B1-4 diagnostic: the no-loop ground truth hits the IDENTICAL pre-existing gap":
    let r = symexFind(addMutationNoLoopDiagnostic, tLabel("add_no_loop_sat"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check "unsupported width" in r.errors[0].msg

  test "B1-5: a seq[byte] param with no consuming loop is unaffected (regression sweep)":
    let r = symexFind(noConsumingLoop, tLabel("no_consuming_loop_sat"))
    check r.status == sxSat

suite "symex round-6 B1 — walker version pin":

  test "walker version floor >= 78 (string-backed seq[byte] params)":
    check parseInt(symexWalkerVersion) >= 78

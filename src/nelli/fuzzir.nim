## IR-aware mutation kernels for the fuzz adapter (#110).
##
## Leaf module: depends on `choice` (for `ChoiceNode` + constraints),
## `rng` (for the mutator's randomness), and `datasource` (for `Span`).
## Nothing engine-side imports back, so this module is independently
## testable and stays out of the fuzz↔engine dependency graph.
##
## **The architectural payoff over byte mutation.** Byte-level mutators
## (`mutateByteFlip` etc.) rewrite the raw byte stream that the byte-mode
## DataSource decodes into choices. A flipped bit in a length-prefix byte
## frequently decodes into an out-of-range length that gets clamped or
## triggers `Overrun`, wasting the iteration. IR mutators rewrite the
## typed choice sequence directly: every output respects the constraints
## the strategy declared (`intC.min/max`, `boolC.p`, kind-aligned span
## boundaries). Mutations are structurally valid by construction.
##
## All mutators are **total** — defined for every input. When the
## structural precondition for a mutator can't be satisfied (e.g.
## `mutateIRPerturbInteger` on an IR with no integer node, or
## `mutateIRSpanSplice` with no matching-label span pair), the mutator
## returns the input unchanged. This "identity on no-op" contract lets
## the fuzz loop call any mutator unconditionally; an unchanged result
## simply produces no new coverage and the loop picks a different
## mutator next iteration.

import ./choice, ./rng, ./datasource, ./int128, ./coverage
import std/options

proc pickIntegerIndex(rng: var SplitMix64, base: seq[ChoiceNode]): int =
  ## Index of a random ckInteger node, or `-1` if none. Selection is
  ## uniform across all integer nodes — *not* across all nodes, so a
  ## sequence with one int among ten booleans still finds it.
  var intIndices: seq[int]
  for i, n in base:
    if n.kind == ckInteger and not n.wasForced:
      intIndices.add i
  if intIndices.len == 0: return -1
  intIndices[int(rng.next mod uint64(intIndices.len))]

proc logScaledDeltasForWidth(width: int64): seq[int64] =
  ## ±2^k for k ∈ [0, log2(width)]; big-to-small. Identical semantics to
  ## the targeted-PBT hill-climb's `logScaledIntDeltas`; duplicated here
  ## to keep this module a true leaf (no engine deps).
  if width <= 0: return @[]
  var k = 0
  while k < 62 and (1'i64 shl (k+1)) <= width:
    inc k
  while k >= 0:
    let d = 1'i64 shl k
    result.add d
    result.add -d
    dec k

proc mutateIRPerturbInteger*(rng: var SplitMix64,
                             base: seq[ChoiceNode]): seq[ChoiceNode] =
  ## Pick a random ckInteger node and perturb it by a constraint-
  ## respecting ±2^k delta. Identity on inputs with no integer nodes.
  ##
  ## The perturbation set is log-scaled by the constraint width, matching
  ## the targeted-PBT hill-climb so the mutator's "step distribution"
  ## already covers fine and coarse moves with one draw.
  let i = pickIntegerIndex(rng, base)
  if i < 0: return base
  let node = base[i]
  let lo = node.intC.min
  let hi = node.intC.max
  if lo >= hi: return base
  let width = hi - lo
  # Bound the log-scale by an int64 view of the width; the IR uses Int128
  # but practical fuzz ranges fit in int64 comfortably.
  let width64 = if fitsInt64(width): toInt64(width) else: high(int64)
  let deltas = logScaledDeltasForWidth(width64)
  if deltas.len == 0: return base
  let d = deltas[int(rng.next mod uint64(deltas.len))]
  var newVal = node.intVal + toInt128(d)
  if newVal < lo: newVal = lo
  if newVal > hi: newVal = hi
  if newVal == node.intVal:
    # Stepped onto the original; try the opposite direction once.
    newVal = node.intVal - toInt128(d)
    if newVal < lo: newVal = lo
    if newVal > hi: newVal = hi
  if newVal == node.intVal: return base  # constraint pinned both directions
  result = base
  result[i] = ChoiceNode(kind: ckInteger, intC: node.intC, intVal: newVal)

proc kindBoundaryAlternatives(node: ChoiceNode): seq[ChoiceNode] =
  ## Kind-respecting boundary values for `node` (excluding `node` itself).
  ## Mirrors `engine/targeting.nim/perturbations` but duplicated here so
  ## fuzzir.nim remains a leaf module (no engine deps).
  if node.wasForced: return
  case node.kind
  of ckInteger:
    let lo = node.intC.min
    let hi = node.intC.max
    let st = node.intC.shrinkTowards
    var cand: seq[ChoiceInt] = @[st, lo, hi]
    if lo + toInt128(1) <= hi: cand.add lo + toInt128(1)
    for c in cand:
      if c != node.intVal and c >= lo and c <= hi:
        result.add ChoiceNode(kind: ckInteger, intC: node.intC, intVal: c)
  of ckBoolean:
    result.add ChoiceNode(kind: ckBoolean, boolC: node.boolC,
                          boolVal: not node.boolVal)
  of ckFloat:
    let cons = node.floatC
    for v in [0.0, 1.0, -1.0]:
      if v != node.floatVal and v >= cons.min and v <= cons.max:
        result.add ChoiceNode(kind: ckFloat, floatC: cons, floatVal: v)
  of ckBytes:
    let cons = node.bytesC
    if node.bytesVal.len > 0 and cons.minSize == 0:
      result.add ChoiceNode(kind: ckBytes, bytesC: cons, bytesVal: @[])
    let allZero = newSeq[byte](node.bytesVal.len)
    if allZero != node.bytesVal:
      result.add ChoiceNode(kind: ckBytes, bytesC: cons, bytesVal: allZero)
  of ckString:
    let cons = node.strC
    if node.strVal.len > 0 and cons.minSize == 0:
      result.add ChoiceNode(kind: ckString, strC: cons, strVal: "")

proc mutateIRKindBoundary*(rng: var SplitMix64,
                           base: seq[ChoiceNode]): seq[ChoiceNode] =
  ## Pick a random non-forced node and replace it with a kind-respecting
  ## boundary value (the `perturbations()` set from the explain phase:
  ## min/max/shrinkTowards for int, ¬v for bool, ±1 / 0 for float, empty
  ## for bytes/string when permitted). Identity when no node has any
  ## boundary alternative (every node forced, or every node already at
  ## the only legal value).
  ##
  ## High coverage-novelty per mutation: boundary values are the inputs
  ## most likely to flip branch decisions in the SUT.
  if base.len == 0: return base
  # Build an index of candidates (non-forced nodes with ≥1 alternative).
  # The mutator picks one uniformly; this avoids a wasted draw on nodes
  # that would no-op.
  var candidates: seq[int]
  for i, n in base:
    if not n.wasForced and kindBoundaryAlternatives(n).len > 0:
      candidates.add i
  if candidates.len == 0: return base
  let i = candidates[int(rng.next mod uint64(candidates.len))]
  let alts = kindBoundaryAlternatives(base[i])
  let pick = alts[int(rng.next mod uint64(alts.len))]
  result = base
  result[i] = pick

proc mutateIRSpanSplice*(rng: var SplitMix64,
                         base, donor: seq[ChoiceNode],
                         baseSpans, donorSpans: seq[Span]): seq[ChoiceNode] =
  ## Pick a span in `base` and a span in `donor` that share a `label`,
  ## then replace base's slice with donor's slice. Structural crossover:
  ## because spans are the strategy's own structural boundaries
  ## (`startSpan` / `endSpan` calls), splicing along them yields IR
  ## sequences that the strategy can still parse.
  ##
  ## Total. Returns `base` unchanged when either side has no spans, or
  ## when no `(baseSpan, donorSpan)` pair shares a label.
  if baseSpans.len == 0 or donorSpans.len == 0: return base
  # Build the candidate list of matching-label pairs. Uniform random pick
  # over pairs preserves the structural-equivalence-class semantics; an
  # alternative would weight by donor-span length, but parsimony first.
  var pairs: seq[tuple[bs, ds: int]]
  for i, bs in baseSpans:
    for j, ds in donorSpans:
      if bs.label == ds.label and
         bs.start >= 0 and bs.finish <= base.len and
         ds.start >= 0 and ds.finish <= donor.len:
        pairs.add (bs: i, ds: j)
  if pairs.len == 0: return base
  let pair = pairs[int(rng.next mod uint64(pairs.len))]
  let bs = baseSpans[pair.bs]
  let ds = donorSpans[pair.ds]
  # Reassemble: base[0..bs.start) ++ donor[ds.start..ds.finish) ++ base[bs.finish..]
  result = newSeqOfCap[ChoiceNode](
    bs.start + (ds.finish - ds.start) + (base.len - bs.finish))
  for k in 0 ..< bs.start: result.add base[k]
  for k in ds.start ..< ds.finish: result.add donor[k]
  for k in bs.finish ..< base.len: result.add base[k]

proc pickValidSpan(rng: var SplitMix64, base: seq[ChoiceNode],
                   spans: seq[Span]): int =
  ## Index of a randomly-chosen span whose `[start, finish)` is in
  ## bounds for `base`. `-1` when no valid span exists.
  var valid: seq[int]
  for i, sp in spans:
    if sp.start >= 0 and sp.finish <= base.len and sp.finish > sp.start:
      valid.add i
  if valid.len == 0: return -1
  valid[int(rng.next mod uint64(valid.len))]

proc mutateIRSpanDelete*(rng: var SplitMix64, base: seq[ChoiceNode],
                         spans: seq[Span]): seq[ChoiceNode] =
  ## Remove the nodes within a randomly-chosen span. The strategy may
  ## reject the result (e.g. a list with fewer elements than `minLen`),
  ## which fuzzOnceIR maps to `foRejected`. That's the right semantic:
  ## the deletion attempts a *structurally smaller* candidate, and the
  ## fuzz loop discards rejections naturally. Total; identity when no
  ## valid span exists.
  let i = pickValidSpan(rng, base, spans)
  if i < 0: return base
  let sp = spans[i]
  result = newSeqOfCap[ChoiceNode](base.len - (sp.finish - sp.start))
  for k in 0 ..< sp.start: result.add base[k]
  for k in sp.finish ..< base.len: result.add base[k]

proc mutateIRSpanDuplicate*(rng: var SplitMix64, base: seq[ChoiceNode],
                            spans: seq[Span]): seq[ChoiceNode] =
  ## Insert a copy of a randomly-chosen span immediately after itself.
  ## Common natural use case: grows a list/string by one structural
  ## unit. Total; identity when no valid span exists.
  let i = pickValidSpan(rng, base, spans)
  if i < 0: return base
  let sp = spans[i]
  result = newSeqOfCap[ChoiceNode](base.len + (sp.finish - sp.start))
  for k in 0 ..< sp.finish: result.add base[k]
  for k in sp.start ..< sp.finish: result.add base[k]
  for k in sp.finish ..< base.len: result.add base[k]

## --- I2S (input-to-state) replacement + auto-dictionary (RFC-fuzzer-nextgen
## G5, §G-cmp) --------------------------------------------------------------
##
## The RedQueen-style consumer of G4's `{.covercmp.}` operand-pair log
## (`coverage.nim`'s `CmpLogEntry`). nelli knows which draw produced which
## concrete value, so "find this operand in the input and replace it with the
## other" is EXACT for the *identity-flow* class (the compared value equals a
## drawn value unmodified) — no byte-offset guessing. Scope boundary (RFC
## round-1 fix): once a draw flows through a transform before the comparison,
## the operand->choice-node lookup simply finds no match (falls through to
## the dictionary, then to identity) — this is G6's transparency-descriptor
## domain, not attempted here.
##
## **Why `coverage.nim` is imported here** (not just by `fuzz.nim`): both
## modules are leaves (`coverage.nim`'s own header: "depends on nothing else
## in nelli"), so `fuzzir <- coverage` adds no cycle — `fuzzir.nim` stays
## engine-free, `coverage.nim` stays fuzzir-free.

proc decodeIntCandidates(raw: uint64): seq[ChoiceInt] =
  ## The two ways a `CmpLogEntry.lhsInt`/`rhsInt` 64-bit field could decode
  ## back to the ORIGINAL compared value, since the log (see `logCmp` in
  ## coverage.nim) does not retain whether the source `T` was signed:
  ## `cast[int64]` recovers an exact value if `T` was signed (sign extension
  ## preserves numeric value up through int64); reading the raw `uint64`
  ## recovers it if `T` was unsigned (zero extension). Trying both and
  ## matching against the node's own EXACT `ChoiceInt` is what makes the
  ## lookup exact without needing to know `T`'s signedness at all.
  result.add toInt128(cast[int64](raw))
  let u = toInt128(raw)
  if u != result[0]: result.add u

proc bestIntReplacement(node: ChoiceNode, cands: seq[ChoiceInt]): ChoiceNode =
  ## The node's own value replaced by whichever of `cands` fits its declared
  ## `[min, max]`; if none fits, the FIRST candidate clamped into range (the
  ## RFC's "clamp ... as the constraint allows" — an integer node's
  ## constraint is a closed interval, so clamping is always well-defined and
  ## never needs to fall back to skipping).
  let lo = node.intC.min
  let hi = node.intC.max
  for c in cands:
    if lo <= c and c <= hi:
      return ChoiceNode(kind: ckInteger, intC: node.intC, intVal: c)
  ChoiceNode(kind: ckInteger, intC: node.intC, intVal: clamp(cands[0], lo, hi))

proc clampBytesLen(v: seq[byte], c: BytesConstraints): seq[byte] =
  result = v
  if result.len > c.maxSize: result.setLen(c.maxSize)
  while result.len < c.minSize: result.add 0'u8

proc bestBytesReplacement(node: ChoiceNode, want: seq[byte]): ChoiceNode =
  ## Exact replacement when `want`'s length already satisfies the node's
  ## `BytesConstraints`; otherwise truncated/zero-padded into range (the
  ## RFC's "clamp ... as the constraint allows" — bytes have no interval-set
  ## legality concern the way string codepoints do, so clamp is always safe).
  if permits(node.bytesC, want):
    ChoiceNode(kind: ckBytes, bytesC: node.bytesC, bytesVal: want)
  else:
    ChoiceNode(kind: ckBytes, bytesC: node.bytesC, bytesVal: clampBytesLen(want, node.bytesC))

proc tryStringReplacement(node: ChoiceNode, want: string): Option[ChoiceNode] =
  ## Exact replacement ONLY when `want` already satisfies the node's
  ## `StringConstraints` (codepoint-length bounds AND interval-set
  ## membership) — unlike ints/bytes, a string has no safe generic "clamp"
  ## (truncating codepoints or the interval set could produce ill-formed
  ## output the strategy never would have), so an out-of-constraint `want`
  ## is skipped rather than coerced.
  if permits(node.strC, want): some(ChoiceNode(kind: ckString, strC: node.strC, strVal: want))
  else: none(ChoiceNode)

proc collectI2SMatches(base: seq[ChoiceNode],
                       cmpLog: seq[CmpLogEntry]): seq[tuple[idx: int, repl: ChoiceNode]] =
  ## Every `(node index, replacement)` pair the operand log's typed entries
  ## exactly justify: a `ChoiceNode` whose concrete value equals ONE side of
  ## a logged comparison earns a candidate replacing it with the OTHER side.
  ## Both directions are tried (either operand could be the drawn value) —
  ## `logCmp`'s call site doesn't distinguish which side was "the input"
  ## from "the constant". A replacement identical to the node's current
  ## value is dropped (would be a no-op mutation).
  for entry in cmpLog:
    case entry.kind
    of clkInt:
      let lhsCands = decodeIntCandidates(entry.lhsInt)
      let rhsCands = decodeIntCandidates(entry.rhsInt)
      for i, node in base:
        if node.kind != ckInteger or node.wasForced: continue
        if node.intVal in lhsCands:
          let r = bestIntReplacement(node, rhsCands)
          if r != node: result.add (i, r)
        if node.intVal in rhsCands:
          let r = bestIntReplacement(node, lhsCands)
          if r != node: result.add (i, r)
    of clkBytes:
      for i, node in base:
        if node.kind != ckBytes or node.wasForced: continue
        if node.bytesVal == entry.lhsBytes:
          let r = bestBytesReplacement(node, entry.rhsBytes)
          if r != node: result.add (i, r)
        if node.bytesVal == entry.rhsBytes:
          let r = bestBytesReplacement(node, entry.lhsBytes)
          if r != node: result.add (i, r)
    of clkString:
      for i, node in base:
        if node.kind != ckString or node.wasForced: continue
        if node.strVal == entry.lhsStr:
          let r = tryStringReplacement(node, entry.rhsStr)
          if r.isSome and r.get != node: result.add (i, r.get)
        if node.strVal == entry.rhsStr:
          let r = tryStringReplacement(node, entry.lhsStr)
          if r.isSome and r.get != node: result.add (i, r.get)

type
  DictValueKind* = enum
    ## Mirrors `CmpLogEntryKind` — the type families the dictionary's
    ## harvested constants come in.
    dvInt, dvBytes, dvString

  DictEntry* = object
    ## One harvested constant, typed. Deliberately NOT a `ChoiceNode`: a
    ## dictionary entry is a bare value with no constraints of its own — it
    ## only becomes a legal node once matched against a TARGET node's
    ## constraints at insertion time (see `dictReplacementCandidates`).
    case kind*: DictValueKind
    of dvInt:    intVal*: ChoiceInt
    of dvBytes:  bytesVal*: seq[byte]
    of dvString: strVal*: string

  Dictionary* = object
    ## RFC-fuzzer-nextgen G5 deliverable 3: the per-campaign auto-dictionary
    ## `harvestDictionary` accumulates into, across every run whose cmp log
    ## was parsed (not only admitted/corpus-growing ones — the RFC's "seen
    ## across the campaign" is broader than "seen in the surviving corpus").
    entries*: seq[DictEntry]

const maxDictEntries* = 512
  ## Bound on `Dictionary.entries` — a campaign's comparisons could log
  ## unboundedly many distinct constants; this caps memory/scan cost the
  ## same way `coverageEdgeCount` caps the bitmap. S3 (deepened
  ## havoc-insertion) may raise this later; G5 just needs a bound that
  ## isn't unbounded growth.

proc containsEntry(dict: Dictionary, e: DictEntry): bool =
  for x in dict.entries:
    if x.kind != e.kind: continue
    case e.kind
    of dvInt:    (if x.intVal == e.intVal: return true)
    of dvBytes:  (if x.bytesVal == e.bytesVal: return true)
    of dvString: (if x.strVal == e.strVal: return true)
  false

proc addDictEntry(dict: var Dictionary, e: DictEntry) =
  if dict.entries.len >= maxDictEntries: return
  if not containsEntry(dict, e): dict.entries.add e

proc harvestDictionary*(dict: var Dictionary, log: seq[CmpLogEntry]) =
  ## Fold every operand seen in `log` into `dict`, deduped. Both int decodes
  ## are harvested (see `decodeIntCandidates`'s doc — signedness is unknown
  ## at harvest time, so both candidate values are kept; a later insertion
  ## match against a real node's constraints picks whichever one fits).
  for entry in log:
    case entry.kind
    of clkInt:
      for c in decodeIntCandidates(entry.lhsInt): addDictEntry(dict, DictEntry(kind: dvInt, intVal: c))
      for c in decodeIntCandidates(entry.rhsInt): addDictEntry(dict, DictEntry(kind: dvInt, intVal: c))
    of clkBytes:
      addDictEntry(dict, DictEntry(kind: dvBytes, bytesVal: entry.lhsBytes))
      addDictEntry(dict, DictEntry(kind: dvBytes, bytesVal: entry.rhsBytes))
    of clkString:
      addDictEntry(dict, DictEntry(kind: dvString, strVal: entry.lhsStr))
      addDictEntry(dict, DictEntry(kind: dvString, strVal: entry.rhsStr))

proc dictReplacementCandidates(base: seq[ChoiceNode],
                               dict: Dictionary): seq[tuple[idx: int, repl: ChoiceNode]] =
  ## Fallback source when the operand log has no direct match for this
  ## input: every dictionary entry that legally replaces some node, kind-
  ## matched. This is deliverable 3's "basic insertion" — S3 deepens
  ## havoc-style insertion (mid-sequence splicing, multiple entries at once)
  ## later; G5 only needs the dictionary to be a real, usable mutation
  ## source, not the full havoc treatment.
  for i, node in base:
    if node.wasForced: continue
    case node.kind
    of ckInteger:
      for e in dict.entries:
        if e.kind != dvInt: continue
        let r = bestIntReplacement(node, @[e.intVal])
        if r != node: result.add (i, r)
    of ckBytes:
      for e in dict.entries:
        if e.kind != dvBytes: continue
        let r = bestBytesReplacement(node, e.bytesVal)
        if r != node: result.add (i, r)
    of ckString:
      for e in dict.entries:
        if e.kind != dvString: continue
        let r = tryStringReplacement(node, e.strVal)
        if r.isSome and r.get != node: result.add (i, r.get)
    else: discard

proc mutateIRI2SReplace*(rng: var SplitMix64, base: seq[ChoiceNode],
                         cmpLog: seq[CmpLogEntry], dict: Dictionary): seq[ChoiceNode] =
  ## The 6th IR mutation operator (RFC-fuzzer-nextgen G5): exact I2S
  ## replacement against `cmpLog` (the PARENT input's own logged comparison
  ## operands — see `fuzz.nim`'s wiring) when a match exists; otherwise a
  ## dictionary-informed insertion from `dict` (deliverable 3); otherwise
  ## identity, matching every other mutator's "total, no-op on no
  ## precondition" contract. `cmpLog` empty (no `{.covercmp.}`
  ## instrumentation, or `FuzzSettings.enableI2S` off) AND `dict` empty is
  ## the pre-G5 case: always identity.
  var matches = collectI2SMatches(base, cmpLog)
  if matches.len == 0:
    matches = dictReplacementCandidates(base, dict)
  if matches.len == 0: return base
  let pick = matches[int(rng.next mod uint64(matches.len))]
  result = base
  result[pick.idx] = pick.repl

proc mutateIRDictInsert*(rng: var SplitMix64, base: seq[ChoiceNode],
                         dict: Dictionary): seq[ChoiceNode] =
  ## RFC-fuzzer-nextgen S3 deliverable 3: a standalone havoc operator that
  ## inserts a harvested G5 dictionary constant directly, INDEPENDENT of the
  ## parent's own `cmpLog` — unlike `mutateIRI2SReplace`, which only reaches
  ## `dict` as a fallback when its own comparison log has no direct match,
  ## this operator always draws from the dictionary (it has no "direct
  ## match" concept of its own to try first). This is what makes the
  ## dictionary a first-class havoc-stack insertion source rather than only
  ## an I2S-arm fallback. Total; identity when `dict` is empty or no node
  ## legally accepts any entry (same clamp/skip discipline as
  ## `dictReplacementCandidates`).
  let candidates = dictReplacementCandidates(base, dict)
  if candidates.len == 0: return base
  let pick = candidates[int(rng.next mod uint64(candidates.len))]
  result = base
  result[pick.idx] = pick.repl

## --- Interesting-value table + havoc stacking (RFC-fuzzer-nextgen S3) ------
##
## Deliverable 2: a table of boundary-interesting values for integer choice
## nodes (min/max/0/±1/min±1/max±1/powers-of-two/off-by-one-from-a-power-of-
## two), clamped/filtered to the node's own declared `[min, max]` — this is
## the IR-level, constraint-respecting analogue of AFL-style byte havoc
## (FUZZ_PLAN D4), operating on typed choice nodes instead of raw bytes so
## every candidate is legal by construction.
##
## Deliverable 1: geometric havoc stacking — `drawHavocStackCount` draws how
## many mutation operators `fuzz.nim`'s loop applies, in sequence, to one
## mutant this iteration.

proc interestingIntValues*(c: IntConstraints): seq[ChoiceInt] =
  ## The boundary-interesting-value table for one integer node's declared
  ## bounds: `min`, `max`, `0`, `±1`, `min±1`, `max±1`, and every power of
  ## two (and its ±1 neighbors, in both signs) up to the 62-bit range
  ## `logScaledDeltasForWidth` already bounds itself to — every candidate
  ## filtered to `[min, max]` (constraint-respecting; never an illegal
  ## node) and deduplicated. `min > max` (an inverted/empty range, which
  ## should not occur for a real node but is handled defensively) yields
  ## the empty table.
  let lo = c.min
  let hi = c.max
  if lo > hi: return @[]
  var raw: seq[ChoiceInt] = @[lo, hi, toInt128(0), toInt128(1), toInt128(-1),
                              lo + toInt128(1), lo - toInt128(1),
                              hi + toInt128(1), hi - toInt128(1)]
  var k = 0
  while k <= 62:
    let p = toInt128(1'i64 shl k)
    raw.add p
    raw.add p - toInt128(1)
    raw.add p + toInt128(1)
    raw.add toInt128(0) - p
    inc k
  for v in raw:
    if v >= lo and v <= hi and v notin result:
      result.add v

proc mutateIRInterestingValue*(rng: var SplitMix64,
                               base: seq[ChoiceNode]): seq[ChoiceNode] =
  ## Replace a random non-forced `ckInteger` node with a boundary value
  ## drawn from its own `interestingIntValues` table. Total; identity when
  ## there is no eligible integer node, or every table entry already equals
  ## the node's current value (a `[v, v]`-constrained node, for instance).
  let i = pickIntegerIndex(rng, base)
  if i < 0: return base
  let node = base[i]
  var cands: seq[ChoiceInt]
  for v in interestingIntValues(node.intC):
    if v != node.intVal: cands.add v
  if cands.len == 0: return base
  let pick = cands[int(rng.next mod uint64(cands.len))]
  result = base
  result[i] = ChoiceNode(kind: ckInteger, intC: node.intC, intVal: pick)

const
  maxHavocStackOps* = 8
    ## Bound on stacked mutation ops per iteration. Keeps the geometric draw
    ## from ever "running away": even at `havocStackContinueP` close to 1,
    ## an iteration's mutation cost is capped at a small constant multiple
    ## of a single-op iteration's.
  havocStackContinueP* = 0.5
    ## Per-step continuation probability for `drawHavocStackCount`'s
    ## geometric draw: `P(count == k) = p^(k-1)*(1-p)` for `k <
    ## maxHavocStackOps`, with the remaining tail mass folding onto
    ## `maxHavocStackOps` itself (the loop simply stops drawing at the
    ## bound rather than truncating a continuous distribution).

proc drawHavocStackCount*(rng: var SplitMix64,
                          maxStackOps: int = maxHavocStackOps,
                          continueP: float = havocStackContinueP): int =
  ## RFC-fuzzer-nextgen S3 deliverable 1: how many mutation operators to
  ## stack this iteration. Starts at 1 (an iteration always applies at
  ## least one op); while below `maxStackOps`, keeps stacking with
  ## probability `continueP` per step. Consumes exactly one `rng.next` per
  ## step attempted (zero when `maxStackOps <= 1`), so the caller's RNG
  ## consumption is itself a geometric-length draw, not a fixed one.
  result = 1
  let threshold = uint64(continueP * float(high(uint64)))
  while result < maxStackOps:
    if rng.next < threshold: inc result
    else: break

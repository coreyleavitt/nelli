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

import ./choice, ./rng, ./datasource, ./int128

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

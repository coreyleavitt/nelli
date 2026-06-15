## Canonical structural encoding for the symex IR.
##
## The output of every `canonicalize` proc here is a deterministic
## string that depends only on the witness-relevant structure of
## its input. Source locations, local-variable name spellings, and
## map-iteration order are all encoded out — the canonical string
## of two structurally-equivalent inputs is byte-identical.
##
## Used by Phase 10's content-addressed DB cache key
## (`symexCacheKey`). See `docs/symex/determinism.md`.
##
## Reserved sigils:
##   `<` `>`  — open/close one constructor's payload
##   `;`      — field separator within a constructor
##   `:`      — kind/payload separator
## No constructor's payload may contain an unescaped sigil; primitives
## are wrapped to enforce that.

import std/[strutils, tables, algorithm, sha1]
import ./types

const
  cacheKeySat*     = ":sat"
    ## Phase 13 cycle 2; renamed Phase 15 Z3e. Suffix appended to a
    ## content-addressed key for SAT witness entries. Sibling suffixes
    ## (`:sat`/`:unsat`/`:unknown` + per-type `:raised:<typeId>` via
    ## `cacheKeyRaised`) coexist under one `"sx:" & H` hash so verdicts
    ## have distinct DB slots.
  cacheKeyUnsat*   = ":unsat"
    ## UNSAT verdict sentinel slot. Value is `@[]` (empty seq).
  cacheKeyUnknown* = ":unknown"
    ## UNKNOWN verdict sentinel slot. Value is `@[]` (empty seq).
    ## Phase 15 Z3e: renamed from `cacheKeyUnkSuffix` / `:unk` to standardize
    ## suffixes on full English words (supersedes the Z0 deferral note).
    ## Entries written under the old `:unk` suffix are orphaned — harmless:
    ## a cache miss recomputes, and there are no external consumers.
  verdictCacheMaxEntries* = 1
    ## Mandatory `maxEntries` for `saveSymexVerdictImpl` calls.
    ## The default `maxEntries = 16` allows accumulation; with the
    ## positional sentinel invariant `result[0] == @[]`, a stray
    ## non-sentinel write under the same key would push the sentinel
    ## to position 1 and silently break load detection. Pinning
    ## to 1 makes the structural invariant impossible to violate.

proc cacheKeyRaised*(typeId: string): string =
  ## Phase 15 Z3e. Per-type cache-key suffix for an `sxRaised` finding, e.g.
  ## `cacheKeyRaised("ValueError") == ":raised:ValueError"`. Each raised
  ## exception type gets its own DB slot so multi-raise SUTs (cluster E) can
  ## accumulate one entry per `(exnType, pathCond)` finding.
  ":raised:" & typeId

const renderAsChoicesVersion* = "2"
  ## Phase 12 cycle 3 introduced the constant; cycle 6 bumped it
  ## "1" → "2" to invalidate stale collection witnesses cached
  ## under the old length-prefix `renderAsChoices` encoding for
  ## seq/Table/HashSet. The current "2" encoding emits per-element
  ## `booleanChoice(true, 0.9)` continue-bools terminated by one
  ## `booleanChoice(false, 0.9)`, matching `lists`/`tables`/`sets`
  ## strategies' replay shape. Non-collection witnesses' choice
  ## sequences are unaffected by the bump but invalidate via the
  ## same key — acceptable cost for one-off cache rotation.
  ##
  ## Distinct from `symexWalkerVersion` (walker semantics — how the
  ## walker reasons about the SUT). `renderAsChoicesVersion` covers
  ## *how a sat witness is serialised into the choice-IR*, not what
  ## the walker computes.
  ##
  ## - "1" — Phase 7 / 11 baseline: length-prefix encoding for
  ##   seq/Table/HashSet (broken round-trip through `lists`/`tables`/
  ##   `sets` strategies).
  ## - "2" — Phase 12 cycle 6: continue-boolean encoding matching
  ##   the strategy draw protocol; sorted iteration for Table/HashSet
  ##   to ensure deterministic encoding of the same logical witness.

const symexWalkerVersion* = "6"
  ## Phase 14 cycle A7b bump. Cluster A's walker-semantics changes
  ## (variant soundness completeness: itMultiVariant, else: arms,
  ## non-enum discs, symbolic-RHS reassign, composite zero-init,
  ## Z3Int disc promotion, var T) are not bytecode-compatible with
  ## "3" entries. Single bump at Cluster A close-out is sufficient
  ## because every intermediate change was parser-erroring under
  ## "3" — there are no stale cached witnesses that would falsely
  ## re-hydrate. C3 (frontier pruning) shares this bump.
  ## Bumped by maintainers whenever the walker's semantics shift in a
  ## witness-affecting way. Participates in `symexCacheKey` so old
  ## persisted witnesses become invisible after a walker semantic
  ## change.
  ##
  ## - "1" — Phases 0-10 baseline (variants lowered to flat tuples,
  ##   default(Object) stub for variant witnesses).
  ## - "2" — Phase 11 cycles 1-12: variants as first-class itVariant,
  ##   walker forks at field access, tFieldDefect target added.
  ## - "3" — Phase 11 deferral #5 closed: plain (non-recCase) fields
  ##   shared across arms (allocated once, not per-arm prefixed),
  ##   surviving `obj.kind = X` reassignment. Witness path layout for
  ##   plain fields moved from `<base>.@<tag>.<field>` to
  ##   `<base>.<field>`.
  ## - "5" — Phase 15 Cluster F (float) close-out (cycle F8). Float
  ##   support landed across F1–F7: itFloat32/itFloat64 + svFloat32/
  ##   svFloat64 type-bridge, IEEE literals/arith/compare, int<->float
  ##   conversions (rmRNE / rmRTZ), std/math FP-native ops + predicates
  ##   (iekMathCall), and eval-side bit-exact witness extraction
  ##   (float64Vals/float32Vals). Float SUTs were parser-erroring or
  ##   producing stub witnesses under "4", so no stale "4" entry can
  ##   falsely re-hydrate; a single bump at Cluster F close-out per
  ##   v2 Invariant 1 rotates the cache for the multi-cluster session.
  ## - "6" — Phase 15 Cluster S (full strings) close-out (cycle S11).
  ##   String support landed across S1–S10a: byte-faithful Z3 String
  ##   model (≤0xFF char-range constraint), len/index/slice/high,
  ##   find/contains/startsWith/endsWith, replace/split/join, regex
  ##   match, concat, bytes, and `$int`/`parseInt` int<->string. S11
  ##   classifies the immutable-string mutations (`s[i] = c`, `s.add`)
  ##   as `seUnsupportedStringOp`. A single bump at Cluster S close-out
  ##   rotates the cache so any "5"-era string verdict re-solves under
  ##   the now-complete string semantics. (S10b — the parseInt
  ##   raises-path — is deferred to post-E1 and will carry its own bump
  ##   when it lands.)

# ---- IRType -----------------------------------------------------------------

proc canonicalize*(t: IRType): string =
  if t.isNil:
    return "Ty<nil>"
  case t.kind
  of itInt:
    "Ty<I:" & $t.width & ":" & (if t.signed: "s" else: "u") & ">"
  of itBool:
    "Ty<B>"
  of itString:
    "Ty<S>"
  of itUninterp:
    "Ty<U:" & t.uninterpName & ">"
  of itFloat32: "Ty<F32>"
  of itFloat64: "Ty<F64>"
  of itTuple:
    # Positional encoding: field order is significant; field-name
    # spelling is encoded only when present (named tuples / object
    # field accessors), since renaming an anonymous-tuple field is
    # by definition a no-op but renaming a named field changes
    # `iekField` lookups.
    var parts: seq[string]
    for i in 0 ..< t.fields.len:
      let nm = if i < t.fieldNames.len: t.fieldNames[i] else: ""
      parts.add nm & "=" & canonicalize(t.fields[i])
    "Ty<T:" & t.objectName & ":" & parts.join(";") & ">"
  of itArray:
    "Ty<A:" & $t.size & ":" & canonicalize(t.elemTy) & ">"
  of itSeq:
    "Ty<Sq:" & canonicalize(t.seqElemTy) & ">"
  of itTable:
    "Ty<Tb:" & canonicalize(t.tabKeyTy) & ";" & canonicalize(t.tabValTy) & ">"
  of itSet:
    "Ty<Se:" & canonicalize(t.setElemTy) & ">"
  of itVariant:
    var plainParts: seq[string]
    for i in 0 ..< t.vPlainFieldNames.len:
      plainParts.add t.vPlainFieldNames[i] & "=" &
                     canonicalize(t.vPlainFieldTypes[i])
    var armParts: seq[string]
    for arm in t.vArms:
      var fParts: seq[string]
      for i in 0 ..< arm.fieldNames.len:
        fParts.add arm.fieldNames[i] & "=" & canonicalize(arm.fieldTypes[i])
      armParts.add $arm.tagOrdinal & ":" & arm.tagName &
                   (if arm.isElse: ":else" else: "") &
                   ":[" & fParts.join(";") & "]"
    # Phase 14 A2: encode `vDiscTags` so two variants with the same
    # of-arms but different else-coverage hash differently.
    var ordParts: seq[string]
    for dt in t.vDiscTags: ordParts.add dt.name & "=" & $dt.ord
    "Ty<Vr:" & t.vObjectName &
      ";plain=[" & plainParts.join(";") & "]" &
      ";disc=" & t.vDiscName & "=" & canonicalize(t.vDiscTy) &
      ";dtags=[" & ordParts.join(",") & "]" &
      ";[" & armParts.join(",") & "]>"
  of itMultiVariant:
    # Phase 14 (ADR-0003 D1). Distinct prefix `MVr:` and distinct
    # axis-grouped format `;axes=[...]` ensure cache keys do not
    # collide with single-axis `itVariant` keys.
    var plainParts: seq[string]
    for i in 0 ..< t.mvPlainFieldNames.len:
      plainParts.add t.mvPlainFieldNames[i] & "=" &
                     canonicalize(t.mvPlainFieldTypes[i])
    var axisParts: seq[string]
    for ax in t.mvAxes:
      var armParts: seq[string]
      for arm in ax.arms:
        var fParts: seq[string]
        for i in 0 ..< arm.fieldNames.len:
          fParts.add arm.fieldNames[i] & "=" &
                     canonicalize(arm.fieldTypes[i])
        armParts.add $arm.tagOrdinal & ":" & arm.tagName &
                     (if arm.isElse: ":else" else: "") &
                     ":[" & fParts.join(";") & "]"
      var ordParts: seq[string]
      for dt in ax.discTags: ordParts.add dt.name & "=" & $dt.ord
      axisParts.add "axis(" & ax.discName & "=" & canonicalize(ax.discTy) &
                    ";dtags=[" & ordParts.join(",") & "]" &
                    ";[" & armParts.join(",") & "])"
    "Ty<MVr:" & t.mvObjectName &
      ";plain=[" & plainParts.join(";") & "]" &
      ";axes=[" & axisParts.join(";") & "]>"

# ---- Local-name rewriting ---------------------------------------------------
#
# Local let/assign names are encoded positionally so renames don't
# invalidate witnesses. `LocalEnv` walks the IR in declaration order
# (depth-first, syntactic) and assigns each `let` the next `$N` slot;
# every later `iekVar` that refers to a local gets rewritten through
# the same map. Free variables (params, top-level callees) are
# encoded by their original name — they're part of the program's
# external surface, not internal.
type LocalEnv = ref object
  slots: Table[string, int]   # original-name → de-Bruijn-style slot id
  next:  int

proc newLocalEnv(): LocalEnv =
  LocalEnv(slots: initTable[string, int](), next: 0)

proc bindLocal(env: LocalEnv, name: string): int =
  result = env.next
  env.slots[name] = result
  inc env.next

proc lookupLocal(env: LocalEnv, name: string): string =
  if name in env.slots:
    "$" & $env.slots[name]
  else:
    name  # free — encode by original name

# ---- IRExpr -----------------------------------------------------------------

proc binopTag(op: IRBinop): string =
  case op
  of bAdd: "+"
  of bSub: "-"
  of bMul: "*"
  of bDiv: "/"
  of bMod: "%"
  of bAnd: "&"
  of bOr:  "|"
  of bXor: "^"
  of bShl: "<<"
  of bShr: ">>"
  of bEq:  "=="
  of bNe:  "!="
  of bLt:  "<"
  of bLe:  "<="
  of bGt:  ">"
  of bGe:  ">="

proc unopTag(op: IRUnop): string =
  case op
  of uNot: "!"
  of uNeg: "~"

proc canonicalize(e: IRExpr, env: LocalEnv): string =
  if e.isNil: return "Ex<nil>"
  case e.kind
  of iekIntLit:    "Ex<IL:" & $e.ival & ">"
  of iekFloatLit:  "Ex<FL:" & $e.fwidth & ":" & $e.fval & ">"
  of iekConvIntToFloat: "Ex<CIF:" & $e.convWidth & ":" & canonicalize(e.convOperand, env) & ">"
  of iekConvFloatToInt: "Ex<CFI:" & $e.convWidth & ":" & canonicalize(e.convOperand, env) & ">"
  of iekMathCall:
    var parts: seq[string]
    for a in e.mathArgs: parts.add canonicalize(a, env)
    "Ex<MC:" & e.mathOp & ":" & parts.join(",") & ">"
  of iekBoolLit:   "Ex<BL:" & $e.bval & ">"
  of iekVar:       "Ex<V:" & lookupLocal(env, e.vname) & ">"
  of iekBinop:
    "Ex<Bn:" & binopTag(e.bop) & ";" &
      canonicalize(e.lhs, env) & ";" & canonicalize(e.rhs, env) & ">"
  of iekUnop:
    "Ex<Un:" & unopTag(e.uop) & ";" & canonicalize(e.operand, env) & ">"
  of iekField:
    "Ex<F:" & $e.fieldIx & ";" & canonicalize(e.obj, env) & ">"
  of iekIndex:
    "Ex<Ix:" & canonicalize(e.arr, env) & ";" &
      canonicalize(e.idx, env) & ">"
  of iekArrayLit:
    var parts: seq[string]
    for x in e.lelems: parts.add canonicalize(x, env)
    "Ex<AL:" & canonicalize(e.lelemTy) & ";[" & parts.join(",") & "]>"
  of iekSeqLen:    "Ex<SL:" & canonicalize(e.lenObj, env) & ">"
  of iekStrLit:    "Ex<S:" & e.sval.escape & ">"
  of iekContains:
    "Ex<C:" & canonicalize(e.container, env) & ";" &
      canonicalize(e.key, env) & ">"
  of iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel:
    "Ex<" & $e.kind & ":" & canonicalize(e.mutRecv, env) & ";" &
      canonicalize(e.mutArg, env) & ">"
  of iekSeqDel:
    "Ex<SqD:" & canonicalize(e.delSeq, env) & ";" &
      canonicalize(e.delIdx, env) & ">"
  of iekSeqInsert:
    "Ex<SqI:" & canonicalize(e.insSeq, env) & ";" &
      canonicalize(e.insVal, env) & ";" &
      canonicalize(e.insIdx, env) & ">"
  of iekSeqPop:    "Ex<SqP:" & canonicalize(e.popSeq, env) & ">"
  of iekTableSet:
    "Ex<TS:" & canonicalize(e.tabRecv, env) & ";" &
      canonicalize(e.tabKey, env) & ";" &
      canonicalize(e.tabVal, env) & ">"
  of StrOpKinds:
    # Phase 15 Cluster S (S1). Canonical tag keys on the IR kind + op name +
    # operands so distinct string ops get distinct content-addressed cache keys.
    var parts: seq[string]
    for a in e.strArgs: parts.add canonicalize(a, env)
    "Ex<St:" & $e.kind & ":" & e.strOp & ":[" & parts.join(",") & "]>"

# ---- IRStmt -----------------------------------------------------------------

proc canonicalize(s: IRStmt, env: LocalEnv): string =
  if s.isNil: return "St<nil>"
  case s.kind
  of isBlock:
    var parts: seq[string]
    for x in s.stmts: parts.add canonicalize(x, env)
    "St<Bk:[" & parts.join(",") & "]>"
  of isIf:
    var parts: seq[string]
    for br in s.branches:
      parts.add "(" & canonicalize(br.cond, env) & "=>" &
        canonicalize(br.body, env) & ")"
    "St<If:[" & parts.join(",") & "];else=" &
      canonicalize(s.elseBody, env) & ">"
  of isLet:
    let slot = bindLocal(env, s.lname)
    "St<Lt:$" & $slot & ":" & canonicalize(s.lty) & "=" &
      canonicalize(s.lvalue, env) & ">"
  of isAssign:
    "St<As:" & lookupLocal(env, s.aname) & "=" &
      canonicalize(s.avalue, env) & ">"
  of isWhile:
    "St<W:" & canonicalize(s.wcond, env) & ";body=" &
      canonicalize(s.wbody, env) & ">"
  of isBreak:    "St<Bk>"
  of isContinue: "St<Co>"
  of isReturn:
    "St<R:" & canonicalize(s.retExpr, env) & ">"
  of isCall:
    var args: seq[string]
    for a in s.cargs: args.add canonicalize(a, env)
    let retSlot =
      if s.retName.len > 0: "$" & $bindLocal(env, s.retName)
      else: ""
    "St<Cl:" & s.callee & ";opaque=" & $s.opaque & ";ret=" & retSlot &
      ";retTy=" & canonicalize(s.retTy) & ";args=[" & args.join(",") & "]>"
  of isIndex:
    let retSlot = "$" & $bindLocal(env, s.ixRetName)
    "St<Ix:" & retSlot & "=" & canonicalize(s.ixArr, env) &
      "[" & canonicalize(s.ixIdx, env) & "];ety=" &
      canonicalize(s.ixElemTy) & ">"
  of isVariantField:
    let retSlot = "$" & $bindLocal(env, s.vfRetName)
    var tags = ""
    for t in s.vfMatchingTags: tags.add $t & ","
    "St<VF:" & retSlot & "=" & canonicalize(s.vfRecv, env) & "." &
      s.vfFieldName & ";fty=" & canonicalize(s.vfFieldTy) &
      ";tags=[" & tags & "]>"
  of isVariantReassign:
    "St<VR:" & lookupLocal(env, s.vrObjName) & ".kind=" &
      $s.vrNewTag & ":" & s.vrTagName & ">"
  of isVariantReassignSymbolic:
    # Phase 14 A4a: distinct prefix `VRS:` so cache keys can't
    # collide with static-tag `VR:` entries.
    "St<VRS:" & lookupLocal(env, s.vrsObjName) & "." &
      (if s.vrsDiscName.len == 0: "kind" else: s.vrsDiscName) &
      "=" & canonicalize(s.vrsRhs, env) & ">"
  of isAssert:
    "St<At:" & canonicalize(s.acond, env) & ">"
  of isTargetLabel:
    "St<Tg:" & s.tname.escape & ">"
  of isUnsupported:
    "St<Un:" & s.reason.escape & ">"

# ---- Top-level overloads ---------------------------------------------------

proc canonicalize*(e: IRExpr): string =
  canonicalize(e, newLocalEnv())

proc canonicalize*(s: IRStmt): string =
  canonicalize(s, newLocalEnv())

# ---- IRParam ---------------------------------------------------------------

proc canonicalize*(p: IRParam): string =
  # Params live at the program's external boundary — their *position*
  # is the witness's identity (witness[0], witness[1], …), and their
  # *type* matters for encoding. The name is part of the program's
  # source-level surface; renaming a param doesn't affect the
  # witness's structural validity, so it's excluded from the canonical
  # form. `isVar` matters because it affects mutation propagation.
  # Range hints (rangeLo/rangeHi from Natural / range[...]) DO matter
  # because they're consumed by the abstraction layer.
  var range = ""
  if p.hasRange:
    range = ";range=[" & $p.rangeLo & "," & $p.rangeHi & "]"
  "Pm<" & canonicalize(p.ty) & ";isVar=" & $p.isVar & range & ">"

# ---- ProcSig ---------------------------------------------------------------

proc canonicalize*(sig: ProcSig): string =
  var params: seq[string]
  let env = newLocalEnv()
  for p in sig.params:
    discard bindLocal(env, p.name)  # so body's iekVar refs to params
                                    # resolve as locals positionally
    params.add canonicalize(p)
  "Pr<" & sig.name & ";retTy=" & canonicalize(sig.retTy) &
    ";isVoid=" & $sig.isVoid &
    ";params=[" & params.join(",") & "]" &
    ";body=" & canonicalize(sig.body, env) & ">"

# ---- SymexProgram ----------------------------------------------------------

proc canonicalize*(prog: SymexProgram): string =
  # Top-level body sees params as bound locals (positionally).
  let env = newLocalEnv()
  var paramParts: seq[string]
  for p in prog.params:
    discard bindLocal(env, p.name)
    paramParts.add canonicalize(p)
  # Callees sorted by name — `Table` iteration order isn't stable.
  var keys: seq[string]
  for k in prog.procs.keys: keys.add k
  sort(keys)
  var procParts: seq[string]
  for k in keys:
    procParts.add canonicalize(prog.procs[k])
  "Pg<params=[" & paramParts.join(",") & "];body=" &
    canonicalize(prog.body, env) &
    ";procs=[" & procParts.join(",") & "]>"

# ---- SymexTarget -----------------------------------------------------------

proc canonicalize*(t: SymexTarget): string =
  case t.kind
  of stkLabel:              "Tg<L:" & t.label.escape & ">"
  of stkAssertionViolation: "Tg<AV>"
  of stkIndexError:         "Tg<IE>"
  of stkFieldDefect:        "Tg<FD>"

# ---- SymexSettings ---------------------------------------------------------

proc canonicalize*(s: SymexSettings): string =
  # Witness-relevant subset ONLY. `acceptUnknownAsCovered` is
  # provably excluded because it influences the verifier's
  # raise/pass decision (`assertCoveredBy`) and not the walker's
  # output.
  "St<is=" & $s.integerSemantics &
    ";rl=" & $s.queryRLimit &
    ";fr=" & $s.maxFrontierSize &
    ";cd=" & $s.maxCallDepth &
    ";lu=" & $s.maxLoopUnwind & ">"

# ---- Cache key -------------------------------------------------------------

proc symexCacheKey*(prog: SymexProgram, target: SymexTarget,
                    settings: SymexSettings,
                    z3Version, nimVersion, walkerVersion,
                    renderingVersion: string): string =
  ## Content-addressed key over every input that determines a
  ## witness's validity. Stable across builds (no source locations,
  ## no map-iteration order, no compiler-specific hashes). Returns
  ## `"sx:" & <40-char SHA-1 hex>`.
  ##
  ## `walkerVersion` covers walker semantics (what the walker
  ## computes from a given IR). `renderingVersion` covers the
  ## serialisation of sat witnesses to the choice-IR. Bumping one
  ## must not silently invalidate witnesses whose semantics under
  ## the other axis are unchanged.
  let canon =
    "K|" & canonicalize(prog) &
    "|" & canonicalize(target) &
    "|" & canonicalize(settings) &
    "|z3=" & z3Version &
    "|nim=" & nimVersion &
    "|w=" & walkerVersion &
    "|r=" & renderingVersion
  "sx:" & $secureHash(canon)

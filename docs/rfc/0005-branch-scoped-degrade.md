+++
type    = "rfc"
id      = "0005"
title   = "RFC — soundness channels: separating over- from under-approximation"
state   = "draft"
wiring   = "unproven"
stage   = "rfc"
profile = "rfc-flow@3"
blocked_by = ["0001"]
size = "l"
value = "high"

[[item]]
id    = "i1"
title = "Round-2 cost: keep full scope (SAT replay half) in one RFC? Conditional on S0b's measured payoff"
state = "resolved"
owner = "corey"
lean  = "keep-one-rfc"
reason = "Corey 2026-09-25: /tdd rfc-0005 til done, do not defer anything -- full scope in one RFC, replay half included"

[[item]]
id    = "i2"
title = "Soften blocked_by 0001 to a builds-on edge (every 0001 dependency is landed)"
state = "open"
owner = "corey"

[[item]]
id    = "i3"
title = "feTransparentResultUsed/feTransparentArgNotInert: demote to sevWarning, or add a companion-anchored DeclineScope"
state = "resolved"
owner = "corey"
reason = "Corey 2026-09-26: neither -- they are not declines; moved to a separate verdict-neutral annotation-violation channel (AnnotationViolation on RawResult/SymexResult), enum members tombstoned; landed in S8 (§13.3)"

[[slice]]
id    = "S0"
title = "Exhibit: over-taint-only UNSAT + veto companion, green characterization pins"
state = "done"

[[slice]]
id    = "S0b"
title = "Measure the over-taint-only payoff before building (throwaway spike)"
state = "done"

[[slice]]
id    = "S1"
title = "Lattice + DegradeClass + classOf (conservative dcNoAnswer default) + carrier + degrade() funnel"
state = "done"

[[slice]]
id    = "S1b"
title = "Mint the missing kinds + runTaint/errors correspondence pin"
state = "done"

[[slice]]
id    = "S1c"
title = "Verdict rule: ordered procedure, candidate pool, isTargetLabel solve"
state = "done"

[[slice]]
id    = "S2"
title = "Replay substrate: ReplayOutcome, target-shaped replayWitness, stackable capture"
state = "done"

[[slice]]
id    = "S3"
title = "Taint-monotonicity harness: withPoisonedArm + battery"
state = "done"

[[slice]]
id    = "S4"
title = "Classify allocDegrade funnel; S0 exhibit flips to sxUnsat"
state = "done"

[[slice]]
id    = "S5"
title = "Classify degradeStrArm + R1 placeholder funnel"
state = "done"

[[slice]]
id    = "S6"
title = "Classify heap/halt sites + beBudgetExhausted/feUnsupportedOp splits"
state = "done"

[[slice]]
id    = "S7"
title = "Cross-path sinks + closure/HOF decline path taint"
state = "done"

[[slice]]
id    = "S8"
title = "DeclineScope carrier + Class-A/B unification + totality pin (vetoes retained)"
state = "done"

[[slice]]
id    = "S8b"
title = "Three silent substitutions: bodiless importc callee, parseInt '+' sign, exn hierarchy (ArithmeticDefect)"
state = "done"

[[slice]]
id    = "S8c"
title = "Name-resolved builtins: resolve callees by symbol, walk user overloads"
state = "done"

[[slice]]
id    = "S8d"
title = "Name-classified type heads: resolve type heads by symbol"
state = "done"

[[slice]]
id    = "S8e"
title = "Scope-keyed names: shadowed locals, generic callee types, symbol-bound witnesses"
state = "done"

[[slice]]
id    = "S8f"
title = "A clean sxSat whose witness reproduces: container cardinality, variant reassignment and construction"
state = "done"

[[slice]]
id    = "S8g"
title = "Faithful scalar/string/defect models: float-to-int conversion, unary-negation overflow, split(s, \"\"), new int zero-init, slice/del defect class, reassignment else-arm"
state = "done"

[[slice]]
id    = "S8i"
title = "S8g's different-mechanism remainder: low(int) div/mod -1, uint64-to-float signedness, int-to-range conversion check, reassignment of a declined construction, concolic if-walker raise drain"
state = "done"

[[slice]]
id    = "S8h"
title = "Ref witnesses that reproduce: nil top-level ref, param aliasing, recursive ref fields, refs inside by-value fields"
state = "done"

[[slice]]
id    = "S8j"
title = "S8i's unlowered exits: top-level return lowering and raise drain, inline ref case-object field through a ref, narrowing int conversion as a RangeDefect fork, single range check on plain assignment"
state = "done"

[[slice]]
id    = "S8k"
title = "Termination and resources: long-string Z3 queries bounded (rlimit-proof decline to sxUnknown), loop-unroll feasibility pruning and memory bound, replay never executes a witness into a SIGSEGV (real nil write)"
state = "done"

[[slice]]
id    = "S8l"
title = "S8j's exit remainder: finally on a return exit (callee and top level), defer, named ref-object case variants, variant-faithful reads through a named ref alias, inline ref to a multi-variant"
state = "done"

[[slice]]
id    = "S8m"
title = "S8l's remainder: finally on break/continue exits, sort-checked Z3 stores (no silent sxUnsat), ref-local reassignment/cast walker fault, uninitialised ref locals, closure bare-return zero value, retire heRefVariantUnsupported"
state = "done"

[[slice]]
id    = "S8n"
title = "Precision remainder: concolic closure-condition resolution, renderAsChoices over ref params, callee reading result before writing it, closure returning a variant"
state = "done"

[[slice]]
id    = "S8o"
title = "S8k's termination remainder: byte tests lowered to the character/code form (s[i]==s[j], byte vs symbolic), constant string index folded before Z3, concolic solves capped (pcSatByConcreteInputs unbounded), Z3 cost dependent on process history (a query SAT in 4 s alone takes 100 s in the walker), incremental-core seq.last_indexof miscomputed over a constant receiver (guard or avoid), b7r_bytescan and b7r2_pathscope terminate on Linux"
state = "done"

[[slice]]
id    = "S8p"
title = "S8n's precision remainder: SUT frame reading result (IR carries the SUT return type), augmented field assignment on a result (result.a += x), string char append (result.add c), closures returning multi-field tuples / string / seq, multi-variant zero value, retBindEq kind mismatch on a multi-variant or distinct callee result (weInternalWalkerFault)"
state = "done"

[[slice]]
id    = "S8q"
title = "S8o's termination remainder: b7r_bytescan B7R-3 hangs past its rlimit in the walk's shared Z3 context (int param in BV form converted to Int inside a string query; keep it out of BV or bound the check), b7r2_pathscope off the sweep skip list once measured on c and cpp under gate load, B7R-6 conjunctive symexAssume forking 2^16 paths, per-context Z3 cost history for capped string queries"
state = "done"

[[slice]]
id    = "S8r"
title = "Windows symex-mingw corpus shard 2 loses its runner since S8k (red at 6772146, 8b9e4b4, 5dc201f; green at a696d80): identify the suite under Z3 4.13.4, fix the resource blowup, make a dying suite attributable in CI"
state = "done"

[[slice]]
id    = "S8s"
title = "S8p's precision remainder: seq[uint8] element vs literal walker fault (bv8 field on svBV64), multi-variant with else arm at ordinal 0 zero value, callee array result havoc, variant-arm field writes and positional tuple-element writes (q[0] += b) declining, tsymex_r6_n43_parity cpp compile failure (deleted std::atomic operator=)"
state = "done"

[[slice]]
id    = "S8t"
title = "S8q's termination remainder: and-chain lowering forks 2^(n-1) paths in if/while/symexAssert/let (nest the guard temporaries), other scan shapes (Q1/B0, pair loop) and isExact mode still use the bv2int bridge, B4 isIntOffset promotion lacks a width stamp (no overflow obligations), stale snd3_6 sweep skip-list entry, CLAUDE.md six-Linux-hangers line"
state = "done"

[[slice]]
id    = "S8u"
title = "S8s's precision remainder: variant constructor naming an else-covered tag (feUnsupportedExprKind), callee building a local Table/HashSet (weInternalWalkerFault svTable/svSet assert), callee new(result) ref result (retBindEq svRef vs svBV64 fault), multi-variant with a bool discriminator (weInternalWalkerFault), zero value for untouched distinct results and HashSet/Table fields, op= on an array element"
state = "done"

[[slice]]
id    = "S8v"
title = "S8r's termination remainder: checkCapped step 2 slow on Z3 4.13.4 when the theory-free query cannot see the cap conflict (58 s / 1.2 GB; add str.len >= 0 and -1 <= str.indexof < str.len facts to the theory-free query), tsymex_r4_strip 2.6x slower on 4.13.4 than at a696d80"
state = "done"

[[slice]]
id    = "S8w"
title = "S8t's remainder: alternating and/or chains ((a or b) and (c or d)) still fork 2^m paths, while guard whose first part hoists a read in a body with continue still declines (R14 Case 2), isIntOffset params rejected by promotion (banned, unsigned, isLoose, isExact unchecked) stay unstamped Ints and B4 offsets do not wrap under unchecked isOptimised, trace the base's false OverflowDefect witness (@[], -1) and probe other shapes for the same fault"
state = "done"

[[slice]]
id    = "S8x"
title = "S8t2's remainder: audit compile-time (macro/VM) code in src/nelli for the `let x = s[i]` / `s[^1]` element-aliasing hazard S8t2 hit in the Nim VM (a let copy aliases the seq slot, so mutating the seq corrupts it); fix every live instance, add a macro-time regression pin for any that was reachable"
state = "done"

[[slice]]
id    = "S8y"
title = "Runtime regression: tsymex_r6_n36_raise_degrade went from under the sweep's 900s kill to ~992s standalone between S8s and S8t2 (identical checks), so gates show 0 -> 137; bisect the landing that slowed it, find the query mechanism, restore the runtime without giving up soundness, pin it by query/rlimit shape rather than wall time"
state = "done"

[[slice]]
id    = "S8z"
title = "S8u's remainder: array reads with a nonzero low bound (array[1..3, int]) ignore the bound (potential false sxUnsat); enum result with no ordinal 0 excludes Nim's actual zero value from the free retSym (potential false sxUnsat); array type alias classifies as uninterp; inline anonymous range discriminator is a typebridge compile error; array write at a symbolic index declines; closure-returning callee is weInternalWalkerFault (allocateSym(itUninterp)); remaining container shapes decline scoped"
state = "done"

[[slice]]
id    = "S8aa"
title = "S8w's remainder: unchecked `low(T) div -1` is modelled as a wrap to low(T) but C traps SIGFPE (witness does not replay -- model the trap or decline); the and/or path join merges only scalar-differing paths, so a chain operand writing a string/seq/heap cell/ref or leaving >1 surviving path still forks 2^m; B6 with a negative offset returns sxUnknown when the unroll budget runs out under the IndexError target; `data.len.uint` in an unsigned B4 scan declines on its own path"
state = "done"

[[slice]]
id    = "S8ab"
title = "S8x's remainder: only `ctx.procScoped` lets have a mechanical guard against the compile-time VM value-let aliasing hazard; build a type-aware guard (typed-AST check over the compile-time modules, or a macro-time assertion helper) that flags any `let`/non-var param binding a non-scalar value location in code reachable from the symex macros, and pin it so the next value-typed save/restore in the front end is caught mechanically rather than by review"
state = "done"

[[slice]]
id    = "S8ac"
title = "S8aa's remainder: a callee assigning through a `var` ref parameter (`cur = b`) is an internal walker fault (sort mismatch at array store value) -- must model or decline scoped, never weInternalWalkerFault; exact-mode `start div y` (width-stamped offset by a bitvector param) runs past 900s -- find the query cost and bound it; a shift by a count outside 0..<width is modelled as Z3's result but x86 masks the count (5 shl 64 == 5), so a witness depending on it may not replay -- model the target's masking or decline; the short-circuit join still declines when an operand allocates or when table/set/variant/distinct state differs"
state = "done"

[[slice]]
id    = "S8ad"
title = "S8ac's remainder: a local distinct value with no distinct-typed parameter (`var m = Meters(0)`) is a walker fault (reboxDistinct: distinct sort not allocated) -- must be modelled, never weInternalWalkerFault; `start < 0 and y > 1 and start div y == start` (UNSAT) exhausts the 20M seqQueryRLimit to sxUnknown (nonlinear div under the seq theory) -- find a linear/bounded encoding or a sound pre-solve refutation so it decides"
state = "done"

[[slice]]
id    = "S8ae"
title = "S8v's remainder: checkCapped step 1c declines queries that are UNSAT only through the sequence theory when their theory-free form is refuted only by the cap (e.g. `str.indexof(s, \":\", 0) > 200 and not str.contains(s, \":\")`) -- decide them without reintroducing the 4.13.4 step-2 string search (bounded step-2 core behind 1c's UNSAT, or a sound theory-level refutation); add range facts for str.at, str.substr, str.to_code (-1..255 byte domain), str.to_int (>= -1) and str.++ (len(a ++ b) = len(a) + len(b)) so cap conflicts through them are seen by step 1c"
state = "done"

[[slice]]
id    = "S8af"
title = "S8ab's remainder: close the VM-alias guard's gaps -- Table/`[]`-via-nnkCall aliasing (distinguish typed Table/seq index from string slicing by the callee's resolved symbol, not syntax), type identity by real type equality (sameType) instead of a depth-3 repr bound, instantiated coverage of generic procs (walk their instantiations), and make the guard fire in every CI leg rather than only under the one test file (register it where every leg runs it)"
state = "done"

[[slice]]
id    = "S8ag"
title = "S8y's remainder: lower str.indexof with a literal 1-char needle to a fresh Int plus split axioms (s = pre ++ x ++ c ++ post, with chain facts pre_j = pre_i ++ x_i ++ c when start_j = ix_i + 1) across all three backends of the idiom -- an equivalence for 1-char needles that turns N36-1's 5-iteration exit solves (q103/q106) from 20M exhaustion into SAT candidates (~1.3M/4.7M in a fresh context); prove the equivalence, pin the verdict and cost per test"
state = "done"

[[slice]]
id    = "S8ah"
title = "S8af's remainder: verify compile-time-VM reachability macro-by-macro for all 17 macros and instantiate-audit every VM-reachable generic among the 37 generic routines in scope (not just traceOneCallBoundary); lift the param check's depth-3 sibling-field bound (walk the full field graph with a visited set); classify generics never instantiated in the scope's compilation unit (force a representative instantiation or prove unreachable); run the guard as a build-time check wired into the symex compile path, not only as a test"
state = "done"

[[slice]]
id    = "S8ai"
title = "S8ae's remainder: make step 1c's relational links semantic, not syntactic (a needle/string equal through a chain of equalities or a computed-but-equal term gets the same contains/prefixof/suffixof/indexof/substr links -- canonicalize by the query's equality classes); add sound facts for replace_all, regex membership, from_int, indexof from a nonzero start (converse direction) and word equations; route seq.last_indexof queries through step 1c instead of straight to the uncapped step 3"
state = "done"

[[slice]]
id    = "S8aj"
title = "S8ad's remainder: an uninitialized local array with an element write (`var a: array[3, int]; a[0] = ...; a[i]`) is weInternalWalkerFault (iekIndex on non-array kind=svBV64) -- model Nim's zero-init of local arrays (and nested aggregates) so it is never a walker fault; extend divRangeFacts-style linear links to bv2int of other bitvector arithmetic (add, sub, mul, shifts) read as Int; reshard the symex-mingw corpus so no shard runs near the 60-minute job limit (a cancelled shard hides failures) and pin per-shard headroom"
state = "done"

[[slice]]
id    = "S8ak"
title = "S8ah's remainder: the VM-alias guard's macro-reachability walk must handle a zero-required-argument macro (Nim auto-invokes it when passed bare as a typed parameter, yielding its result instead of its symbol) -- resolve macros by symbol so a future zero-arg macro cannot be a silent false negative; replace extractTopLevelNames/extractTopLevelMacroNames' column-0 source scan with enumeration from the typed module AST (backtick operators and multi-line signatures included)"
state = "done"

[[slice]]
id    = "S8al"
title = "S8ak's remainder: the forced-generic-instantiation half of the VM-alias guard has only run against one real generic (traceOneCallBoundary) -- exercise it with a fixture generic whose forced instantiation carries a let/param-aliasing hazard, so a regression in the force-and-audit path goes RED; make vmGuardAuditMacroReachWithSpecs (the test hook) resolve macros by symbol like the real vmGuardAuditNames path, so its fixtures no longer need a dummy required parameter to dodge zero-arg auto-invoke"
state = "done"

[[slice]]
id    = "S8am"
title = "S8z's remainder: a seq element compound assignment (s[i] += x and other op=) still declines -- model it; verify s[i] = f() evaluation order against Nim (value before or after the bounds check) and pin whichever Nim does; char witnesses render as uint8 -- render char; low(a)/high(a) on an array are unsupported -- model them; a non-zero-based array (array[1..3, int]) witness renders as array[0..2, int] -- render the declared index range; close the remaining container declines where a sound model exists (non-string Table keys, non-integer values or elements, char/byte/uint8 container witnesses, bool-indexed arrays), keeping any that stay as scoped declines with a stated reason"
state = "done"

[[slice]]
id    = "S8an"
title = "S8ac's remainder: a routine declared inside the SUT is feUnsupportedStmtKind -- model nested proc/func declarations (with and without captures); a `var ptr` parameter passed `addr x` is the heUnsafeCast scoped decline -- model addr-of a local passed as ptr where the pointee is a tracked cell; copy-in/copy-out declines on possible aliasing by argument only, and a callee that reaches the location through a global is outside the fragment -- model module-level var reads/writes from a callee, or prove the decline covers every such path with a test"
state = "done"

[[slice]]
id    = "S8ao"
title = "S8aj's remainder: `add` on a dotted seq field (`o.s.add v`) is N49 feUnsupportedOp while `s.add v` on a local seq and `o.s = @[v]` are modelled -- model add through a field path; an uninterpreted type has no zero (`zeroValueForType` returns nil for itUninterp and the caller declines) -- give itUninterp a zero (a fresh constant of the sort, or a declared default), or prove the decline is the only sound answer and pin it"
state = "done"

[[slice]]
id    = "S8ap"
title = "S8ao's remainder: a ref-object field of a compound sort (seq) has no field-split heap representation (`p.s = @[...]` and `p.s.add v` are seUnsupportedCompoundSortLeaf) -- build compound-sort field-split heap storage; `del`/`insert`/`incl`/`excl`/`[]=` on a dotted field are still N49 feUnsupportedOp -- route them through the same field-write primitives as `add`; `add` on a dotted STRING field is N49 -- route it via iekStrConcat; the uninitialized-`var` decline for itUninterp gives one generic message for all three placeholder prefixes (__ownership, __closure, __unsupported) -- give each the precise kind allocateSym already uses"
state = "done"

[[slice]]
id    = "S8aq"
title = "S8ai's remainder: step 1 itself can run out of budget, so step 1c is never reached when step 1's capped solve is cancelled -- give step 1c a path that does not depend on step 1 completing, or decline with the budget reason; the fact that L is at least every found first index is not emitted (valid but unprovable within the pin's UNSAT budget) -- emit it in a form the solver can use, or show it is subsumed; str.replace_all is unreachable from the walker (Z3_mk_seq_replace_all is behind an optional nim-z3 build flag) -- make it reachable (enable the binding in nim-z3 and push, then bump the lock) or decline it as a scoped decline with the reason; the equality classes are syntactic over the roots, so an equality the query implies without stating it is not seen -- close them under implied equalities, or show the miss only costs completeness and never soundness, and pin it"
state = "done"

[[slice]]
id    = "S9"
title = "Delete both blanket vetoes"
state = "done"

[[slice]]
id    = "S10"
title = "SAT relaxation: replay wired into verdict across both runSymex consumers"
state = "done"

[[slice]]
id    = "S8ar"
title = "S8ap's remainder. Faults first: a seq of the object's own ref type crashes type classification (VM call depth) -- classify recursive ref element types without unbounded recursion; a plain seq[string] faults in add -- model it or decline cleanly, never a walker fault. Then: insert is unmodelled even on a plain seq -- model it; p.inner.s.add (a field path through a ref then a value) is outside the dotted-field shape and stays N49 -- extend the shape; tuple/array/object fields, non-string-keyed Tables and unbacked Table[string,V] still decline as seUnsupportedCompoundSortLeaf -- close those with a sound model, keeping any remaining decline scoped and stated; a distinct field is havocked and has no construction zero -- give it one; a container the witness cannot render demotes the parameter -- render it; the heap-depth budget counts field reads -- count heap steps only, or show field reads must count; Table witnesses render only int and bool values -- render every backed value type; well-formedness facts are asserted only at reads -- assert them wherever a cell enters the model, or show reads cover every path"
state = "pending"

[[slice]]
id = "S8as"
title = "S8an's remainder: explore-mode if-forks without feasibility pruning (symbolic recursion declines); opaque calls do not invalidate globals; global read before write; closure capture/global writes; escaping pointers and addr outside modelled forms; path-based addr alias check; Int/BV conversion cost in int heap cells"
state = "pending"

[[slice]]
id = "S8at"
title = "S8ar's remainder: ref to anonymous tuple; initTable inside the function under test; symbolic index into array of seqs; by-value case-object fields (model + construction zero); distinct over composite base; value object recurring through a container; Table float keys and container values; uint8/char top-level container witness; nim-z3 sortOf(Z3Array) sort-lifetime fix and lock bump"
state = "pending"

[[slice]]
id = "S8au"
title = "S8ag's remainder: local distinct value with no distinct-typed parameter is a walker fault; nonlinear div by bv2int under the seq theory stays unknown; copy-in/out aliasing through a global; non-literal and multi-char needles and rfind/last_indexof do not split; all-pairs chain facts are quadratic per haystack; per-Z3-version encoding cost of c notin t"
state = "done"

[[slice]]
id = "S8av"
title = "S8am's and S11's remainder: raise-irrelevant-parameter witness sentinel; public cache macros discard dbErrors; ExampleDatabase optional closures unchecked in db.nim wrappers (nil SIGSEGV); cache hit returns empty gaps for a served sfUnknown"
state = "pending"

[[slice]]
id = "S8aw"
title = "S8aq's remainder: step 1c has no foothold joining seqRangeFacts to str.indexof (L at least every found index); regex replace_re/replace_reAll gated and undecidable in Z3"
state = "pending"

[[slice]]
id = "S8ba"
title = "S8au's remainder: seq[distinct] locals, compiler-temp misread as global, len(s) <= high(int) for string-derived indices, model global-reachable copy-in/out, deterministic split term order"
state = "done"

[[slice]]
id = "S8bd"
title = "S8ba's remainder: symbolic string index cost, seq[distinct] parameter witnesses, heap-depth budget, pass-by-reference through indexed/call refs and generic callees"
state = "done"

[[slice]]
id = "S8bf"
title = "S8bd's soundness finding: copy-in/copy-out var write-back aliasing through let-bound ref copies"
state = "done"

[[slice]]
id = "S8bh"
title = "S8bf's remainder: var writes dropped through proc-variable calls; ptr parameters assumed disjoint from ref fields; ill-sorted up-conversion of refs"
state = "done"

[[slice]]
id    = "S11"
title = "Public surface: Soundness, gaps(), SymexFinding/render, cache schema, bound echo"
state = "done"
+++

# RFC — soundness channels: separating over- from under-approximation

- **Status:** draft — **repurposed 2026-09-01; round 1 reviewed 2026-09-20;
  round 2 reviewed 2026-09-20.**
  This RFC was opened to carry RFC-0001's BLOCKER B7-2 ("case/else-raise
  sibling poisoning") on the premise that it needed a branch-scoped
  classified-degrade architecture. **That premise was wrong and B7-2 is fixed**
  (`cac15e6`, walker v124) — see §1. What survives is the genuinely valuable
  half, which B7-2 was never an instance of: the engine conflates two
  structurally opposite kinds of imprecision and throws away answers it has
  already earned. **Round 1 inverted the direction of the payoff** (§0.3) and
  raised Size M → L. **Round 2 found four unsound-as-specified mechanisms**
  (§2.3's missing candidate protocol, §2.5's closure-veto argument, §2.2's
  classification premise, and the S7/S8 slice boundary) and restructured the
  slice plan so a verdict flip lands at slice 6 instead of slice 10.
  **Round-1 forks are resolved in §12; round-2 forks are open in §13.**
- Category: symex
- Size: L
- Value: high
- **Depends on:**
  - RFC-0001 (chapulin-hardening) — the SND-1 taint machinery, the three-way
    carrier taxonomy, and the N36/N37/N39/N40 raise-to-in-band migration are
    all prior art this builds directly on. **Every item §1 names is landed;
    §13.2 asks whether the `blocked_by` edge should therefore become soft.**

**Path convention.** Bare `runtime.nim`, `types.nim`, `canonicalize.nim`,
`dsl_parser.nim`, `runtime_heap.nim`, `runtime_strings.nim` mean
`src/nelli/smt/…`; `markers.nim` means `src/nelli/engine/markers.nim`. This
matters for blast radius: **`runtime_heap.nim`, `runtime_strings.nim`,
`runtime_floats.nim`, `runtime_exceptions.nim` and `runtime_closures.nim` are
`include`d into `runtime.nim`** (`runtime.nim:892-898`, `:4902-5021`) — they
are one ~17.6k-line compile unit, not five modules. A slice touching two of
them touches one unit; a slice touching `runtime.nim` at all inherits the whole
unit as context.

## §0 — Thesis

### §0.1 The distinction

There are two ways the walker can be wrong about a program, and it currently
reports both as one undifferentiated `sxUnknown`:

| | mechanism | modelled behaviour set |
|---|---|---|
| **Over-approximation** | fresh unconstrained symbol | ⊇ real — *adds* behaviours |
| **Under-approximation** | path drop, prune, halt | ⊆ real — *removes* behaviours |
| **Incomparable** | forced concrete value, stale env, fabricated continuation | neither — *substitutes* behaviours |

Their soundness consequences are **dual**:

- **SAT is trustworthy if the path carries no over-approximation.** An
  under-approximation cannot invent a model — a witness found on a path that
  was merely *selected* from a smaller set is a real witness.
- **UNSAT is trustworthy if no path anywhere carried an under-approximation.**
  An over-approximation cannot hide a model — if the enlarged program has no
  solution, neither does the real one.

Both are **one-directional**: they license trust, they do not characterise it.
A witness on an over-tainted path may still be real, and §4.2's replay is
precisely the instrument that recovers those cases. The original draft stated
these as "iff"; that was wrong in the forward direction and is corrected here.

**The UNSAT rule quantifies over paths the engine actually solved.** A path
that reaches the target and is *skipped unsolved* is itself an omission — it
removes a behaviour from the searched set — so it contributes `scIncomplete`
regardless of why it was skipped. This is not a footnote: `isTargetLabel`
(`runtime.nim:11159-11168`) skips `trySolve` on every tainted path today, so
relaxing the verdict rule **without** also relaxing that skip mints a false
`sxUnsat`. §2.3 states the rule so this cannot be sliced apart, and §5 keeps
the two in one slice.

Note the asymmetry: **over-taint scopes to a path; under-taint is global.** A
sibling branch's garbage cannot invalidate a witness found and replayed on a
clean path, but an UNSAT claim is a statement about *all* paths, so one
under-approximated path anywhere voids it. §2.4 records the places taint
escapes a path into global solver state, where this asymmetry needs care.

### §0.2 The third class is not a corner case

The original draft's table had two rows. Round 1 established that the
**majority of current degrade arms belong to neither**. A site that
substitutes a *forced concrete value* — `defaultZero` (`runtime.nim:3532`),
the typed-zero dummy behind `mkUnsupported` in expression position
(`canonicalize.nim:2911-2915`), or the stale `env` left by a dropped
unmodelled statement (`runtime.nim:11326-11334`) — produces a behaviour set
that is neither ⊇ nor ⊆ the real one. It is *wrong*, not merely *coarse*.

Classifying such a site "under" mints a false `sxSat` (the S1 failure class,
inverted); classifying it "over" mints a false `sxUnsat` (the S1 failure class
itself — a placeholder whose `.len` silently read 0 produced a false `sxUnsat`
one line from a committed pin). Both are unsound. The only correct treatment
is **both channels at once**, which distrusts the path for SAT and the run for
UNSAT. This is why the carrier is a `set` (§2.1) and not a two-valued tag, and
it is the affirmative answer to the original draft's open question 2.

**Classification therefore keys on substitution semantics, not on the
mechanism's name.** §3 restates the rule and applies it.

### §0.3 Where the recovered capability actually is — *corrected*

The original draft claimed the payoff was on the SAT side and cited RFC-0001's
handoff for the opOack whole-proc search. **Round 1 found that citation
misread.** The handoff entry (`0001-chapulin-hardening.handoff.md`, B7 THIRD
PASS) reads:

> the whole-proc unconstrained **no-defect search** stays sxUnknown because
> the region-membership NON-member fallback still k-unrolls (maxLoopUnwind=5)

A no-defect search carries **no witness** and wants `sxUnsat`. K-unrolling is
under-approximating, and this RFC's own rule voids UNSAT under under-taint —
so that case stays `sxUnknown` after this change, correctly. It is not
discarded capability; it is an honest report of an unproven bound.

The draft's SAT-side framing also contradicted its own §1.3, which concedes
that a found witness already beats the global flag. Both are now corrected.
The real ledger:

**The SAT side is nearly closed already.** Paths that exit a loop within
budget are untainted (`runtime.nim:9509` forks the exit path with `not cond`
conjoined and *no* taint) and already reach `trySolve` and report `sxSat`. The
only paths the relaxed SAT rule newly admits are the **exhausted survivors**
(`runtime.nim:9555`: `survivors.add forkPathTainted(p, p.pc, p.env)` — `pc`
still carries `cond = true` from iteration k, `env` frozen there, and no exit
constraint is ever conjoined). Post-loop code then executes on a trajectory
the real program never takes, because the real program is still looping. That
is a **fabricated continuation** — the §0.2 incomparable class — so it is
distrusted for SAT by construction, and the k-unroll payoff is *empty* unless
a witness found there is replay-confirmed against the real function (§4.2).

**So state it plainly: the SAT half's entire live payoff is two mechanisms** —
the blanket-veto deletion of §2.5 and the raise-routing recovery of §2.6 — and
both are now pinned in §6. Round 2 added this sentence because §6 previously
pinned only the replay-gated cases, i.e. the half this section calls empty; a
reader could discharge every SAT DoD item without the SAT half ever changing
an observable verdict.

**The UNSAT side is where the capability is, and it is measurable.** Today
*any* degrade sets `w.sawUnknown` (52 write sites in `src/`), and `sxUnsat` is
reported only when it never fired (`runtime.nim:13576-13595`). So a run whose
only imprecision is over-approximating — a fresh unconstrained placeholder, an
`mkUnsupported` on an untaken arm — proves the target unreachable and is told
to report `sxUnknown` anyway. Under the channel rule that is a sound
`sxUnsat`. The population is **272 `== sxUnknown` assertions across 110 test
files** at HEAD; the subset whose runs are over-taint-only is the measured
payoff. **Round 2 moved the count to the front of the plan** (slice S0b, §5):
the original plan counted it at slice 8, which is eight slices spent before
learning whether the payoff is non-empty. §0.2's own finding — that the
*majority* of degrade arms are `⊤`, which never flips — makes a near-zero
count a live possibility, and §13.1 makes that outcome a scheduled fork rather
than a late surprise.

This reframing does not shrink the RFC's value — it relocates it, and
relocates it onto the half RFC-0011 is blocked on (§8.2).

### §0.4 Why the distinction unifies past work

It unifies findings RFC-0001 fixed one at a time. **S1** — the placeholder seq
whose `.len` silently read 0, producing a false `sxUnsat` — was an
*incomparable* site treated as sound. **Bug #2**'s field poisoning was an
over-approximation applied globally instead of per-read. **N20**'s k-unroll is
under-approximating, which is precisely why its own note that "verdict stays
correct either way" holds. Three separate slices, one missing distinction.
These are history, not pending flips; they motivate the taxonomy, they do not
quantify the payoff. §0.3 quantifies the payoff.

## §1 — What is already true (do not re-derive)

Read the source before designing against it. Five things that are **not** what
RFC-0001's escalation implies:

1. **B7-2 was a parser gap, not an architecture gap. FIXED `cac15e6`.**
   `case` as a statement was always modelled; `case` as an *expression* had no
   `parseExpr` arm and declined `feUnsupportedExprKind`. The "sibling
   poisoning" was downstream: the declining proc is a callee, parsed whole-proc
   at registration **before any path exists**, so the decline had no path to
   scope to. Fixed by the A-normalisation M5 already applied to `nnkIfExpr` at
   walker v50. No architecture was required.

2. **The raise-to-in-band migration already happened for `allocDegrade`'s
   arms** — N36/N37/N39/N40, walker v101–v104, in the 0.5.1 fix loop.
   `allocDegrade`'s own comment records that those arms "previously `raise`d."
   RFC-0005's original framing described this as the large unstarted refactor.
   It is substantially done — but **not complete**: `runtime.nim:64-213`
   documents a residual class still "Caught at the `runSymex` boundary →
   sxUnknown". Those whole-walk aborts discard already-found winners and can
   carry no path-scoped channel at all. §3.3 rules on them.

3. **A witness beats `sawUnknown` — but not the two blanket vetoes.** The
   verdict is `if w.found.len > 0 and not capForcedUnknown and not
   closureForcedUnknown:` (`runtime.nim:13536`). `capForcedUnknown`
   (`13497-13510`) fires on **any** `sevError` in `prog.parseErrors`,
   deliberately including constructs guarded behind an unreachable branch that
   no walked path ever touched (`13492-13495`); `closureForcedUnknown`
   (`13519-13523`) fires on any `sevError` closure-call error. So the SAT half
   is path-scoped for exactly one of three unknown-forcing channels. The
   original draft's claim 3 named only the first. §2.5 decides the other two.
   **Round 2 correction:** the closure veto is not redundant machinery — it is
   today the *only* soundness barrier for a set of value-substituting closure
   sites that set `sawUnknown` and record a `closureCallErrors` entry but
   **never taint any path** (§2.5, verified list). Deleting it before those
   sites carry path taint is unsound.

4. **Per-path taint exists and is well built — with two escape hatches.**
   `Path.uncertain` (`runtime.nim:479`), `forkPathTainted` (24 live call
   sites — regenerate the inventory in the slice; round 1's "25" is off by
   one), and an internal template deliberately shaped so that "drop the taint"
   is unspellable. But `runtime_heap.nim:337` and `runtime_heap.nim:990` mutate
   `p.uncertain = true` / `child.uncertain = true` **directly**, bypassing that
   discipline; §2.2 closes both — with a *mutation-shaped* primitive, because
   neither site is fork-shaped. The Invariant-7 mechanism is a drain-time
   **backstop that stamps** `weInternalWalkerFault` on an empty-errors
   `sxUnknown` (`runtime.nim:13577-13589`) — it detects the class after the
   fact, it does not prevent it. The original draft called it an assertion.

5. **Exceptions may not be caught below the top frame on this toolchain.**
   RFC-0001's B7r2 prototype established that wrapping even ONE non-top-level
   `seq[Path]`-returning recursive call in `try`/`except` causes the
   classified-degrade exception to **never be raised at all** (Nim
   2.2.10-patched, C backend, ORC, `--exceptions:goto`, `--threads:on`;
   bisection-isolated, fully reverted). This constraint lived only in the 0001
   handoff. It is binding here: channels ride fields and in-band returns, as
   `uncertain` does now. No design in this RFC may introduce a non-top-level
   catch.

So the remaining work is **narrower in mechanism and wider in surface** than
the original seed claimed: classify each existing degrade by substitution
semantics, carry two channels on the taint, and make the verdict rule consume
them.

## §2 — Design

### §2.1 The lattice

```nim
SoundnessChannel* = enum
  scSpurious    ## over-approximating: modelled ⊇ real. A witness on such a
                ## path may be spurious. Blocks sxSat for THIS path.
  scIncomplete  ## under-approximating: modelled ⊆ real. A proof over such a
                ## run may have missed behaviours. Blocks sxUnsat RUN-WIDE.

Taint* = set[SoundnessChannel]
```

`Taint` is the powerset lattice on two elements: `⊥ = {}` (clean, the identity
of join), `⊤ = {scSpurious, scIncomplete}` (incomparable — §0.2), join is set
union. The existing return-merge `p.uncertain or cp.uncertain`
(`runtime.nim:11083`) becomes `p.taint + cp.taint`; union replaces OR with no
special case.

**The join does not swap channels under negation.** *(Round 2 replaced the
original argument, which was not a proof.)* The original text argued from
images — "if S ⊇ R then f(S) ⊇ f(R), including f = boolean negation". Branching
does not apply a function to a behaviour set; it **conjoins different
predicates** on the two sides (the model constrains a havoc symbol `h`, reality
constrains the modelled-away expression `e(x)`), and intersection preserves ⊇
only against the *same* constraint. The property that actually holds is
**per-trace simulation**:

> Let a `{scSpurious}` site introduce symbol `h` **unconstrained at the point
> of introduction**. Then for every real trace `t` there is a model trace `t′`
> agreeing with `t` on every non-degraded variable and taking the same arm at
> every branch — because `h` is free, so whichever arm `t` takes is satisfiable
> in the model. Hence each arm's modelled behaviour set contains the
> corresponding real arm's set, for **both** polarities, and equally for
> `isAssume`'s filter as for `isIf`'s fork.

The hidden premise is load-bearing and is therefore an **invariant, not an
aside**: *a `{scSpurious}` site's symbol carries no constraints at
introduction.* Sites that violate it — `defaultZero`, the typed-zero dummy,
any forced value — are exactly §0.2's incomparable class, which makes §0.2 a
corollary of this invariant rather than an independent assertion. §6 pins it.

The over/under duality appears **only at consumption** (§2.3): SAT reads the
winning path's `scSpurious` coordinate, UNSAT reads the run-global
`scIncomplete` coordinate. This holds *because* the taint is path-level. A
value-level channel would need negation-swap join rules; §9.3 dismisses that
design for exactly this reason.

**Only two of the four coordinates are consumed by the verdict** —
`path.scSpurious` and `run.scIncomplete`. `run.scSpurious` is diagnostics-only
(it drives §8.1's actionability) and `path.scIncomplete` is inert. That is
deliberate: uniformity is worth two idle bits, and stating it here is the
answer to "why does a pure-omission site put `{}` on the path?", which every
future classifier-author would otherwise re-derive.

**Naming.** Members are named for the failure mode, not the direction, so the
verdict rule reads self-evidently: `if scSpurious notin winnerTaint: sxSat`,
`if scIncomplete notin runTaint: sxUnsat`. "Over-/under-approximation" stays
in doc comments as the literature cross-reference. May/must is rejected — it
renames the confusion rather than removing it.

### §2.2 Where the channel lives — path-level, derived from a named class

**Carrier.** `Path.uncertain: bool` → `Path.taint: Taint`
(`runtime.nim:479`); `w.sawUnknown: bool` → `w.runTaint: Taint`, with
`sawUnknown ≡ runTaint != {}`. The existing value-level placeholder pattern
(`isUnsupportedFieldPlaceholder` / `seqUnsupportedFieldReason` /
`seqUnsupportedFieldKind`, `runtime.nim:340-364`) is **retained unchanged** as
the deferred-taint mechanism: it stays inert until a read converts it to path
taint via `placeholderReadDeclineKind` (`runtime.nim:3671`), which now supplies
the channel for free. That pattern already delivers the per-read precision
Bug #2 needed without threading a join through every combinator.

#### The classification is a named class, not a pair of set literals

Round 1 specified `func channels(k): tuple[path, run: Taint]` with four arms
returning set-literal pairs. **Round 2 rejects that encoding**, on evidence
from the RFC itself: the k-unroll exhausted survivor — which round 1 called
"the motivating case" for returning a pair — needs
`({scSpurious, scIncomplete}, {scIncomplete})`, and **no arm of round 1's own
sketch produced it**; §3.1 patched it with a parenthetical footnote on one
table row. A four-coordinate product of 2-element sets has 16 states, five of
which are meaningful, and the author of the sketch silently got the flagship
row wrong. Name the five classes and derive the coordinates:

```nim
type DegradeClass* = enum
  dcFreshSymbol   ## substitutes a fresh unconstrained symbol: modelled ⊇ real
  dcSubstituted   ## forced value / stale env: modelled neither ⊇ nor ⊆ real
  dcFabricated    ## the survivor path is fiction, but the omission is real:
                  ## ⊤ on the path, {scIncomplete} on the run (k-unroll survivor)
  dcOmitted       ## path drop / halt / prune: modelled ⊆ real
  dcNoAnswer      ## Z3 unknown / walker fault: no modelled program exists

func classOf*(k: SymexErrorKind): DegradeClass
  ## THE exhaustive case — one word per kind. The compiler rejects a new
  ## unclassified kind. This is §3.4's deliverable, in code.

func pathTaint*(c: DegradeClass): Taint =
  case c
  of dcFreshSymbol:                            {scSpurious}
  of dcSubstituted, dcFabricated, dcNoAnswer:  {scSpurious, scIncomplete}
  of dcOmitted:                                {}

func runTaint*(c: DegradeClass): Taint =
  case c
  of dcFreshSymbol:                            {scSpurious}
  of dcSubstituted, dcNoAnswer:                {scSpurious, scIncomplete}
  of dcFabricated, dcOmitted:                  {scIncomplete}

func channels*(k: SymexErrorKind): tuple[path, run: Taint] =   ## convenience
  (pathTaint(classOf(k)), runTaint(classOf(k)))
```

The taint algebra is now written once in ten lines. A `classOf` row is a
reviewable **judgment** — "`beBudgetExhaustedKUnroll` is `dcFabricated`" —
checkable against §3.1's rule by reading one word, instead of a coordinate pair
whose correctness requires re-deriving the semantics per row. The eleven
meaningless states become unconstructible, the fifth class gets a name instead
of a footnote, and `DegradeClass` turns out to be exactly the user-facing lever
taxonomy §8.1 needs.

#### The premise "every taint site has a kind in hand" is false — enumerate the exceptions

Round 1 asserted that "every taint-introducing site already has a classified
`SymexErrorKind` in hand at the moment it taints" and that the 24 call sites
make the migration mechanical. **Verified false at these sites**, each of which
is a slice obligation, not a detail:

| site | what is missing |
|---|---|
| `isUnsupported` walk arm (`runtime.nim:11322-11338`) | `forkPathTainted` with **no `SymexErrorInfo` in the arm at all**. The IR node carries only free text (`mkUnsupported(reason)` → `IRStmt(kind: isUnsupported, reason)`, `types.nim:3398`). Requires `mkUnsupported(kind, reason)` across ~40 emitting sites in `dsl_parser.nim` + `canonicalize.nim`. **This is §0.2's flagship incomparable example.** |
| recursion cycle-break (`runtime.nim:10855-10864`) | fresh `_cyc` retSym + `forkPathTainted`; **no kind exists for this degrade** — mint one |
| over-cap missing-callee (`runtime.nim:10700-10722`) | `forkPathTainted`; kind lives only in `prog.parseErrors`, not at the site |
| `trySolve` returning `zsUnknown` (`runtime.nim:7524-7525`), consumed at `:11167` and `:11491` | bare `w.sawUnknown = true`; **no error minted**. The `ekZ3*` kinds §3.1 cites are minted only from *raised* Z3 exceptions (`:12860-12863`), never from an unknown *result*. Consequence today: a run whose only degrade is a solver resource-out reaches the Invariant-7 backstop with empty errors and is stamped `weInternalWalkerFault` — "walker classification gap" — for routine solver exhaustion |
| handler-stack re-raise (`:11226`), diverged closure body (`:11866`), break/continue outside loop (`:9564`, `:9574`), `isTargetLabel`'s two writes (`:11162`, `:11167`) | bare `sawUnknown`, no kind |

Minting the missing kinds is slice S1b and is a **precondition** for the
derivation rule below.

#### The run coordinate is derived, not written

Round 1 would have migrated ~52 `sawUnknown = true` writes into ~52
hand-written `w.runTaint = w.runTaint + …` joins, each free to disagree with
the kind recorded one line above it — and `forkPathTainted` cannot absorb the
run join, because the template (`runtime.nim:669`) has no `w` in scope. That is
a second source of truth, which §10 row 5 already forbids for `forcedBy`.

**Decision: `w.runTaint` is derived at drain time** as the union of
`runTaint(classOf(e.kind))` over every drained `sevError` in the existing error
seqs (`walkDegradeErrors`, `parseErrors`, `closureErrs`,
`loweringDegradeErrors`, heap sinks). The empty-error `sxUnknown` case is the
existing Invariant-7 backstop → `⊤`, which is §2.5's bucket 3 verbatim. Two
consequences to hold:

- It requires **error-pairing totality** — every degrade records an error.
  That is exactly what S1b's kind-minting delivers, and
  `tests/tsymex_r6_degrade_pairing_audit.nim` already pins part of it.
- It requires a **severity rule**. `sevWarning` kinds must not taint by
  default — but §3.1 now has a row for the one that should
  (`eeUnknownExnType`, which substitutes behaviour; see §3.1).

**Path taint stays written**, because `errors` carries no path association —
nothing can re-derive *which* entries were on the winning path. §10 row 5 is
corrected accordingly: the derivation principle is true of the run coordinate
only.

#### One funnel performs all three acts

A degrade site today performs three acts (`runtime.nim:9516-9556` is the
canonical shape): set `sawUnknown`, add a `SymexErrorInfo`, fork a tainted
survivor. Round 1 disciplined only the third. Discipline all three from one
kind mention:

```nim
proc degrade(w: var WalkCtx; kind: SymexErrorKind; msg: string): Degrade =
  ## The ONLY way to obtain a `Degrade` token. Records the SymexErrorInfo, so
  ## the drain-time derivation of `w.runTaint` sees it. Recording and
  ## classification cannot disagree: there is one kind mention.
  w.walkDegradeErrors.add SymexErrorInfo(kind: kind, severity: sevError, msg: msg)
  Degrade(path: pathTaint(classOf(kind)))

template forkPathTainted(parent: Path; pcExpr: seq[Z3Bool]; envExpr: Env;
                         d: Degrade): Path =
  forkPathWithTaint(parent, pcExpr, envExpr, parent.taint + d.path)

proc taintInPlace(p: Path; d: Degrade) =   ## the runtime_heap.nim:990 shape
  p.taint = p.taint + d.path
```

The token handles the one-error-many-survivors shape for free (`let d =
w.degrade(…)` once, then `forkPathTainted(p, p.pc, p.env, d)` per survivor —
exactly the `:9555` loop). Halt sites (`heapDepthExhausted`, `isUnsafeCast`)
call `discard w.degrade(…)` and return: **no path act at all**, matching the
rule that a halted path needs no carrier. `runtime_heap.nim:337` is a halt and
therefore loses its mutation entirely; `:990` uses `taintInPlace`. Round 1's
"route both through the same helper" was shape-wrong for both.

**Scope the totality claim honestly.** Compile-time totality is real at
`classOf`'s exhaustive `case` and at `forkPathTainted`'s required `Degrade`.
It is *not* achievable for direct field writes: `runtime_heap.nim` and
`runtime_strings.nim` are `include`d into `runtime.nim`, so there is no module
boundary to hide `Path.taint` behind. Close that class the way this codebase
already closes such classes — a structural pin (the `.drift` / marker-scope
idiom): a test that `command grep`s `src/` for writers of `.taint` / `.runTaint`
outside the sanctioned primitives and asserts the list is exactly the expected
set. The remaining spellable mistake — reusing an **existing** kind at a site
whose substitution class diverges — no mechanism can check; §3.2 makes it a
stated rule.

Minimum ceremony for next year's engine author: append the enum member, add
one `classOf` arm (the compiler forces it), call `w.degrade(kind, msg)`.

`loweringDidDegrade: bool` (`runtime.nim:1400-1403`) becomes
`loweringPendingTaint: Taint`, subsumed at the drain (`runtime.nim:8812-8816`).
That drain's documented attribution slop (`runtime.nim:1352-1355`) is
conservative-safe under union *for misattribution* — but `runtime_heap.nim:838-862`
records empirically that the pending flag can be **lost entirely**, and a lost
`{scSpurious}` leaves a havoc value on a clean path → an unreplayed `sxSat`.
S1 therefore pins `loweringPendingTaint == {}` at walk end, extending the
Invariant-7 backstop to pending-taint leaks.

This answers the original draft's open question 3 — the channel **rides the
existing sinks**; no fourth taxonomy column on `SymexErrorInfo` for the
*channel*. (§2.5's decline **scope** is different data and does need a carrier;
see there.) And it answers open question 1's heap-depth case: a halted path
needs no surviving carrier, because its contribution is run-global by
construction.

### §2.3 The verdict rule — an ordered decision procedure

Round 1 stated the rule as four bullets. Round 2 found four states they leave
unresolved, two of which mint the failure classes this RFC exists to prevent,
and one of which turns the relaxation into a **regression** against today's
engine. The rule is therefore restated as an ordered procedure with disjoint
guards, against the real code (`runtime.nim:13524-13595`, `shouldStop` at
`:8212-8221`, `isTargetLabel` at `:11156-11168`).

**Candidate lifecycle.** `isTargetLabel` must solve `scSpurious`-tainted paths
(today it skips `trySolve` outright, `:11162-11167`) and a SAT result becomes a
**candidate**. Candidates are held in `w.candidates: seq[RawResult]`, a
separate pool — *not* in `w.found`. This is structural, not a filter predicate,
for one reason: `shouldStop` (`:8212-8221`) halts the entire walk on the first
`sxSat` in `w.found`. If a candidate entered `w.found` it would halt
exploration before a clean witness on a sibling path was ever solved; if replay
then refuted it, the verdict would be `sxUnknown` **where today's engine
reports `sxSat`**. The relaxation must not be able to lose a verdict the engine
already earns.

**Ordered procedure** (first matching rule wins):

1. a clean `sxSat` in `w.found` (`scSpurious notin path.taint`) → **`sxSat`**
2. a clean `sxRaised` winner → **`sxRaised`** (a reachable raise is an
   existence claim, so it obeys the SAT rules verbatim; the *absence* of a
   raise is a universal claim and falls under rule 5)
3. a candidate whose replay returns `roConfirmed` (§4.2) → **`sxSat`** /
   **`sxRaised`**, carrying `replay = rsConfirmed`
4. **any solved SAT on any path — candidate included, replay outcome
   irrelevant — terminally blocks `sxUnsat`.** A candidate that fails replay
   falls to `sxUnknown`, never to `sxUnsat`: the enlarged program *does* reach
   the target, and only reality is unknown. Round 1's bullets permitted reading
   "no witness" as "no *confirmed* witness", which mints a false `sxUnsat`.
5. no solved SAT anywhere and `scIncomplete notin runTaint` → **`sxUnsat`**
   (§0.3's recovered capability)
6. otherwise → **`sxUnknown`**, carrying `runTaint`

Rules 1–2 before 3 fixes the scan-order hazard: today the winner scan takes the
first `sxSat` in **discovery order** (`:13537`), so without an explicit order a
tainted-but-confirmed candidate could shadow a clean witness found later, and
the public result would carry `pathTaint != {}` when a taint-free answer
existed. A refuted candidate must likewise never shadow a live clean
`sxRaised`, and must not leak into the non-winning-raise diagnostics protocol
(`:13555-13566`).

**The unsolved-skip is itself an omission.** Any path that reaches the target
and is not solved contributes `{scIncomplete}` to `runTaint` — this is §0.1's
corollary and it is what makes rule 5 sound. It also means rule 5 and the
`isTargetLabel` solve **cannot be sliced apart**: shipping rule 5 while
`isTargetLabel` still skips tainted paths mints exactly the false `sxUnsat`
this RFC exists to prevent. §5 keeps them in one slice.

`w.found` and `w.candidates` entries gain `pathTaint: Taint` recorded at
target-hit time (`RawResult`, `runtime.nim:538-570`), because the winning path's
taint is not otherwise available at verdict time. Because replay must run in
macro-generated code (§4.2), `RawResult` must also carry candidacy across the
`runSymex` boundary in a form that **cannot be mistaken for a plain `sxSat`** —
see §4.2's plumbing note.

### §2.4 Cross-path sinks

"Over-taint scopes to a path" is true of forks, and *not* true of the places
taint escapes a path into global solver state. Each needs a per-channel
admission rule, because an under-tainted sub-path baked into a global axiom
can hide models run-wide, and an over-tainted one can fabricate them run-wide:

| sink | site | rule |
|---|---|---|
| closure ground axioms | `runtime.nim:8302-8316`, `:11762-11785` | mint only from `taint == {}` sub-paths (today: skips `uncertain`) |
| callee summary cache | `runtime.nim:11041-11053` | admit only `taint == {}` (today: gated on `not uncertain`) |
| fresh-`Path` constructions | `runtime.nim:11729-11730` (`descentBase`, the actual hardcoded `uncertain: false`), `:13346` and `:14214` (roots), `:690`/`:704` (H1 test hooks) | audit each against the new type |
| `parseIntGateConstraintsLive()` | drained into every check, `runtime.nim:7481-7496` | per-channel disposition; minted per-occurrence during string lowering |
| `currentClosureCallAxioms` | same drain | per-channel disposition |
| `stripDecompConds` | same drain; minted on a live path at `runtime_strings.nim:760` | per-channel disposition |
| `defectSurvivorPc` | same drain | per-channel disposition |

**Round 2 corrected row 3's citation** — `runtime_heap.nim:843-858` contains no
`Path(` construction and no `uncertain: false`; it is the deref-drain comment.
**Round 2 added the last four rows**: `trySolve` asserts these pools into every
subsequent check, each carries only a local definitional-soundness comment, and
the idiom is named and copied (`runtime.nim:3017`) so the list grows silently.
The audited set must be pinned against the actual drain list, or this table is
stale the moment someone adds a pool.

Slice S1 pins "**any** channel ⇒ no summary cache" — sound, less reuse. A
channel-aware `CallCacheEntry` is a later optimisation, out of scope here.
**Producer:** these admission rules are S7 (§5), not "somewhere in S1" — round
1 left them assigned to no slice at all.

### §2.5 The two blanket vetoes — delete both; make reachability representable

`capForcedUnknown` and `closureForcedUnknown` (§1.3) veto the winner scan
before it runs, on any `sevError` anywhere. The code's own rationale for the
blanket is explicit (`runtime.nim:13492-13495`):

> The walker's missing-callee arm already sets `w.sawUnknown` when the capped
> call is reached, but we force it here so a cap discovered on a NON-walked
> path (the over-cap callee is parsed but, e.g., guarded behind an unreachable
> branch) still cannot yield an unsound sat/unsat.

**A construct on a never-walked path contributed nothing to any verdict.**
Forcing `sxUnknown` for it does not protect soundness in the unreachable case;
it insures against the possibility that the reach-taint mechanism has a gap.
The blanket is a backstop for a *coverage* defect, wearing the costume of a
soundness rule — and it is the same shape as the Invariant-7 backstop, which
this codebase already knows how to express honestly.

So the right design is neither "trust the reach mechanism and fold the blanket
in" nor "keep the blanket". Both argue about how much to trust a backstop. The
defect is that **the representation cannot answer the only question that
matters: was this decline site reached?** Make it answerable:

1. **Every site-anchored decline mints a marker node.** Today the two classes
   are split by accident of history: Class-A sites record a `sevError` in
   `prog.parseErrors` (→ caught by the blanket), Class-B bare `mkUnsupported`
   sites mint a dummy node and rely on the walker's `isUnsupported` arm to
   taint the reaching path (`runtime.nim:13502-13505`). That is two mechanisms
   for one thing. Unify: a site-anchored decline mints the marker **and**
   records the error. Reach-taint then decides the verdict — exactly the
   per-path scoping this RFC exists to provide — and the `parseErrors` entry
   becomes purely diagnostic. (Note the dependency: §2.2 requires
   `mkUnsupported` to carry a kind, and a marker that carries no kind cannot
   feed `classOf`. S1b lands the kind; this slice consumes it.)
2. **Signature-scoped declines stay run-wide, via the class table, not a
   veto.** `feUnsupportedParamType`/`feUnsupportedWitnessType` and their kin
   have no site to attach to because the unmodellable thing *is* the
   signature. They classify `dcNoAnswer`, which forces `sxUnknown` in both
   directions by construction. No separate switch.
3. **Unregistered-callee declines are anchored by the callee key.** *(Round 2
   added this third class; without it the invariant below is not total.)*
   `geInstantiationCapped` (`dsl_parser.nim:9290`), unresolvable-`getImpl`
   `feUnsupportedOp` (`:9219`), `geDistinctBarrier` (`:9247`) and
   `geConceptViolation` (`:9390`) are `sevError` with **no marker node and no
   signature scope**: the callee is never registered, so reach detection is the
   walker's missing-callee arm firing on the `mkCall` key. This is precisely
   the "cap behind an unreachable branch" case the blanket's own comment
   describes. Under a two-class invariant they would all land in bucket 4 and
   be stamped `⊤` on **every** run — louder than the blanket and no better
   scoped. The `sevError` must therefore carry the callee key so the verdict
   can associate reach-taint.
4. **What still cannot be placed is a walker-completeness defect, and says
   so.** A `sevError` carrying none of the three anchors means the engine
   cannot tell whether it was reached. That is a defect in the mechanism, not a
   property of the SUT. It stamps `⊤` and a `weInternalWalkerFault`-class
   diagnostic, exactly as the Invariant-7 backstop does today
   (`runtime.nim:13577-13589`) — conservative in the verdict, loud in the
   diagnostics, and *visible* rather than silently absorbed into every run's
   answer.

**Where the scope lives.** Round 1 specified the invariant without specifying
its representation, so the totality pin §6 demands was unwritable —
`SymexErrorInfo` is `(kind, severity, msg)` (`types.nim:1786-1792`) and carries
nothing that can name a marker or a callee. **Decision: add a `scope` field to
`SymexErrorInfo`**:

```nim
DeclineScope* = object
  case kind*: DeclineScopeKind
  of dskSiteAnchored:   markerId*: int
  of dskSignature:      discard        ## the signature itself is unmodellable
  of dskCalleeKey:      calleeKey*: string
  of dskUnplaced:       discard        ## bucket 4 — a walker-completeness defect
```

Round 1's "no fourth column on `SymexErrorInfo`" ruling was about the
**channel**, which stays derived from `kind`. A *scope* is genuinely new
information that no existing field carries, and putting it on the record makes
the invariant a total function of the record — checkable by construction rather
than by a join against a side table. The alternative (a side
`prog.declineSites: Table[errorIndex, markerId]`) is index-coupled and is
rejected in §9.8.

The invariant that keeps this honest is structural and pinnable: **every
`sevError` carries a `DeclineScope` other than `dskUnplaced`.** That is a
totality pin of the same kind as `classOf`'s exhaustive `case` — bucket 4 is a
measurable, shrinking defect class instead of an invisible policy knob. Two
kinds were expected to need reclassification rather than anchoring:
`feTransparentResultUsed` (`dsl_parser.nim:4324`) and `feTransparentArgNotInert`
(`:8486`) are diagnostic *companions* to a walk-time mechanism that already
taints via `feOpaqueCallUnmodelled`. **Resolved (§13.3, Corey 2026-09-26):
neither `sevWarning` nor a companion scope — they are not declines at all.**
They left `SymexErrorKind`'s live set (tombstoned, never emitted) for a
separate, verdict-neutral annotation-violation channel, so the invariant is
total without them and no scope kind exists for two members.

**As landed (S8, walker 148).** Deviations from and additions to the sketch
above, each forced by making the totality pin *real* rather than approximate:

- **A fifth scope kind, `dskWalkSite`.** The sketch scoped only the parse-time
  records the vetoes read. The run coordinate (`taintsRun`) also admits every
  record the *walker* makes — `degrade`, `lowerDegrade`, `closureDegrade`,
  `allocDegrade`, the extraction sink, and a `runSymex` boundary abort raised
  mid-walk. Such a record exists only because a path reached its site, so its
  reach is the record itself; it needs no join. Left unscoped it would have
  been bucket 4 on every run. The two walk arms that reach a *parse* anchor
  record that anchor instead (`isUnsupported`/`isUnsafeCast` →
  `dskSiteAnchored(marker)`, the missing-callee arm → `dskCalleeKey(key)`), so
  a reached parse decline carries two records under one anchor and an
  unreached one carries only the parse record — the join S9 reads.
- **Signature scope is the param-entry boundary.** A carrier raised by
  `raiseParamAllocIssue` (before any walk state exists) is recorded
  `dskSignature` at the `runSymex` boundary; every other boundary abort is
  `dskWalkSite`.
- **One funnel per record.** `ctx.parseErrors` is written only by
  `declineAtSite` (Class A: record + `isUnsupported` marker in one act),
  `declineUnsafeCast` (the `isUnsafeCast` sibling) and `declineCallee` (record
  + never-registered key); Class B mints its marker through `declineMarker`
  and records nothing at parse time (a parse record would trip the retained
  veto — a verdict change S8 may not make). Grep-pinned.
- **`isUnsafeCast` now records its reach.** The halt previously relied on the
  parse record alone; that says the cast *exists*, not that a path reached it.
- **`geConceptViolation` is decided before registration.** It ran inside
  `parseCalleeImpl`, i.e. after the callee was already being registered — the
  "never registered" premise of point 3 was false for it. The check is
  hoisted into `ensureProcRegistered` (`conceptViolationMsg`), so the key is
  genuinely never registered and the missing-callee arm is its reach.
- **A placement check, not a trust.** `parseProc` scans the *emitted* program
  (`placeDeclineScopes`) for every marker literal and never-registered key; a
  parse record whose anchor did not survive into the IR the walker walks is
  rescoped `dskUnplaced` — so a dropped marker is caught, not assumed away.
- **Bucket 4 today: empty for every run, with one construction `dskUnplaced` by
  design** — the Invariant-7 backstop, which fires only when nothing at all was
  recorded (there is no site to name). It is enumerated by name in the pin.

**As landed (S8b, walker 149) — three silent substitutions.** Found during
S6b/S10: sites in §2.2's class that substituted behaviour and recorded
*nothing*, so no channel, scope or veto could see them. Each was a false
verdict with an empty `errors`. S9 inherits them fixed, not hidden behind the
blanket vetoes it deletes.

- **Bodiless foreign callee.** A call to an `{.importc.}` (or `importcpp`,
  `importobjc`, `importjs`, `dynlib`) proc with no Nim body was registered and
  its EMPTY body walked, so the call returned the zero default. A target
  reachable only through the foreign result was a false `sxUnsat`.
  `isBodilessForeign` (`dsl_parser.nim`) now routes it through both
  call-position opaque arms, next to `{.symexOpaque.}`. The call gets a fresh
  result and a walk-site `feOpaqueCallUnmodelled`. That kind is reused rather
  than minted: `dcSubstituted` is the class the site earns (§3.2), because
  the result is fresh (⊇) and any foreign effect on state is dropped (⊆).
  Statement-position calls whose arguments are all values stay inert no-ops
  (#163's rule). `{.symexTransparent.}`/`{.symexOpaque.}` importc callees are
  unchanged. A bodiless proc over a `distinct` formal keeps its
  `geDistinctBarrier` callee decline.
- **`parseInt`.** The model is now `parseutils.rawParseInt` for every string
  with no `_`. It accepts one optional `+`/`-` sign, then digits only, in
  `int` range with Nim's asymmetric bound. The digits continuation used to
  drop every `+` string, a false `sxUnsat` for `parseInt("+5")`. A value
  outside `int` used to be an unbounded Int that never raised; now it raises
  `ValueError`. With `+` exact, only `_` is `seParseIntLaxSyntax`, since its
  value would need the version-gated `str.replace_all`. A `_` string now
  continues on a fresh, tainted value (`dcFreshSymbol`, replay-gated). S10
  dropped that continuation.
- **Exception hierarchy.** `exnTypeTable` had flattened `DivByZeroDefect`/
  `OverflowDefect` onto `Defect` and omitted `ArithmeticDefect`, so `except
  ArithmeticDefect` caught neither: a false `sxRaised`. The table now matches
  Nim's tree. That adds `ArithmeticDefect`, the `FloatingPointDefect` family
  and five more direct `Defect` children. The table is audited against the
  compiler's own `lib/system.nim` + `lib/system/exceptions.nim`, read at
  compile time. Found while auditing: an `except`/`raise` naming a type
  **alias** (a user `type E = ArithmeticDefect`, or system's deprecated
  `DivByZeroError`) used the alias's name as the type id. That id is in no
  table, so the handler silently never matched. `canonicalExnTypeSym`
  resolves aliases.

Pins: `tests/tsymex_rfc0005_s8b_substitutions.nim`. S10's two `+` pins
become clean verdicts (`"+5"` → `sxUnsat`, `"+x"` → an exact `sxRaised`), and
its confirmed-lax pin moves to `"1_x"`.

**As landed (S8c, walker 150) — name-resolved builtins.** The same class as
S8b, one level up: the parser recognised operators and builtins by **name**,
so a user overload was modelled as the builtin and nothing was recorded. A
user `+`/`<`/prefix `-`/`+=` on a `distinct`, a user `==` on an object, and a
non-generic `contains`/`len`/`items`/`add` that beats the stdlib generic all
gave false `sxSat`/`sxUnsat` with an empty `errors`. So did a
string-receiver `find` and a user proc merely named `symexAssume`.

- **Rule.** A builtin model applies only when the resolved callee is declared
  under Nim's lib dir (`isStdlibDecl`, `dsl_typebridge.nim`). Every
  name-dispatch site checks this through `isBuiltinNamed`/`isUserCallee`
  (`dsl_parser.nim`). A user routine is walked as an ordinary user call. That
  covers call, infix, prefix and hidden-conversion expressions, statement
  calls and aug-assign, and for-loop iterators. If the body cannot be walked,
  the call falls to the existing opaque/decline arms, so no new kind is
  needed.
- **Edges.** A `{.borrow.}` proc keeps its base model. A `method` stays a
  recorded callee decline (dynamic dispatch). A `converter` now walks: it is
  re-treed like a `func`, where before it was a `feUnsupportedExprKind`
  decline. The DSL markers match by their declaring module
  (`nelli/engine/markers.nim`), not by name.
- **Second order.** A stdlib generic whose instantiated body reaches a user
  `==`/`hash` is `system.==` over an object/tuple/seq, or `sets.contains` over
  a distinct key. It is already closed by the element fragment: a recorded
  `sxUnknown` (`feUnsupportedOp`, `seNestedSeqUnsupported`,
  `feUnsupportedWitnessType`). It is pinned, not guarded. A guard would be
  dormant, and the pins fire if the fragment widens.

- **Name-only models, removed.** Three models could be reached *only*
  through a user routine sharing a builtin's name. Each one was a
  substitution, and keeping a name allowlist for them would bring the bug
  back.
  - **`replaceAll`.** Nim has no stdlib `replaceAll`, so the entry is gone.
    Its all-occurrence model is what real `strutils.replace` does (both
    overloads). The resolved `strutils.replace` used to reach a
    *first-occurrence* model: `"foofoo".replace("foo","bar")` gave
    `"barfoo"`, which is a false verdict (`tsymex_phase15_S5_strops` pinned
    it `sxSat`). It now reaches `iekStrReplaceAll`, and `iekStrReplace` is
    deleted. The op stays version-gated: without
    `-d:z3WithSeqReplaceAll` it records `seZ3VersionMissing`
    (`dcFreshSymbol`, replay-gated), never a silent first-match. An empty
    literal `sub` returns `s` exactly, as `strutils` does
    (`if subLen == 0: result = s`).
  - **`bytes(s)`.** There is no stdlib `bytes`. `toOpenArrayByte` returns
    an `openArray`, not a value the model could stand for. So `iekStrBytes`,
    `smkStrBytes` and the `ResourceBudget.maxBytesEncodingLen` field (with
    its `;mbel=` settings-key segment) are deleted.
    `seBytesSymbolicLength`/`seBytesLengthTooLarge` are retired: the ordinal
    is kept and `classOf` is `dcNoAnswer`. A user `bytes` helper is walked.
    Its `for c in s` declines with a recorded `seByteIterUnsupported`.
  - **R8 `inc`/`dec` on a `ptr`.** `system.inc` takes an Ordinal, so the
    guard fired only on a user overload. `hePtrArith` is retired. Real
    pointer arithmetic goes through `cast`, which records `heUnsafeCast`
    (pinned in `tsymex_phase15_r8_ptr`).

  **Consumer-visible (S11 migration note).** Three changes:
  - `ResourceBudget.maxBytesEncodingLen` is removed.
  - `strutils.replace` results are now all-occurrence. On this Z3 build
    they are recorded `seZ3VersionMissing` rather than a clean
    first-occurrence value.
  - The three retired kinds are never emitted.

Left by name, deliberately: the receiver-mutation veto in
`scanShapeReceiverMutated` (a broad match only vetoes more), the diagnostic
hidden-marker scan, and type-name checks. Out of scope, noted for later:
`classifyType` classifies the `seq`/`Table`/`HashSet` type heads by name, so
a user type named `Table` would be misread. Pins:
`tests/tsymex_rfc0005_s8c_resolution.nim`.

**As landed (S8d, walker 151) — name-classified type heads.** S8c's noted
leftover, and the same class one level down: `classifyType` and the parser's
type-dependent arms recognised a type by its **name**. A user type spelled
like a stdlib or builtin type was modelled as that type, and nothing was
recorded. Each of these gave a false verdict with an empty `errors`:

- a user generic `seq`/`Table`/`HashSet` (here, an `array[3, T]`) took the
  container model, so its length was symbolic (false `sxSat`);
- a user alias `Natural = int` got `[0, high(int)]` (false `sxUnsat`);
- a user alias `int8 = int` made `low(int8)` fold to -128 (false `sxSat`);
- a user `Rune = distinct RuneImpl` took the `[0, 0x10FFFF]` intercept (false
  `sxUnsat`);
- a user enum named `bool` was two-valued (false `sxUnsat`).

- **Rule.** A type-head model applies only when the head's symbol is the
  stdlib type (`isStdlibTypeSym`, `dsl_typebridge.nim`). That means a
  compiler builtin, or a type declared under Nim's lib dir. The builtins
  (`int`, `char`, `string`, and the `seq`/`set`/`array`/`range`/`openArray`
  heads of an instance) have no declaration at all: `getImpl` is nil, and
  every user type has a `TypeDef`. So a nil impl identifies the builtin. Any
  other type is decided by its declaring file, as S8c decides callees. A
  generic instance is decided by its head symbol, which `getTypeInst`
  returns directly. `isBuiltinTypeHead` checks a head against a spelling
  set. `typeSpelling` feeds the name-keyed tables, and tags any non-stdlib
  symbol `user:` so that it matches no entry. `isStdlibRuneSym` is shared by
  both Rune sites.
- **What a user type gets instead.** Its structure, as for any other user
  type: a user enum named `bool` is that enum. Otherwise it gets the
  existing recorded decline for its shape. A user generic instance or plain
  alias is `feUnsupportedParamType`, which every user generic and alias of
  any other name already gets. `low`/`high` of a user type is the recorded
  A0 decline. A conversion to a user type named like an int or float is not
  the builtin conversion. No kind is minted.
- **Audit, with each site's check.**
  - `classifyType`: the raw `sink`/`lent`/`owned`/static-`array` arms, the
    post-`getTypeInst` `sink`/`lent`, `range` and `array` arms, the
    range-alias arm, the `bool` exclusion from the enum arm, the Rune
    intercept, the `seq`/`Table`/`HashSet`/`WeakRef`/`Atomic` container
    arm, and the scalar text match (`bool`, `string`, `char`, `byte`, the
    int and float spellings, `Natural`, `Positive`).
  - Parser: `valueTypeName`/`typeNodeName`, which feed the `nnkConv`
    int/float/bool conversion arms, the B2 width arms and the A0
    `low`/`high` fold; the `byte`/`uint8` literal unwrap; `isRuneTyped`;
    `unwrapGenericTy`'s `sink`/`lent`; and the G7 static-array binder,
    which now needs the argument's head to be the builtin `array` too.
  - An unresolved `nnkIdent` head keeps its spelling, as under S8c. The
    typed pipeline never presents a user type that way.
- **Name-only model removed.** The container arm's `WeakRef` spelling
  mapped to `__ownership:WeakRef`, but Nim's lib declares no `WeakRef`. So
  under the rule it could match only a user type, the same as S8c's
  `replaceAll`/`bytes`, and it is deleted. `Atomic` (`std/atomics`) keeps
  the ownership arm. `tsymex_r6_n42_deref_taint` and `tsymex_r6_n43_parity`
  had built a local `WeakRef[T] = distinct T` stand-in that depended on the
  name match. They now use the real `Atomic[bool]` and still pin the same
  `heUnsupportedOwnership` heap-deref decline.
- **Not covered here.** `Option`, `Deque`, `OrderedTable`, `CountTable`,
  `set` and `openArray` have no name arm, so a user type of those names was
  already the user-generic decline (pinned for `Option`). Two places
  outside the classifier still spell types by name:
  - The witness emitter (`symex.nim`, `dsl_parser.nim`'s emitters) writes
    `seq`/`Table`/`HashSet` and a user object's own name as identifiers in
    the caller's scope. If a caller shadows one, the result is a compile
    error, which is loud, not a verdict.
  - `derive.nim` and `jsonschema.nim` are PBT generator and schema code,
    not symex.

Pins: `tests/tsymex_rfc0005_s8d_typeheads.nim` (+ helper module
`tests/s8d_user_types.nim`).

**As landed (S9, walker 152) — both vetoes deleted.** `capForcedUnknown`
and `closureForcedUnknown` are gone from `runSymexImpl`. What each one used
to force is now decided by the lattice (§2.3) and the anchor on each record
(S8).

- **The reach join (`reachJoinParseErrors`, `runtime.nim`).** Take a parse
  record that is `taintsRun` and anchored (`dskSiteAnchored` or
  `dskCalleeKey`). If the drained walk records have no `taintsRun` record
  under the same anchor, no walked path reached the site. The parse record
  is then rewritten to `sevHint`, and its message gets the suffix
  `[never reached on a walked path: diagnostic only (RFC-0005 S9)]`. It
  stays in `errors`, but it no longer feeds `runTaint`. A record the join
  matches keeps its `sevError`. The verdict code reads the joined list
  (`parseErrs`) wherever it used to read `prog.parseErrors`.
- **"Reached" means walked, not feasible.** The walker forks both arms of an
  `if` without a feasibility check. So a decline in an arm that is walked
  but infeasible still has its walk record, and still taints that arm's
  path. That arm has no model, so the path taint is what drives the verdict,
  and it is scoped to the path. What the join recovers is narrower:
  `sxUnsat` behind a decline that **no** path walks. Examples are a handler
  for an exception nothing raises, a callee never called, or a label no path
  enters (`s9DeadHandler`: `sxUnknown` → `sxUnsat`, checked by
  `checkUnsatOverTaintOnly`). The `sxSat` recovery is wider and does not
  come from the join. Since the vetoes are gone, a clean path's hit is
  `sxSat` even when another path reached a decline (the S0 companions).
- **Dedup keys on message and anchor.** `dedupedByMsg` used to collapse two
  same-message walk records at different markers into one. That left the
  second marker with no walk record, so the join would have called a
  reached site unreached. The key is now `msg & "\0" & $scope`, pinned by
  twin Class-A casts and twin Class-B markers.
- **Class B is not unified with a parse record (deviation from point 1).**
  A Class-B `declineMarker` site still has only its walk record. Under the
  join, a parse record at a Class-B site could only ever be diagnostic: it
  would be `sevHint` when unreached, and a duplicate of the walk record when
  reached. Adding one would mint records that affect no verdict, so it is
  not done. The join does not read `collectUserExnAncestors`, and it
  decides nothing from handler shape. Reach is only the walk record.
- **An unplaced decline blocks both directions.** A `taintsRun` record
  scoped `dskUnplaced` (point 4) in the parse, walk or closure records sets
  `reachUnknown`, which forces `sxUnknown` from `decideVerdict`. This covers
  `sxUnsat` as well as `sxSat`, whatever the record's class, because the
  engine cannot say whether that site was reached. `decideVerdict`'s
  `vetoed` parameter is renamed `reachUnknown`. The threadvar
  `rfc0005UnvetoedStatus` is renamed `rfc0005RawStatus`: it is the decision
  procedure's status before S10's replay, and there is no longer a veto to
  bypass.
- **Capture by reference (the S7 handoff's `capMutNeg`).** A Nim closure
  reads a captured `var` as that variable stands at the call. `buildClosure`
  snapshotted the value at construction, which gave a false `sxSat` (dead
  label reported reachable) and a false `sxUnsat` (live label reported
  dead), both with an empty `errors`. The closure veto never caught this,
  because nothing was recorded.
  - The parser records the captures whose symbol is `nskVar`/`nskForVar`
    (`lambdaMutCaptures`; it is part of the canonical key, rendered
    `byref=[...]`).
  - The closure value records those captures and its constructing frame (a
    new `frameId` on `CallFrameCtx`).
  - In that frame, reading the closure (`iekVar`, `lowerClosureCall`)
    re-reads the by-reference captures from the current env
    (`refreshByRefCaptures`). This is exact.
  - Applied in any other frame (for example, passed to a callee), the
    snapshot may be stale. The descent records the new kind
    **`ceCaptureByRefUnmodelled`** (`dcSubstituted`: the stand-in is a stale
    value) through `closureDegrade`.
  - A body that writes a by-reference capture would have to write back to
    the caller's variable, and the descent's fresh env drops that write. It
    is detected by comparing each capture's value on every exit path
    against the entry (`sameSymVal`, identity of representation) and
    declined with the same kind.
  - `let` captures are unaffected and stay exact by value.
- **Flip audit.** No new `sxSat` comes from a path that passes a
  substituting site: rule 1 requires a path with no `scSpurious`, and every
  substituting record taints its path `⊤`. Every new `sxUnsat` below is
  checked by `checkUnsatOverTaintOnly`.

  | SUT | before | after | why |
  |---|---|---|---|
  | S0 pin 2 (`s0CapVetoCompanion`) | `sxUnknown` | `sxSat` (x = 42) | the reached cast taints only the other path |
  | S0 pin 3 (`s0ClosureVetoCompanion`) | `sxUnknown` | `sxSat` | the S7 path taint sits on the `x == 7` path only |
  | S8 (c) `castDeadS8` | `sxUnknown` | `sxSat` | the unreached decline is now a hint |
  | `s9CapCompanion` / `s9ClosureCompanion` (both consumers) | — | `sxSat` / `sfSat` | clean witness path |
  | `s9CapMutNeg` | `sxSat` (false) | `sxUnsat` | by-reference read, checked |
  | `s9CapMutPos` | `sxUnsat` (false) | `sxSat` (x = 7) | by-reference read, clean |
  | `s9CapBranch` | `sxSat` (false) | `sxUnsat` | by-reference read per arm, checked |
  | `s9CapEscaped` | `sxSat` (false) | `sxUnknown` | `ceCaptureByRefUnmodelled` |
  | `s9BodyWrite` | `sxSat` (false) | `sxUnknown` | `ceCaptureByRefUnmodelled` |
  | `s9DeadHandler` | `sxUnknown` | `sxUnsat` | reach join, checked |

  The full sweep moved no verdict outside these pins. Its one regression
  was the N27 placeholder-read audit, which flagged `sameSymVal`'s svSeq
  arm. That arm compares handles and the placeholder flag and lowers
  nothing. It is now tagged `[placeholder-audited]`, and the inventory is
  67 → 69.
- **Found, not fixed: shadowed names conflate in the env.** An inner `var k`
  that shadows an outer `k` shares the outer's env slot, so a write through
  either name is seen through both. This predates S9 and is independent of
  capture. It is left for a scope-keyed-names slice (S8e-shaped). *Fixed
  in S8e, below.*

Pins: `tests/tsymex_rfc0005_s9_vetoes.nim` (a)–(f), and
`tests/tsymex_rfc0005_s0_exhibit.nim` pins 2 and 3 (now `sxSat`).

**As landed (S8e, walker 153) — names keyed by symbol.** S8c resolved
callees by symbol and S8d type heads. Three more places identified a thing by
its spelling where Nim identifies it by its symbol.

- **Shadowed locals (the S9 finding).** The IR names every variable by a
  string. The walker's env, the closure capture lists, the `var`-param
  write-back map and the pre-pass collectors all key on that string, and the
  parser took it from `strVal`. So two distinct locals of one spelling
  shared one env slot. That covers an inner `var k` in a block, an `if` arm,
  a loop body, a for-variable, a closure body, or an inlined iterator body.
  The result was a silent substitution (§2.2): a false `sxSat` or `sxUnsat`
  with `errors` empty.
  - **Fix.** `smt/scoped_names.nim` claims each routine's declarations in
    source order, one naming scope at a time. A scope is the env the walker
    gives a routine: the entry proc, or a callee with its lambdas and
    inlined iterator bodies. A top-level proc used as a value gets its own
    scope. The first symbol to claim a spelling keeps it, so entry params
    keep their witness names. A later, different symbol with that spelling
    gets `k__scN`. Nim identifiers cannot contain `__`, so this collides
    with no user name.
  - **Why no per-site audit.** The module exports its own `strVal` in place
    of `std/macros.strVal`, and `dsl_parser` imports `std/macros except
    strVal`. So every symbol-to-name conversion sees the scoped name by
    construction. This covers declarations, reads and writes, the capture
    scan, the collectors and the iterator param substitution.
  - **The map audit.** Once IR names are unique per symbol, every
    name-keyed map is keyed by symbol: locals, `varArgs`, loop variables,
    captures. None needed its own change.
  - **Case narrowing.** The ADR-0029 narrowing stack keyed its scrutinee by
    `.repr`, which prints an inner and an outer `k` alike. It now keys on
    `scopedRepr`, which spells each symbol by its scoped name.
- **Generic callees lost their types.** `x in s` and `s.add x` over `type
  MySeq[T] = seq[T]` aborted the whole compile with `classifyType`'s "node
  has no type". So did any user generic whose body calls a helper. There
  were two causes.
  - `monomorphize` rebuilt every node with `newTree`, which drops the node
    type. It now uses `copyNimNode` and returns symbols unchanged.
  - The callee's formals were read from the generic declaration. They are
    now read from the instance's own `getTypeInst` (`instTy`), which gives
    typed concrete nodes such as `openArray[int]`.
  - **Result.** A user generic is walked and modelled. The alias cases now
    reach the existing recorded declines. As a param, that is S8d's
    user-alias `feUnsupportedParamType`. As a local, it is a
    parse/walk decline for the stdlib body the alias does not model. No
    case crashes.
- **Witness emitters spelled types by name.** `symex.emitTyAndReader`
  builds the witness in the caller's scope. It wrote the following as bare
  identifiers:
  - `seq`, `Table` and `HashSet`, the scalar types and the readers;
  - a user object's, enum's or distinct's name;
  - an enum member.

  A caller that imported only the SUT could not compile it. A caller that
  holds another symbol of that spelling had the witness built through that
  symbol. For example, S8d's dropped non-generic user `OrderedTable` bound
  to `std/tables.OrderedTable`, and a local enum `Color` silently re-typed
  the witness. Now:
  - fixed names are `bindSym`-bound (`stdName`);
  - a user type is named by its own symbol, which `dsl_typebridge`
    recorded under `IRType.typeKey` at classification (`keyedBySym`,
    `witnessTypeSym`). `typeKey` is compile-time only, and `==`, `$` and
    the canonical form ignore it;
  - a discriminator is written `DiscTy(ordinal)`, not by member name;
  - `default(T)` becomes `var w: T; w`, and `new(T)` becomes `var c: ref
    T; new(c)`, because a typed-AST symbol is not a `typedesc` argument;
  - the result is unshared with `copyNimTree`.

  In `dsl_parser`'s IR emitters, enum values go through `newLit` (a
  conversion through the enum type's symbol), and `string` is `bindSym`.
- **Flips.**

  | SUT | before | after |
  |---|---|---|
  | block / `if`-arm shadow, inner write | `sxSat` (false) | `sxUnsat`, checked |
  | block / param shadow, outer read | `sxUnsat` (false) | `sxSat` |
  | loop / `while` / for-variable shadow | `sxSat` (false) | `sxUnknown` (`beBudgetExhausted`, as the unshadowed loop) |
  | closure captures `k`, inner `k` written | `sxSat` (false) | `sxUnsat`, checked |
  | lambda captures `k` and declares its own | `sxUnknown` (`feGlobalReadUnmodelled`) | `sxUnsat`, checked |
  | inlined iterator local named like a caller local | `sxSat` (false) | `sxUnsat`, checked |
  | case narrowing, shadowed scrutinee | `sxUnsat` (false) | `sxSat` |
  | alias `in`/`add`, user generic calling a helper | compile abort | decline / `sxSat` |
  | witness of a type the caller cannot name | compile error or wrong type | `sxSat`, correct witness |

- **Consumer-visible.** A shadowed local's IR name is `name__scN`. It shows
  in decline messages and cache keys, so the walker bump invalidates those
  caches. Code that failed to compile now compiles:
  - generic callees;
  - witnesses of types the caller did not import.

  A caller no longer needs `std/tables` or `std/sets` in scope for a
  `Table`/`HashSet` witness.

Pins: `tests/tsymex_rfc0005_s8e_scoping.nim` (a)–(d) (+ helper module
`tests/s8e_user_types.nim`).

**As landed (S8f, walker 154) — a clean `sxSat` whose witness reproduces;
open.** S8e found `proc f(t: Table[string, int])` with target `t.len == 2`
returning a clean `sxSat` whose witness rendered `{:}`. This part closes the
container gap and the variant gaps the replay audit found. The audit also
found model defects outside this slice's design, so the slice stays open (see
"Remainder" below).

- **Containers.** `Table`'s and `HashSet`'s `len` was a free integer in
  `[0, 1024]`, never tied to the present/member array.
  - The model: every check asserts, for each allocated table and set, `len >=`
    the number of distinct present key terms among every key term the run
    selected at (`ContainerCardRegistry`, asserted in `trySolve` as
    `cardConds`). That is a fact of every real table, so it prunes no real
    input, and it makes every model realizable.
  - The extractor renders the present values of the run's key terms plus fresh
    fill up to `len`. That covers symbolic keys and tables in object fields,
    where the old literal scan rendered nothing. A seq renders all `len`
    elements; it was cut at 64.
  - Audit per container:
    - `Table` and `HashSet`: fixed as above.
    - `seq`: the 64-element cut is fixed. `seq`/`array` of `ref T` rendered
      every element as a fresh default cell. Each element now renders its own
      cell: nil, an earlier element it aliases, or its observed fields.
    - `string`: Z3's own `str.len`, sound and faithful. No gap.
    - `OrderedTable` and `CountTable`: not modelled. They decline with
      `feUnsupportedParamType`, so there is no claim to be wrong.
- **Variant reassignment (ADR-0003 amended).** Nim 2 raises `FieldDefect` on
  a discriminator assignment that changes the object's branch, and keeps the
  fields on one that does not. The walker modelled the pre-2.0 zero-init.
  Both reassignment arms now fork `FieldDefect` on "old branch != new branch"
  and carry the branch's fields otherwise. The IR carries the branch grouping
  as `vrBranches`/`vrsBranches`, so the cache keys change.
- **Variant construction (ADR-0029 amended).** In `isVariantConstructSym`,
  every arm field is now its type's `default(T)`; it was fresh, so
  `p.rq == 777` was a false `sxSat`. A field with no modelled default declines
  the construction.
- **`defaultZero` float arm.** `defaultZero(float)` returns 0.0; it raised.
  Construction needs it, and an untouched `float` call result now binds Nim's
  `default(float)` where it was havocked (`feUnsupportedOpHavoc`). The
  "no zero default" pins in `r6_r2_zerodefault_result` and `s6b_ops` move to
  a variant result.
- **Range-discriminator witness.** A `range` discriminator's `else:` arm
  renders its tag and fields; it rendered `kind: 0`.
- **Replay decision (S10 on clean candidates): no.** Replay is not extended
  to confirm clean candidates as the mechanism for the minimum. A test-only
  patch replayed every clean `sxSat`/`sxRaised` in the suite against the real
  SUT and showed three problems:
  - Faithful refutations were real model defects, fixed here or listed below.
  - Four were wrong refutations from a settings mismatch: the analysis
    declares unchecked integer semantics while the SUT build is checked
    (`163rev_concolic_modes:340`, `phase2_overflow:48/55`,
    `161_overflow_obligation`). Clean replay would demote true claims unless
    it is gated on the declared semantics matching the build.
  - Every `ref`-witness miss is `wfLossy` or `wfUnexecutable`, and a lossy or
    unexecutable miss is inconclusive by S10's own rule. So replay cannot
    enforce the minimum where it is violated most.

  The mechanism is therefore by-construction fixes, as above. A gated clean
  replay as a safety net is the open fork (c) below.
- **Flips.**

  | SUT | before | after |
  |---|---|---|
  | `t.len == 0 and t.hasKey("a")` (and the set twin) | `sxSat` (false) | `sxUnsat` |
  | `t.len == 2`, symbolic key, table in a field | `sxSat`, witness `{:}` | `sxSat`, reproduces |
  | branch-changing reassignment of a param | `sxSat` from the wrong branch | `sxSat` from the new branch, or `sxRaised` `FieldDefect` |
  | branch-changing reassignment of a local | `sxSat` (false) | `sxRaised` `FieldDefect`, checked |
  | same-branch reassignment reading the kept field | `sxUnsat` (false) | `sxSat` |
  | runtime-discriminator construction, arm field `!= 0` | `sxSat` (false) | `sxUnsat` |
  | untouched `float` result | `sxUnknown` raw (havoc), replayed to `sxSat` | `sxSat` clean; `!= 0.0` is `sxUnsat` |

- **Remainder (open; the slice's blocker).** Faithful replay refutations
  outside this slice's design:
  - float-to-int conversion never raises in Nim 2.2.10: `int(1e30)`, NaN and
    Inf give `low(int)`. So R16-2's `RangeDefect` fork is fictional. Every
    `sxRaised` in `CR3_CR4_CR6_float`, `cr9_lowerInExpr`, `F5_float_conv`,
    `F5_probeproto`, `R16_2b_shortcircuit_conv` and `R16_2_rangedefect` is
    false, plus that last file's `sxSat` at :59.
  - `split(s, "")` gives `@[s]` in Nim but is modelled bytewise
    (`S5_strops:101`).
  - `new int` is not zero-initialised (`r2_new:87/93`).
  - Unary negation overflow is unmodelled: `-low(int)` raises
    `OverflowDefect` (`r6_r2_zerodefault_result:369`).
  - Slice and `seq.del` out of bounds raise `RangeDefect`, but are claimed as
    `IndexDefect` (`r4_seq_slice:115`, `r6_n14_seqops:312`).
  - `ref`-witness lossiness, probe-confirmed non-reproducing `sxSat`:
    - a top-level ref param's nil renders non-nil;
    - cross-param aliasing `p == q` renders distinct cells;
    - a recursive live ref field renders nil;
    - a ref in a by-value object field does not render.
  - The symbolic reassignment's candidate tags skip the `else:` arm (-1), so
    paths to else-covered values are dropped (a false-`sxUnsat` risk).

Pins: `tests/tsymex_rfc0005_s8f_witness.nim` (a)–(e); re-pinned to Nim
semantics, each with a real-SUT oracle where one applies: `phase11_walker`,
`r6_n13`, `r6_a3`, `r6_a4`, `r6_n9`, `r6_lows_blockparse`, `r6_n14_seqops`,
`r6_lows_declines`, `r6_n36_raise_degrade`, `r6_r2_zerodefault_result`,
`rfc0005_s6b_ops`; the audit inventories `r6_n27` (+2 guarded
`seqDataRaw` reads) and `r6_n36_raise_class_audit` (-1 float raise).

**As landed (S8g, walker 155) — faithful scalar, string and defect models.**
Six of S8f's remainder items were model defects: the walker claimed behaviour
real Nim does not have. Each is now fixed by construction. Replay is still not
extended to clean candidates. Every flip below was probed on the pinned
toolchain (Nim 2.2.10, c and cpp identical, debug build).

- **Float to int (ADR-0011 R16-2 reversed in place).** `int(f)` casts first
  and checks the cast value, so an int-family target never raises:
  - `int(1e30)`, `int(NaN)` and `int(Inf)` all give `low(int)`;
  - `int32(1e30)` gives 0, and `int8(300.0)` gives 44;
  - `Natural(-5.0)` raises `RangeDefect`.

  The model:
  - In range, the value is exact at the target's own width and signedness.
    An 8- or 16-bit target was not modelled at its own width.
  - Out of range, the value is fresh and taints the path through
    `feConvFloatToIntUndefined` (`dcFreshSymbol`). A candidate that depends on
    it is replayed and either confirmed or refuted.
  - A `range` target forks `RangeDefect` on the converted value. It uses the
    general `rangeDefectConds` sink, which replaces `convFloatToIntDomainConds`
    and is shared with slice and `del`.
  - Gone: `drainConvFloatToIntBounds`, the in-domain narrowing (which made
    every out-of-range value falsely unreachable) and
    `drainConvFloatToIntRaises`.
- **Unary negation.** On a signed int, `-x` and `abs(x)` are `0 - x` under
  the overflow check. So `-low(T)` raises `OverflowDefect`; it used to wrap.
- **`split(s, "")`** is `@[s]` for a literal or symbolic receiver. It was a
  byte-wise split for a literal receiver and a `seZ3StringIncomplete`
  decline for a symbolic one.
- **`new T` for a non-object `T`** (`new int`, `new bool`, ...) stores
  `default(T)` in a heap keyed by the type. It was a free cell. A type with
  no modelled zero value declines with `heNewFieldZeroUnsupported`.
- **Slice and `del` defect classes.**

  | Operation | Condition | Result |
  |---|---|---|
  | `s[a .. b]` on a seq or string | non-empty and out of bounds | `IndexDefect` |
  | `s[a .. b]` on a seq or string | negative length (`b < a - 1`) | `RangeDefect` |
  | `s[a .. b]` on a seq or string | empty past the end | no defect |
  | `substr(s, a, b)` | any bounds | clamps |
  | `del(i)` | `i < 0` | `RangeDefect` |
  | `del(i)` | `i >= len` | `IndexDefect` |

  Before, a seq slice was an `IndexDefect` for every out-of-bounds case, a
  string slice clamped, and `substr` did not clamp a negative start.
  A `^k` bound of a string slice, and the low `^k` bound of a seq slice,
  read as `k` rather than `len - k`: `s[1 .. ^1]` of "abcd" was "b". The
  clamping extract hid this until the slice forked its defects (the
  `retest_c11_stack` shape `s[1 .. ^1]` on a 1-byte string then raised a
  false `IndexDefect`).
- **Symbolic discriminator reassignment** forks the `else:` arm. Its guard is
  "the RHS equals no explicit tag", and its new discriminator is the RHS
  itself. So `kC -> kD` under `else:` keeps the branch's field, and
  `kA -> kD` raises `FieldDefect`. The else arm used to have no path, so
  both were a false `sxUnsat`.
- **Drain fixes found on the way (same mechanism: a raise fork dropped).**
  - The deref-write sites (`p[] = e`, including inside a variant arm) now
    drain the RHS's scalar raise forks. Before, a raise in such an RHS
    (for example `p[] = a div b`) was dropped.
  - `drainScalarRaiseForks` now forks every sink on every survivor of an
    earlier stage. It used to fork only on the first survivor, for example
    after `parseInt`'s lax continuation.
  - `if`, `assert` and `assume` now walk every drain continuation, not just
    the first.
- **Flips.**

  | SUT | before | after |
  |---|---|---|
  | `int(f)`, target `RangeDefect` | `sxRaised` (false) | `sxUnsat` |
  | `try: int(f) except RangeDefect: label` | `sxSat` (false) | `sxUnsat` |
  | `int8(f)`/`uint8(f)` of an out-of-range `f` reaching a label | `sxUnsat` (false) | `sxSat`, reproduces |
  | `int(NaN) == low(int)` | `sxRaised` | `sxSat`, replay-confirmed |
  | `int(NaN) == 7` | `sxRaised` | `sxUnknown` (`feReplayRefuted`) |
  | `Natural(f)` on a negative `f` | `sxUnsat` (false) | `sxRaised` `RangeDefect` |
  | `-x` / `abs(x)` at `low(T)` | `sxUnsat` (false) | `sxRaised` `OverflowDefect` |
  | `"abc".split("") == @["abc"]` | `sxUnsat` (false) | `sxSat` |
  | `(new int)[] != 0` | `sxSat` (false) | `sxUnsat` |
  | `data[4 .. ^1]`, short `data` | `IndexDefect` | `RangeDefect` |
  | `data[5 .. 4]` on a 3-seq | `IndexDefect` (false) | no defect |
  | `s[1 .. 7]` on a 3-string | no defect (false) | `IndexDefect` |
  | `del(-1)` | `IndexDefect` | `RangeDefect` |
  | `substr(s, -2, 1)` | `sxUnsat` (false) | `sxSat` |
  | `s[1 .. ^1] == "bcd"` for `s == "abcd"` | `sxUnsat` (false) | `sxSat` |
  | symbolic reassignment into `else:` | `sxUnsat` (false) | `sxSat` / `FieldDefect` |

- **Consumer-visible (for S11's migration note).**
  - `int(f)` and `intN(f)`/`uintN(f)` no longer report `RangeDefect`, and a
    `try/except RangeDefect` around one is dead. `Natural(f)` and other range
    targets do report it.
  - There is a new error kind, `feConvFloatToIntUndefined`, appended to the
    enum (`dcFreshSymbol`). An exhaustive `case` over `SymexErrorKind` needs
    an arm for it.
  - `-low(T)` and `abs(low(T))` report `OverflowDefect`.
  - `split(s, "")` is `@[s]`, and `new int` reads 0.
  - The class of a slice or `del` defect can change between `IndexDefect`
    and `RangeDefect`. A string slice now raises, and `substr` clamps.
  - A deref-write RHS's raise now surfaces.
  - The CFI canonical form carries width, signedness and range. With the
    walker bump to 155, every symex cache entry is invalidated.
- **Different mechanisms, reported and not fixed here.**
  - `low(int) div -1` raises `OverflowDefect` in Nim, and `low(int) mod -1`
    crashes with SIGFPE. Neither is modelled: `divBV` forks only on zero.
  - `toFpFromSigned` converts a `uint64` to float as signed.
  - An explicit int-to-range conversion (`Natural(x)` for an int `x`) is a
    pass-through with no `RangeDefect`.
  - Symbolic reassignment of an object whose construction was declined hits
    an internal walker assertion (`weInternalWalkerFault`).
  - The concolic `walkIfFollowConcrete` never drains scalar raise forks.

Pins: `tests/tsymex_rfc0005_s8g_models.nim` (1)–(7).

Re-pinned to Nim semantics, each checked against the real SUT:
- `phase15_CR3_CR4_CR6_float`;
- `phase15_CR11_CR18_splitcap` (an empty-separator split is one part, so a
  5-part result is `sxUnsat`);
- `r6_n36_raise_degrade` (the split-cap decline's vehicle is now a
  literal-separator split);
- `phase15_cr9_lowerInExpr`;
- `phase15_F5_float_conv`;
- `phase15_F5_probeproto` (clean `sxSat` whose witness reproduces);
- `phase16_R16_2_rangedefect` (rewritten around `int` vs `Natural`);
- `phase16_R16_2b_shortcircuit_conv` (the guard now exercised through
  `Natural`);
- `phase15_rereview_drains` (NI-2-2);
- `phase15_S5_strops` (split empty separator);
- `phase15_r2_new` (the disjoint arms write before reading);
- `r4_seq_slice` (unguarded slice is `RangeDefect`);
- `r6_n14_seqops` (a `del` `IndexDefect` means `i >= len`).

Inventories:
- `rfc0005_s1_lattice` (new kind);
- `r11_range_invariant_audit` (+1 marker-exempt `bvRangeConds`, the
  range-defect check);
- `r6_n36_raise_class_audit`: the two removed empty-separator split raises,
  and one category-c raise added in `discFromRhs`. Also the
`phase15_CR2_cachekey` pin (155).

**As landed (S8h, walker 156) — ref witnesses that reproduce.** A clean
`sxSat`/`sxRaised` whose witness holds a ref or ptr is now built from the
solver model's **input** heap. Running the SUT on it takes the path the
solver proved. Before S8h, four shapes each produced a false clean `sxSat`:

1. A nil top-level ref param rendered non-nil.
2. Params at one model address rendered as distinct objects.
3. A live recursive ref field (`n.next != nil`) rendered nil.
4. A ref inside a by-value field (`Holder.n`, a tuple field) rendered nil.

The same mechanism also caused a fifth: (5) a cell's fields showed the heap
the SUT had **written** by the end of the path, not the heap it was called
with. For example, `p.v == 0` followed by `p.v = 1` rendered `v: 1`.

- **Runtime.** `buildHeapSnapshot` works in three steps:
  - It collects every ref/ptr position of the input. That covers params and
    positions inside by-value params (tuple, array, seq, variant, distinct,
    closure captures), each named the way the emitter names it.
  - It assigns one cell per model address. Bare params are named first, in
    lexicographic order, then the rest breadth-first.
  - It reads each cell's fields by selecting from the free input constant
    `heap_<key>` of every heap that the winning path materialised.

  `mkHeapArrayVar` records each heap's value type in `heapKeyShapes`, plus
  the variant for `__@disc`/`__@<ord>__f` heaps. As a result, a cell whose IR
  pointee is a recursive-field placeholder still renders every observed
  field, and a case object renders its discriminator and active branch. The
  walk has no depth cut: it follows model addresses, which form a finite
  universe, until it reaches nil or a cell that is already named.
  `currentHeapDerefVals` and `extractFromSymVal`'s proto-default cell leaves
  are deleted, as is `clampWitnessFieldsDeep`. `currentHeapDerefVals` held the
  last value read through a param name on any path, not necessarily the
  winning one.
- **Emitter.** Every ref/ptr position renders as `resolveRef[T](ctx, pos)`.
  All four tuple sites share one `RefWitness` per witness tuple through
  `emitWitnessTuple`. For each position the call returns one of:
  - nil;
  - the object already built for that address;
  - a new cell, filled generically over the SUT's own Nim type (`fieldPairs`
    under `uncheckedAssign`, so case objects work).

  A field that the model never observed gets `validDefault`, which is
  `low(F)` wherever a zeroed range or enum field would lie outside its
  declared range. It recurses through by-value aggregates, doing the job
  `clampWitnessFieldsDeep` used to do. Seqs and arrays of refs resolve per
  element. S8f's `rebaseWitness` and
  `refCell*` readers are deleted. A `ptr` to an object or scalar renders an
  `alloc0` cell instead of a nil placeholder. In `witnessFidelity`, a ref cell
  is `wfFaithful` when every one of its field kinds is modelled by the logical
  heap (int/enum, bool, float, ref, ptr), so S10's replay refutes a miss.
  Every other ref cell is `wfLossy`.
- **Consumer-visible (for S11's migration note).**
  - Typed ref witnesses now carry nil, aliasing and cycles. Each address is
    one object, whether it is reached through a param, a field or an element.
    Field values are the input values.
  - A `ptr T` witness is a real cell, never freed, instead of nil.
  - `heapSnapshot` changes in several ways:
    - It shows the input heap.
    - It has an entry for every ref position of a param, including positions
      inside by-value params.
    - Cells are named breadth-first.
    - `"<max-heap-depth>"` is gone.
    - A variant cell shows its discriminator and active branch.
    - An unobserved scalar pointee has `pointsTo` none; it was `"0"`.
  - S10 replay treats these ref witnesses as faithful, so a miss refutes.
  - The walker bump to 156 invalidates every symex cache entry.
- **Different mechanisms, reported and not fixed here.**
  - An inline `ref <case object>` field reached through a ref (`h.v.kind ==
    vkB and h.v.b == 5`, with `v: ref VObj`) yields a false `sxUnsat`. In
    isolation it yields `sxUnknown(ekZ3Error)`. A named alias (`VRef = ref
    VObj`) works. This is already present on `f91eb94`.
  - `renderAsChoices`, and so `assertCoveredBy`, still rejects ref params at
    compile time.

Pins: `tests/tsymex_rfc0005_s8h_refwitness.nim`. It covers the four
violations, a cycle, alias through a field, input-versus-written fields, a
`ptr` cell, a variant field, seq-element aliasing, and the `>= 156` floor.

Re-pinned, each checked by running the SUT on the witness under real Nim:
- `phase15_E5_finally` had pinned the values the SUT writes. It now pins two
  live, distinct cells, and running the SUT on the witness raises
  `ValueError`.
- `phase15_r13_ptr_finally` had pinned the written `"7"`. Running the SUT on
  the witness now raises `ValueError`.
- `h_witness` had pinned a depth-cut chain with a `"<max-heap-depth>"`
  marker. It now pins three distinct live typed cells, and running the SUT
  on them hits the label.
- `163rev_armfield_write` had pinned the written `v == 55`. It now pins an
  input `v` in `1 .. 100`, and running the SUT on the witness takes the
  `nkA` branch and writes 55.
- `a2_refvariant_fields` read-after-write had pinned the written `g ==
  99`. Running the SUT on the witness now takes the `cGreen` arm and writes
  99.
- In `163rev_nested_clamp`, the never-dereferenced `c2` may now be nil,
  which is faithful. The range oracle runs only on a live cell, and both
  SUTs run on their witnesses.
- `phase15_CR2_cachekey` pin (156).

**As landed (S8i, walker 157) — S8g's different-mechanism remainder.** S8g
reported five defects whose mechanism lay outside its design. Each was a
claim the real SUT contradicts, or an internal walker fault. Every expected
behaviour was probed against the pinned toolchain (c and cpp identical):

1. `low(T) div -1` raised nothing in the model; Nim raises `OverflowDefect`
   at every signed width. `low(T) mod -1` continued as 0; at 32 and 64 bits
   the C division traps (SIGFPE, an uncatchable abort), while `low(int8)` and
   `low(int16)` `mod -1` are 0. Along the way, signed `mod` took the
   divisor's sign (`bvsmod`: `-7 mod 2` modelled as 1, Nim gives -1), and the
   Int-sort `div`/`mod` were Euclidean.
2. `float(x)` of a `uint64` treated the pattern as signed: every value
   `>= 2^63` became negative.
3. An integer conversion to a `range` or enum target (`Natural(x)`,
   `Positive(x)`, `range[a..b](x)`, `R(x)`, `E(x)`) was a pass-through. The
   implicit conversion into a range type (`let q: R = x`,
   `var n: Natural = x`, a `Natural` object field, an `int8` into a
   `Natural`) was too. Nim range-checks all of them (`RangeDefect`).
4. Reassigning the discriminator of an object whose construction was
   declined hit a `doAssert` in both reassignment arms
   (`weInternalWalkerFault`).
5. The concolic `if` walker never drained its conditions' scalar raises: a
   closure call that raised on the trace had its raise dropped, and the
   handler's decisions were never recorded. A let-site raise the trace did
   not take was still routed into its handler, recording a decision that
   never happened and making `pcSatByConcreteInputs` false.

- **Runtime.**
  - `lowerArith`: signed `div`/`mod` push `divLowByMinusOne` (in the
    operands' native sort; skipped when an svInt's interval excludes
    `low(T)`). `div` pushes it to `overflowConds` (acOverflow-gated). At
    widths 32/64 both push it to the new survivor-only `arithTrapConds`
    sink, whose drain (`drainArithTraps`, after the overflow stage in
    `drainScalarRaiseForks`, ungated) adds the negation to the
    continuation's defect-survivor facts and forks no raise.
  - `modBV` signed uses `bvsrem`; `arithInt`'s `div`/`mod` go through
    `truncDivInt` (the Euclidean pair adjusted toward zero).
  - `iekConvIntToFloat` uses `toFpFromUnsigned` for an unsigned 64-bit
    operand (narrower unsigned operands were already zero-extended).
  - `iekConvIntWidth` gains `ciwHasRange`/`ciwLo`/`ciwHi`. A range target
    lowers through `lowerConvIntRange`: the bounds clamped to the operand's
    own type, the negated check to `rangeDefectConds` (acRange-gated, as
    S8g's float -> range check), and the value converted to the target width
    (extend, retag or truncate — exact wherever the check passes). The
    parser emits it for an explicit `nnkConv` whose target is a range/enum
    and whose operand is an integer, and for a hidden conversion into a
    range type unless the operand's own range lies inside the target's.
    An array index is excluded: Nim wraps `arr[i]`'s index in the same
    hidden conversion to the index type but checks it as an index
    (`IndexDefect` "index 7 not in 0 .. 4", probed), which `isIndex`
    already forks. The array-index parse marks that one conversion
    (`ParseCtx.indexConvPending`). `rhsHasInlineDefectFork` treats the
    range conversion as forking; its canonical key includes the bounds.
  - `degradeUnmodelledReassign`: a reassignment of a non-variant object
    records `feUnsupportedOp`, unbinds the object and taints the path. The
    kind is `dcSubstituted`, not `feUnsupportedOpHavoc`, because the site
    drops the branch-change `FieldDefect` fork (§3.2 standing rule).
  - `walkIfFollowConcrete` drains each condition. A continuation whose new
    defect-survivor facts the draws contradict is not followed, and those
    facts join `concreteBranchOutcome`'s solves (a closure call's exit facts
    define its result). Under `wmFollowConcrete`, `routeRaise` drops a raise
    path the draws contradict (`concretelyInfeasible`).
- **Consumer-visible (for S11's migration note).**
  - New findings: `OverflowDefect` from `low(T) div -1`; `RangeDefect` from
    explicit and implicit int -> range/enum conversions. A defect surfaces
    under any target, so a `tRaisedExn("X")` search can now return one of
    these instead of `sxUnsat`.
  - Paths through `low(T) mod -1` at 32/64 bits (and `div` with overflow
    checks off) no longer continue: a label reachable only through the trap
    is `sxUnsat`.
  - Signed `mod` results and `float(uint64)` values change to Nim's; SAT/UNSAT
    verdicts that depended on the old values flip.
  - A reassignment of a declined construction is `sxUnknown` with
    `feUnsupportedOp`, not `weInternalWalkerFault`.
  - Concolic collection: `branchTrace` gains the handler decisions of a
    raising `if` condition and loses records from handlers the trace never
    entered; `ambiguousBranches` drops for a closure condition that raised.
  - The walker bump to 157 invalidates every symex cache entry.
- **Different mechanisms, reported and not fixed here.**
  - The SUT's own top-level `return <expr>` is never lowered: `isReturn`
    with an empty call stack ends the path without lowering or draining
    `retExpr`. Every raise in the returned expression is lost. `return 100
    div x` and `return x` from a `Natural` proc both give a false
    `sxUnsat` for their defect, while the `result = ...` forms raise. A
    callee's `return` is lowered and drained (R1). This is present before
    S8i.
  - A concolic `if` whose condition is a closure call that returns normally
    stays ambiguous. The closure's ground axioms are implications guarded by
    the whole caller pc, so `concreteBranchOutcome`'s solves do not see
    them. A closure that raises on the trace is resolved (item 5).
  - A narrowing integer conversion (`int8(x)` from an `int`) is still a
    recorded decline. It is not modelled as a `RangeDefect` fork.
  - `renderAsChoices` still rejects ref params, and an inline `ref <case
    object>` field reached through a ref is still a false `sxUnsat` (both
    reported under S8h).
  - Z3 does not finish a query whose witness needs a string longer than
    about a thousand bytes, and `rlimit` does not bound it. A label search
    for `findColon(s, 0) > 1000` over a scan loop does not terminate on
    `4cfa655`, before S8i. S8i's range check at a callee's `return i` into
    `range[0..1000]` (`163rev_intoffset_range`) issues exactly that query:
    the `RangeDefect` is real (Nim raises it for a 1001-byte string with no
    early `':'`), but its solve does not return. That test pins the #163 W8
    placeholder range, so it now runs with `acRange` off (re-pinned below);
    the callee-return check is pinned at a bound Z3 can witness.

Pins: `tests/tsymex_rfc0005_s8i_models.nim`. It covers:
- `div -1` at 64, 32 and 8 bits;
- the `mod -1` trap at 64 and 32 bits and its absence at 8 bits;
- a witness steered off the trap;
- the sign of `mod`;
- `float` of a `uint64`, including `float32(high(uint64))`;
- explicit `Natural`, subrange, anonymous range, `Positive`-of-`int8` and
  enum conversions, with in-range values and a live `except RangeDefect`;
- the implicit `let`, `var`, object-field and `int8 -> Natural`
  conversions;
- an out-of-bounds array index, which stays an `IndexDefect`;
- a callee's `return x` into a `range[0..10]` result;
- symbolic and literal reassignment of a declined construction;
- the concolic let-site and closure raising conditions, both raising and
  returning;
- the `>= 157` floor.

Each test comment cites the real-Nim probe it relies on.

Re-pinned, each checked against real Nim:
- `phase16_R16_3_divzero` R16-3-4 had pinned "nothing raised" for
  `sg(a, b)` (`b != 0 and a div b > 5`). A defect surfaces under any
  target, and `low(int) div -1` now raises `OverflowDefect`. The pin is now
  "no `DivByZeroDefect`", and when an `OverflowDefect` is found, running
  `sg` on the witness must raise it.
- `phase16_R16_3_divzero` R16-3-6 (`acDivByZero` off) had pinned
  `sxUnsat`. It now admits the `OverflowDefect` at `(low(int), -1)`, which
  real Nim raises.
- `r6_n36_raise_class_audit` pattern-(B) inventory: 77 -> 78 marked
  `runtime.nim` lines and 80 -> 81 category-c. The new site is
  `divLowByMinusOne`'s caller-guarded `else`.
- `r11_range_invariant_audit`: 4 -> 5 `bvRangeConds` calls, with
  `runtime.nim` going 3 -> 4 and 4 procs. The new call is
  `lowerConvIntRange`'s `range-defect-check`.
- `phase15_A1_arithmetic`: the open `bMod` sign note is marked resolved.
  The cell's domain is unchanged.
- `163rev_intoffset_range` had pinned `sxUnsat` for three label searches
  whose callees `return i` into `range[0..1000]`. That is the old model:
  Nim raises `RangeDefect` there (the file's own oracles), and the
  finding's witness is a string Z3 cannot build (see Different
  mechanisms). The three searches now run with `acRange` off, which keeps
  their subject, the W8 placeholder range, and their `sxUnsat`.
- `phase15_CR2_cachekey` pin (157).

**As landed (S8j, walker 158) — S8i's unlowered exits.** S8i reported four
defects outside its design. Each was a claim the real SUT contradicts.
Every expected behaviour was probed against the pinned toolchain (c and cpp
identical):

1. The SUT's own top-level `return <expr>` was never lowered: `isReturn`
   with an empty call stack ended the path without lowering or draining
   `retExpr`. `return 100 div x` and `return x` from a `Natural` proc gave a
   false `sxUnsat` for their defect, and a raising `return` inside a `try`
   never reached its handler. The concolic walker dropped the same raise,
   so the handler's decisions were never recorded.
2. An inline `ref <case object>` field reached through a ref (`h.v.kind`
   with `v: ref V`, `V` a case object) was an `ekZ3Error` `sxUnknown`
   ("Sorts Ref_… and Ref_… are incompatible"), not the false `sxUnsat` S8h
   reported. The field's placeholder keyed its `Ref_<id>` sort by the
   type's nominal id; the nil literal and the deref classify the full
   variant, whose id was structural.
3. A narrowing integer conversion was a recorded decline (`int8(x)`,
   `uint8(x)`, `char(x)` of a wider int). At the same width, unsigned ->
   signed (`int8(x)` of a `uint8`) was the unchecked reinterpret, and any
   conversion of a subrange operand (`int8(x)`, `x: range[0..1000]`) was
   the identity pass-through: 1000 flowed on as the `int8`. Nim:
   - a signed target checks the value against its own bounds:
     `int8(200)`, `int8(300'i16)`, `int8(200'u8)`, `int32(high(uint32))`,
     `int(2^63'u64)` raise `RangeDefect`;
   - an unsigned target truncates and never raises: `uint8(300) == 44`,
     `uint16(-1) == 65535`, `byte(300) == 44`;
   - a `char` target checks 0 .. 255: `char(300)`, `char(-1)`,
     `char(-1'i8)` raise.
4. A plain assignment into a range variable checked twice. S8i's parser
   wraps `q = x` in the range conversion, and the walker's #163 R22 site
   check forked the same condition again (canonical form: two checks for
   `q = x` and for `q = R(x)`). A field or seq element store did the same
   at the walker.

- **Runtime.**
  - `isReturn`, empty call stack: the expression lowers through
    `lowerInExpr` (the `result` binding shapes a literal) and each
    continuation from `drainScalarRaiseForks` binds `result` and joins the
    new `WalkCtx.topReturnedPaths`. A raise routes as any other
    (`routeRaise`, so an enclosing handler catches it). A bare `return`
    joins unchanged. The concolic driver appends `topReturnedPaths` to
    the body's surviving paths (the symbolic driver discards both: its
    findings are the raise and label records).
  - `IRType` `itVariant` gains `vNominalId` (from `nominalId` in
    `dsl_typebridge`, emitted by `emitIRType`); `refPointeeTypeId` keys a
    variant pointee by it, so the placeholder and the full variant share
    one sort.
  - `iekConvIntWidth` now also carries an unchecked narrowing
    (`mkConvIntWidth` asserts a range or a width change). The new
    `lowerConvIntTrunc` truncates a BV operand (`truncBV`) and takes an
    Int-sorted one modulo `2^w`. A checked conversion reuses S8i's range
    conversion with the target's own bounds (or 0 .. 255 for `char`). The
    parser's `nnkConv` int-family arm picks checked / truncating / widening
    / reinterpret from the probe table above; `intConvSrcName` reads a
    subrange operand as its base type.
  - `carriesRangeCheck(e, ty)`: `e` is a range conversion whose bounds lie
    inside `ty`'s. The parser's plain-assign `aty` is nil for it, and the
    walker's field-write (`Dw`, both arms) and seq element-write sites skip
    `forkAssignRangeCheck` for it. One check per store.
- **Consumer-visible (for S11's migration note).**
  - New findings: defects raised in a top-level `return` expression
    (`DivByZeroDefect`, `OverflowDefect`, `RangeDefect` into a range
    result, …), and `RangeDefect` from narrowing into a signed or `char`
    target. A `tRaisedExn("X")` search can now return one of these instead
    of `sxUnsat`.
  - A label reachable only through a handler of a raising `return` is now
    found.
  - Programs with narrowing conversions that were `sxUnknown` (the
    recorded decline) now get a verdict; an unsigned narrowing's value is
    the truncation.
  - Searches through an inline `ref <case object>` field that were
    `sxUnknown` (`ekZ3Error`) now get a verdict, including `FieldDefect`
    on a wrong-arm read.
  - Concolic collection: `branchTrace` gains the handler decisions of a
    raising top-level `return`.
  - The walker bump to 158 invalidates every symex cache entry.
- **Different mechanisms, reported and not fixed here.**
  - `finally` does not run on a `return` exit, in a callee or at top level:
    `isReturn` never consults the handler stack's `finally` blocks.
    `proc calleeFin(x: int): int = (try: return x finally:
    symexTarget("cfin"))` called from `proc callsFin(x: int) = discard
    calleeFin(x)` gives a false `sxUnsat` for `tLabel("cfin")`. At top
    level, `try: return x * 2 finally: (if result == 10:
    symexTarget("fin"))` is `sxUnknown` `feGlobalReadUnmodelled`. The
    `result` binding on a returned top-level path has no reader until
    this is fixed.
  - `defer:` is `feUnsupportedStmtKind` (`nnkDefer`): honest, and a
    `return` under a `defer` has the same gap.
  - A named `ref object` case variant (`VB = ref object case …`) still
    declines: `p != nil` (CR-2a, `nnkNilLit`) and `p.a = x` ("unsupported
    nnkAsgn shape").
  - Suspected, not verified: a named alias `VRef = ref VObj` reads variant
    fields through a variant-blind placeholder, so a wrong-arm read through
    it may raise no `FieldDefect`.
  - An inline `ref` to an `itMultiVariant` field keeps the structural /
    nominal sort split (no nominal id there). The deref of a ref to a
    multi-variant is declined anyway.

Pins: `tests/tsymex_rfc0005_s8j_exits.nim`. It covers:
- top-level `return` of a division, a `Natural` result, a branch, a
  caught raise, and a guarded division that never raises;
- the concolic walker on a raising and a returning trace;
- an inline `ref <case object>` field: reachability, aliasing with a
  second param (and its unsat clash), and a wrong-arm `FieldDefect`;
- signed narrowing at 64 -> 8, 32 -> 16, 64 -> 32, same-width unsigned ->
  signed, a caught one, and one of a subrange param;
- unsigned truncation, including a negative operand, a subrange param and
  `byte`;
- `char` from `int`, in range, and from `int8`;
- a single canonical range check for `q = x`, `q = R(x)` and `q += 1`,
  with their verdicts; field and seq element store verdicts;
- the `>= 158` floor.

Each test comment cites the real-Nim probe it relies on.

Re-pinned, each checked against real Nim:
- `r6_b2_intwidth` B2-9 and B2-13 had pinned the round-6 narrowing decline
  (`sxUnknown`, `feUnsupportedExprKind`) for `uint8(x)` and `byte(x)` of an
  `int32`. Nim truncates there (`uint8(300) == 44`), so both are now
  `sxSat` with a witness whose low byte is 42.
- `tot1_totality_corpus`: the §0 row "B2: narrowing int conversion" was a
  decline row; it moves to the capability suite beside the B2 reinterpret,
  pinned `sxSat` with the same low-byte check.
- `phase15_CR2_cachekey` pin (158).

**As landed (S8l, walker 159) — S8j's exit remainder.** S8j reported five
defects outside its design. Every expected behaviour was probed against the
pinned toolchain (Nim 2.2.10); c and cpp are identical except where noted.

1. `finally` did not run on a `return` exit. `isReturn` completed the return
   at once and never consulted the handler stack. Nim runs every enclosing
   `finally` innermost first, with `result` already assigned:
   - a `finally` can read `result` and write it (`result = result + 1` is
     returned);
   - a raise in the `finally` replaces the return;
   - a `return` in the `finally` overrides it;
   - a `return` from an `except` arm, and a bare `return`, run it too.
   The one exception is `try: raise newException(ValueError, "a") finally:
   return 7`. Here c re-raises the `ValueError` and cpp returns 7.
2. `defer:` was `feUnsupportedStmtKind` and its body was dropped. Nim lowers
   `defer: D` to a `try: <rest of block> finally: D`. A later defer runs
   first, and a `defer: result += 100` changes the returned value.
3. A named `ref object` case variant (`VB = ref object case kind: …`) was
   value-modelled. `p != nil` was a `weInternalWalkerFault`, construction
   was a recorded decline, and `new(VB)` had no zero cell.
4. A `VRef = ref VObj` alias was variant-blind in the same way. A field
   typed by a `ref Obj` alias (`v: VRef`, and the plain `p: PRef` with
   `PRef = ref PObj`) was an `ekZ3Error` sort error. Its placeholder keyed
   the `Ref_<id>` sort on the alias symbol, while every other position keyed
   it on the object.
5. An inline `ref` to a multi-variant was `heRefVariantUnsupported` on a
   deref or write. As a field it was a Z3 sort error, because
   `itMultiVariant` had no nominal id.

Also found and fixed: no discriminator write through a ref was checked. Real
Nim raises `FieldDefect` when a discriminator assignment through a ref
changes the branch, even on a fresh `new` cell. A same-branch move (between
two tags of one `of` group) keeps the branch's fields. A constructor's
discriminator write is not checked. The heap arm had stored the new tag
silently.

- **Runtime.**
  - `CallFrame` gains `retTy`, `pendingReturn` and `raisedFinally`.
  - `isReturn` binds `result` on the returning path and calls `exitReturn`.
  - `exitReturn` hands the path to the deepest `HandlerFrame` of the frame
    that has a `finallyBlock` (`pendingReturn`), or else calls
    `completeReturn`.
  - `completeReturn` does what `isReturn` did before:
    - at top level, it joins `topReturnedPaths`;
    - in a callee, it binds the frame's `retSym` to `result`, or to the
      return type's zero value when a value-returning callee never assigned
      it. Where the return type has no modelled zero value (a variant),
      `retSym` stays free and the site records `feUnsupportedOpHavoc`,
      S6b's fresh class, the same as the `isCall` arm's untouched-result
      twin. This is a new twelfth site in S6b's audited list.
  - `isTry` claims the returns recorded at its depth, walks the `finally` on
    each, and sends the fall-through outward through `exitReturn`.
  - While a `finally` runs on a raised exit (`raisedFinally > 0`), a
    `return` halts through the new `dcOmitted` kind `eeFinallyReturnOnRaise`
    (`discard w.degrade`). The walker cannot know which backend will replay
    the witness.
  - The top-level `result` binding now has a reader. A top-level `finally`
    reading `result` was `feGlobalReadUnmodelled`.
  - The concolic driver records the `finally`'s decisions on a top-level
    return.
  - `dsl_parser.parseDeferList` performs the `defer` lowering above.
  - `dsl_typebridge` gives both the direct `ref object` form and the
    sym-indirection alias `{itTuple, itVariant, itMultiVariant}` the ref
    wrap. `ctorIsRefAliasedVariant` and its decline are deleted.
    `classifyFieldType` keys a named ref field's placeholder on the pointee
    symbol. This retires ADR-0022 sub-decision #1 (named-ref variants
    value-modelled).
  - The ref-constructor arm writes each axis's discriminator with the new
    `isDerefWrite.dwInit` (it appears in the canonical form as `;init`),
    then the plain fields, then the arm fields. A `bool` discriminator's
    folded int literal becomes a bool literal. Before, it was stored
    BV-into-Bool, and Z3 swallowed that into a silent `sxUnsat`.
  - `itMultiVariant` gains `mvNominalId` (the `Ref_<id>` key) and `itVariant`
    gains `vIsAxisView`. `runtime_heap.mvAxisView` models one axis of a
    multi-variant as a single-axis variant whose discriminator heap has its
    own key, `<id>__@disc__<discName>` (`variantDiscHeapKey`).
  - The multi-variant deref and write arms re-dispatch through the axis
    view that owns the field (`mvAxisOfField`) instead of declining.
    `new(MV)` zero-initialises every axis.
  - The heap discriminator write (not `dwInit`) forks `FieldDefect` on
    `not sameBranchSymCond(old, new)`. On a multi-tag `of` group it
    re-stores each branch field over the old tag's arrays.
  - The witness `renderCell` walks every axis of a multi-variant cell.
    `refWitnessTypeNode` returns the named ref symbol for a variant pointee,
    so the witness tuple is typed `VRef`, not `VObj`.
- **Consumer-visible (for S11's migration note).**
  - New findings:
    - labels and raises inside a `finally` reached by a `return`;
    - a `finally`'s raise replacing a return;
    - `defer` bodies;
    - `FieldDefect` from a branch-changing discriminator write through any
      ref;
    - wrong-arm `FieldDefect` through a named ref variant, a `ref` alias, or
      a ref to a multi-variant.
  - Returned values change where a `finally` or `defer` writes `result`.
  - Programs that were `sxUnknown` now get verdicts:
    - `feUnsupportedStmtKind` for `defer`;
    - `weInternalWalkerFault` for a named ref variant's `p != nil`;
    - the construction decline;
    - `heRefVariantUnsupported`;
    - `ekZ3Error` for alias-typed and multi-variant ref fields.
  - A new `sxUnknown`: `eeFinallyReturnOnRaise`.
  - `heRefVariantUnsupported` and the `heapArmDegrade` funnel's F4 arm have
    no live producer now. The enum member stays for cache and consumer
    compatibility.
  - Witnesses for a named ref variant param are typed by the named ref.
  - The walker bump to 159 invalidates every symex cache entry.
- **Different mechanisms, reported and not fixed here.**
  - `break` / `continue` out of a `try: … finally:` inside a loop does not
    run the `finally`. `for i in 0..1: (try: (if i < 5: continue) finally:
    echo "loopfin ", i)` prints `loopfin 0`, `loopfin 1` in Nim. The walker
    walks the `continue` past the `finally`, so a label in it is a false
    `sxUnsat`.
  - A ref local reassigned from a param, `var q: ref Obj; if p != nil:
    q = p; if q != nil: …`, and the cast form `let q = cast[ref Obj](p); if
    q != nil: …`, are `weInternalWalkerFault`. The cause is an
    `AssertionDefect` in `eqBV`'s `a.kind == b.kind` (`runtime.nim:4608`).
    This is pre-existing (`runtime.nim:4603` at 3500d0d).
  - An uninitialised `var p: ref T` local is `feUnsupportedStmtKind`, so the
    tests use `new(T)`.
  - A closure's bare `return` has no `retTy`, so a closure that never
    assigns `result` still takes the free-`retSym` path, not the zero
    default.
  - A Z3 store whose sort mismatches (a BV into a Bool array) surfaced as a
    silent `sxUnsat` with no error recorded. That is how the bool
    discriminator constructor failed before the fix above. No other
    producer is known, but nothing checks the sort at the store.
  - The `heUnresolvedRef` sites are reachable only on a ref that was already
    degraded upstream.

Pins: `tests/tsymex_rfc0005_s8l_exits.nim`. It covers:
- a callee's `finally` on a return, which reads and writes `result`;
- a raise in a `finally`, nested `finally`s, a `return` in a `finally`, and
  a return from an `except` arm (with a raise from an `except` arm alongside);
- a bare `return`, a bare `return` before `result` is assigned (the zero
  value; and, with no zero value, `feUnsupportedOpHavoc` licensing
  `sxUnsat`), and a top-level `finally` on both walkers;
- the `eeFinallyReturnOnRaise` decline;
- `defer`: return, raise, a write to `result`, two defers in order, and a
  trailing defer;
- a named ref variant: nil, arm read and write, wrong arm, construction
  (including a `bool` discriminator), `new` zero, aliasing, a
  branch-changing discriminator write, a same-branch one, and a multi-tag
  carry;
- `VRef` alias reads, construction, and alias-typed fields;
- an inline `ref` to a multi-variant: reads on both axes, wrong arm on
  each, write, a discriminator change, a field, a named alias, `new`,
  construction, and aliasing;
- the `>= 159` floor.

Every `sxSat` pin replays its witness on the real code.

Re-pinned, each checked against real Nim:
- `phase15_CR2_cachekey` pin (159).
- `rfc0005_s1_lattice`: `eeFinallyReturnOnRaise` joins the reclassified set
  (`dcOmitted`).
- `rfc0005_s6b_ops`: the structural count of `feUnsupportedOpHavoc` sites
  goes from 11 to 12 for the `completeReturn` zero-default fallback, after
  that site was re-audited. The composite-return site moved from `isReturn`
  into `completeReturn` without change.
- `h_verification`: the named-ref multi-variant discriminator read had
  pinned the value-model decline. It is now `sxSat`.
- `p2b_refobjconstr_expr` P2b-13 and `r6_a1_variantlit` A1-7 had pinned
  the ref-variant construction decline (`ctorIsRefAliasedVariant`). Both
  are now `sxSat` with witness 3, which reproduces.
- `r6_heap_raise_totality` N46-followup-2: the multi-variant ref read and
  write had pinned `heRefVariantUnsupported`. Both are now `sxSat`.
- `rfc0005_s4_alloc` `s4MultiVariantDead`: a wrong-arm read through a ref
  to a multi-variant is `sxRaised` `FieldDefect`, as Nim raises. It was
  `heRefVariantUnsupported`.
- `rfc0005_s3_monotonicity` F4 used `heRefVariantUnsupported` as its
  live F4 producer. F4-before now asserts the kind is absent. 2a is `sxSat`
  (witness `kindA == s3f4KindA1`, `y == 42`, which reproduces). 2b is
  `sxRaised` `FieldDefect` with no `sevError` kinds.

**As landed (S8m, walker 160) — S8l's remainder.** S8l reported six
defects outside its design. Every expected behaviour was probed against the
pinned toolchain (Nim 2.2.10); c and cpp are identical except where noted.

1. `break` / `continue` did not run a `finally` they left, and the parser
   flattened every `block` into its body and emitted a bare `break` /
   `continue` for each source one. The walker applied it to the innermost
   `isWhile`, so:
   - a `continue` past a `try: … finally:` skipped the `finally` (a label
     in it was a false `sxUnsat`);
   - `break outer` out of two nested loops left only the inner one (a false
     `sxSat` on the code after it);
   - a `block`'s `break` left the enclosing loop, and a `break` out of a
     top-level `block` or an unrolled array loop halted
     (`weBreakOutsideLoop`);
   - a `continue` in a `for` loop skipped the desugared increment and
     replayed the same iteration up to the unroll bound.
   Nim leaves the innermost `block` or loop (`break`), the named block
   (`break L`), or goes to the innermost loop's next iteration
   (`continue`), running every `finally` in between, innermost first. One
   backend divergence: a `break` / `continue` leaving a `finally` that runs
   on a raised exit. `try: raise … finally: break` re-raises under c and
   swallows under cpp; the `continue` form overflows the call depth under c.
2. A Z3 term built with mismatched sorts (a BV stored into a Bool array)
   raised `Z3Error` from `checkErr` inside a `walkBlock` frame. On c the
   goto-based exception was lost and the run ended a silent `sxUnsat []`; on
   cpp it reached the boundary as `ekZ3Error`. Reproduced at a58dc08 by
   disabling S8l's bool-discriminator fold: `BoolV(on: true, t: x)` was c
   `sxUnsat []`, cpp `sxUnknown [ekZ3Error: … domain sort (_ BitVec 64) and
   parameter sort Bool do not match]`.
3. A ref local assigned from a param (`var q: ref Obj; if p != nil: q = p`)
   and a same-type cast (`let q = cast[ref Obj](p)`) were
   `weInternalWalkerFault` (`eqBV`'s `a.kind == b.kind` assert,
   `runtime.nim:4608`). The cast reached `parseExpr`'s catch-all, whose int
   dummy met a ref in `q != nil`; the alias form `q = p` was
   `feUnsupportedStmtKind`.
4. An uninitialised `var p: ref T` local was `feUnsupportedStmtKind`, then
   a walker fault on its first comparison: `zeroValueForType` returned nil
   (no encoding) for `itRef` / `itPtr`.
5. A closure's bare `return` (and its fall-through) with `result` never
   assigned took the free-`retSym` path, because the closure `CallFrame` had
   no `retTy`. `f(-1) == 7` for `f = proc(x: int): int = (if x < 0: return;
   result = 7)`-shaped closures was a false `sxUnsat`, and a dead label
   behind the zero was a false `sxSat`.
6. `heRefVariantUnsupported` had no live producer after S8l.

- **Runtime.**
  - `isBlock` gains `blkLabel` and `isBreak` gains `brkLabel`
    (`mkLabelledBlock`, `mkBreak(label)`; both canonicalised). A labelled
    `isBlock` pushes a `LoopFrame` carrying the label; a labelled `break`
    resumes after it, an unlabelled one leaves the innermost `isWhile`.
  - The parser keeps a lexical `jumpTargets` stack
    (`ProcScopedCollectors`) and resolves each source jump
    (`resolveBreak` / `resolveContinue`) to the construct Nim leaves. A
    `for` loop's body is a labelled block its `continue` leaves, so the
    increment still runs; an unrolled loop (array, constant string) is
    wrapped in a block its `break` leaves. A label is minted only when a
    jump names it, so the IR of every program without such a jump is
    unchanged.
  - `LoopFrame` records the handler depth it was entered at (`hsDepth`).
    `exitJump` hands a jump to the deepest `finally` between it and its
    target (`pendingJump`), exactly as S8l's `exitReturn` does for a
    return; `isTry` walks the `finally` on each claimed jump and sends it
    outward through `exitJump`. `routeRaise` cuts the loop stack to the
    try's depth while a handler runs (`HandlerFrame.loopLen`).
  - A jump leaving a `finally` that runs on a raised exit halts through the
    new `dcOmitted` kind `eeFinallyJumpOnRaise` (`discard w.degrade`), the
    jump twin of `eeFinallyReturnOnRaise`. `raisedFinally` became
    `raisedFinallyLoops`, which records the loop depth so a jump that stays
    inside the `finally` is not caught.
  - Every Z3 `store` / `select` / `ite` / `eq` the walker builds goes
    through `checkedStore` / `checkedSelect` / `checkedIte` / `checkedEq`
    (17 sites in `runtime.nim` and `runtime_heap.nim`). A sort mismatch
    records `weInternalWalkerFault` through `lowerDegrade` (path taint
    `{scSpurious, scIncomplete}`) and a fresh term of the expected sort
    stands in. No exception is raised, so no backend can lose it. A
    source audit pins zero unchecked raw calls.
  - Backstop: `resetSymexRunState` installs a counting Z3 error handler. If
    any Z3 API error was raised during the run and no `ekZ3*` error
    reached the verdict (or the status is not `sxUnknown`), `runSymex`
    returns `sxUnknown` with `ekZ3Error`. No Z3 error can end in a verdict.
  - `parseExpr` gains an `nnkCast` arm: a cast to the ref / ptr type the
    operand already has is the identity (same address, same `Ref_<id>`
    sort). Any other cast keeps the catch-all's `feUnsupportedExprKind`
    decline, message for message, now with a kind-correct dummy. (A first
    cut prefixed the site to the message; S9's twin-decline pin caught it,
    since that dedup keys on message and anchor.)
  - `zeroValueForType` returns `mkNil` for `itRef` / `itPtr`. This models
    the uninitialised ref local and makes every catch-all dummy of a ref
    type a nil ref, not an int.
  - A comparison of a ref against a non-ref operand (a value the model did
    not resolve to an address) records `heUnresolvedRef` through
    `degradeAlloc` (`refMixedCmpDecline`) instead of crashing `eqBV`.
  - The closure `CallFrame` carries `retTy: cb.retTy`, so S8l's
    `completeReturn` binds the zero value (or records
    `feUnsupportedOpHavoc` where the return type has none).
    `applyClosureGround` checks a returned path's taint before it skips an
    empty path condition, so the unconditional bare return's havoc path
    carries its taint to the caller.
  - `heRefVariantUnsupported` is retired: the enum member, its `classOf`
    arm, `SymexRefVariantUnsupportedError` and its `runSymexCaught` arm are
    deleted. Its six unreachable carriers in `runtime_heap.nim` raise
    `SymexClassifiedDegradeError(kind: weInternalWalkerFault)`.
- **Consumer-visible (for S11's migration note).**
  - `heRefVariantUnsupported` is gone from `SymexErrorKind`. A consumer
    matching on it no longer compiles.
  - New `SymexErrorKind`: `eeFinallyJumpOnRaise` (`sxUnknown`).
  - New findings: labels and raises in a `finally` reached by `break` /
    `continue`; code after a labelled `break` out of nested loops; code
    after a `block`'s `break`; each `for` iteration after a `continue`.
  - Verdicts change from false to true:
    - a label in a `finally` left by `continue` (was `sxUnsat`);
    - code only reachable after an inner loop's `break outer` (was `sxSat`);
    - a closure whose bare return yields the zero value (was `sxUnsat` /
      `sxSat` the wrong way round);
    - an ill-sorted Z3 term is `sxUnknown` + `weInternalWalkerFault` (was a
      silent c-only `sxUnsat`).
  - Programs that were `sxUnknown` now get verdicts: a top-level block's
    `break` (`weBreakOutsideLoop`), a ref local assigned or same-type cast
    from a param (`weInternalWalkerFault`), an uninitialised ref local
    (`feUnsupportedStmtKind`).
  - A layout-changing `cast` keeps its `feUnsupportedExprKind` decline; a
    ref-typed one no longer adds a walker fault at its first comparison.
  - The walker bump to 160 invalidates every symex cache entry.
- **Different mechanisms, reported and not fixed here.**
  - A callee that reads `result` before any write (`proc rr(x: int): int =
    result += 100`) is `feGlobalReadUnmodelled` on its caller. Nim
    zero-initialises `result`. Pre-existing at a58dc08. The S8m pin for a
    `break` cancelling a return assigns `result = 0` first for this reason.
  - A variant-typed closure result is substituted
    (`seUnsupportedCompoundSortLeaf` / `feUnsupportedOp`) on the caller.
    The item-5 havoc fires as well; the verdict stays `sxUnknown`.
  - A real nil write (`p[].x = 1` with `p == nil`) SIGSEGVs in a default
    debug build on the pinned toolchain; the walker models it, as R5 did, as
    `sxRaised NilAccessDefect`. A witness replay oracle cannot catch it
    with `expect NilAccessDefect`.
  - The Linux-hanging r6 suites `b7r_bytescan`, `b7r2_pathscope` and
    `n10_coverage_matrix` contain unlabelled `break`s in `while` loops. The
    lowering of those is unchanged (a plain `mkBreak()` still leaves the
    innermost `isWhile`), but they run only on Windows CI.

Pins: `tests/tsymex_rfc0005_s8m_exits.nim`. It covers:
- `continue` and `break` through a `finally` (loop, nested `try`, `defer`,
  `for` and `while`), a labelled block break through a `finally`, a nested
  block break, `break outer` from nested loops, a `break` from an `except`
  arm, a `break` in a `finally` cancelling a return, a return through a
  loop's `finally`, and `break` / `continue` in an unrolled array loop;
- `eeFinallyJumpOnRaise`;
- an ill-sorted store as `sxUnknown` + `weInternalWalkerFault` on the live
  and dead label, the error-handler backstop, and the zero-unchecked-call
  source audit;
- ref assignment, aliasing, same-type cast, and a different-pointee cast;
- an uninitialised ref local: nil, a nil write (`sxRaised
  NilAccessDefect`), and `new` after it;
- a closure's bare return: zero value, dead label, and the variant havoc;
- the `>= 160` floor.

Every `sxSat` pin checks its witness value against an oracle run of the
real code; the ones over non-constant witnesses also replay it. Loop pins
run at `maxLoopUnwind: 3` and accept a dead label behind a loop as
`sxUnsat` or `beBudgetExhausted`-only `sxUnknown` (k-unroll has no
feasibility pruning, so the unroll bound is structural).

Re-pinned, each checked against real Nim:
- `phase15_CR2_cachekey` pin (160).
- `rfc0005_s1_lattice`: `eeFinallyJumpOnRaise` joins the reclassified set
  (`dcOmitted`).
- `rfc0005_s1b_kinds`: the surface `break s1bBlk` of a `block` had pinned
  `weBreakOutsideLoop`. It is now `sxSat`, as in Nim. The kind is still
  pinned at the IR level (a bare `mkBreak()` outside any loop).
- `h_verification`, `rfc0005_s3_monotonicity` and `rfc0005_s4_alloc`:
  every `heRefVariantUnsupported` check retargets `weInternalWalkerFault`
  (the retired kind's carriers). S3's F4 `classOf` test becomes a
  retirement test that the member is gone. S4 drops the member from the
  `dcNoAnswer` list.

**As landed (S8k, walker 161) — termination and resources.** Three ways a
run could fail to finish or take its host down. Every Z3 figure below was
measured on the pinned Z3 (reports 5.1.0) in the `nelli-dev` container;
every Nim behaviour was probed on Nim 2.2.10, debug build, c and cpp
identical.

1. **Long-string queries were not bounded.** `findColon(s, 0) > 1000` (a
   `while i < s.len: if s[i] == ':'` scan) never returned, whatever
   `queryRLimit` said. Why `rlimit` did not bound it: Z3's sequence solver
   searches string lengths upward, and past ~100 elements each step grows
   super-linearly (`len(s) > N` alone: N=100 1.4 s; N=200 19 s, 1.6 GB;
   N=300 102 s, 3.4 GB). Past ~250 elements single steps run for minutes
   without polling the resource counter. At N=300 a 10 s wall-clock
   `timeout` returned after 102 s, and `rlimit = 300000` also returned at
   101 s. `len(s) > 1000` never returned. Neither bound can stop a step
   that never checks it, so neither is the fix. Z3 parameters that do not
   help: `model=false`, `smt.seq.max_unfolding` / `min_unfolding`,
   `smt.seq.split_w_len`, and `smt.string_solver=z3str3`, which answers
   `unknown` at once for everything.
2. **The k-unroll forked both arms of every iteration.** A loop with a
   concrete trip count kept its impossible "guard still true" continuation
   to the unroll bound. So a dead label after `var i = 0; while i < 3: inc
   i` was `sxUnknown [beBudgetExhausted]`, and nested loops multiplied.
3. **Replay could execute a SIGSEGV.** A real nil dereference is a SIGSEGV
   in the default build: `try: p[].x = 1 except NilAccessDefect: …`
   prints "SIGSEGV: Illegal storage access. (Attempt to read from nil?)"
   and exits 139, for a read too, with or without `--nilchecks:on`. The
   walker models the nil edge as `NilAccessDefect` (a finding under
   `tRaisedExn("NilAccessDefect")`, or a handler-caught raise). S10 replays
   an `scSpurious` candidate against the real SUT. A candidate whose path
   crossed the nil edge killed the test process: `nilWriteOnNaN(p, f)` (`let
   k = int(f); if f != f: p[].x = k`), where the NaN edge of `int(f)` is a
   `feConvFloatToIntUndefined` fresh symbol, died with that SIGSEGV under
   `symexFind(…, tRaisedExn("NilAccessDefect"))`.

- **Runtime.**
  - Every query the walker issues (`trySolve` and the loop check below,
    both through the new shared `pathRoots` / `checkCapped`) caps each
    uninterpreted seq-sorted term at `ResourceBudget.maxSeqLen` elements
    (bytes for a `string`; default 128; `0` = unlimited). The capped terms
    are an input, a fresh return, a closure / UF result, or a heap
    `select`. Every other seq term is built from these leaves by
    interpreted operations, so capping the leaves bounds the search.
    First, each byte test `int2bv8(str.to_code(str.at(s, i))) == n` over
    an input string `s` whose byte-domain constraint is in the query
    becomes `str.at(s, i) == "\xNN"` (or `""` too, for `n = 255`): the
    same predicate under that constraint, and far cheaper (below).
    `checkCapped` then decides the query in up to four fresh one-query
    solvers:
    1. one-shot, with every `len(t) <= maxSeqLen` asserted. A model is a
       model of the uncapped query.
    2. after (1) was UNSAT, or (1) and (4) both ran out of budget:
       one-shot with no sequence theory registered
       (`smt.string_solver = none`). Every string operation Z3's rewriter
       does not evaluate is uninterpreted, so the models are a superset
       of the real ones and an UNSAT is the query's own. It has no string
       search to run into.
    3. if (1) was UNSAT and (2) was not: the caps behind one assumption
       literal, checked incrementally, and the unsat core read. No
       literal in the core: the query's own UNSAT. The literal in the
       core, or `unknown`: `zsUnknown`, recorded as `beSolverUndef`
       naming `maxSeqLen`, never a verdict.
    4. the uncapped one-shot query (the pre-S8k one), only when (1) ran
       out of budget, or in place of (3) for a query holding a
       `seq.last_indexof`.
    (1) and (4), the model search, run under half of the query's budget
    each, so a query that finds no model spends at most that budget
    searching; (2) and (3) run under all of it.
    Why so much: each simpler design broke a pinned suite on the first
    gate or on the way to the second.
    - Z3's incremental core (any `check-sat-assuming` or `push`, even
      `(check-sat-assuming (true))`) evaluates `seq.last_indexof` wrongly
      over a term fixed to a constant: with `s == "abc"` it takes
      `seq.last_indexof(s, "bc")` to be -4294967292, not 1. That made
      `phase16_m3_rfind` a false `sxUnsat`. So every model comes from a
      one-shot check, and a `last_indexof` query never trusts (3).
    - The incremental core is also far slower on bit-vector-heavy
      queries: `r14_case2_degrade`'s label query, seconds one-shot, ran
      out of 20M units, so its IndexDefect raise was reported first.
    - Z3's unsat cores are not minimal. `r6_r3_svint_overflow` R3-5b
      bounds `s.len <= 1000` itself, and the overflow it asks about is
      refuted by arithmetic alone, but the core named the cap (which
      bounds the length as well). (2) decides it.
    - `seq.last_indexof` has no decl kind of its own in the C API: it
      reports Z3's catch-all internal ordinal, shared with `ubv_to_int`
      among others. Matching on the kind sent every string index query
      down (4) uncapped, and `farColon` hung again. It is matched by
      name.
    - Byte tests: in their lowered form, `s[0..2] == "aaa"` needs 41M
      units (103 s) and the `parseInt("-x")` raise query of
      `s7_closure` 23.6M; in character form, 3.8k and 12k. The other
      exact rewrite, `x mod 256 == n`, fixed the first and made the
      second 110M. The character form is used only where the query
      itself pins the string to bytes.
    - Z3's cost on a string query is not a function of the query alone.
      The lowered `s[0..2] == "aaa"` label query was SAT at once as a
      program's only search and ran past 20M units as the last search of
      `r1b_shortcircuit_oob`. Running (2) before (4) pushed the
      `parseInt` raise query across 20M. A `seq[byte]` scan query of
      `r6_b7r_bytescan` that is SAT in 2.1M units from its own SMT-LIB
      text ran past 20M in the walker even when tried in a fresh Z3
      context (Z3 keeps process-wide state), so fresh contexts were tried
      and dropped. The budget is a bound, not a promise: the character
      form keeps the common byte tests far below it, and a query near it
      can decline in one process and not in another.
    - With (1) and (4) each under the whole budget, a query that found
      no model could spend it twice, then (2) on top. The
      four-iteration pair-loop query of `r6_n36_raise_degrade`'s
      no-block companion, SAT in 3.9 s from its own text with all ten
      caps asserted, ran 100 s to 20M units in the walker before (4)
      found the model in 23 s, and the file went from passing to past
      the 900 s gate timeout (15.5 min standalone). Half each: 2.6 min.
    Residual risk: (4) runs uncapped under half the budget, which a long
    enough string search does not poll. It is reached only after the
    capped query ran out of budget, or for a `seq.last_indexof` query
    whose capped form is UNSAT.
  - Under the cap the sequence solver does poll `rlimit`, but it can
    spend it at 40–55k units/s (against ~1M/s for arithmetic). With the
    byte test in its lowered form, `s.len == 20 and s[19] == 'q'` needed
    2.3M units (~60 s) and the same at length 100 34M (~10 min); the
    character form decides both at once, but nothing stopped a within-cap
    query that needed more under the default unbounded `queryRLimit`. So a query
    that mentions a string or seq also runs under
    `ResourceBudget.seqQueryRLimit` (default 20M, the
    `defaultConcreteBranchRLimit` the tainted target-hit solve already
    uses) whenever that is smaller than its own bound. `maxSeqLen = 0`
    turns off both the cap and this bound.
  - **No wall-clock timeout is used.** Both bounds are step counts, so a
    query they cut off is the same `beSolverUndef` on every machine, and
    the verdict cache stays deterministic. Every `beSolverUndef` message
    now ends with its reason: the cap text, or `Z3: <reason_unknown>`,
    with the `seqQueryRLimit` value when that bound applied.
  - The `wmExplore` `isWhile` k-unroll walks an arm only if
    `loopArmInfeasible` cannot refute it on the path. A guard that
    simplifies to a literal never reaches the solver. Otherwise the check
    is the path's full `pathRoots` query (through `checkCapped`) plus the arm, under
    `loopPruneRLimit` (250k, or a smaller caller `queryRLimit`). An
    `unknown` never prunes. After the last unrolled body, a surviving path
    faces the guard once more, as the real loop does. Where the guard is
    provably false there, the path leaves clean through the exit. Only a
    path whose guard may still hold is the exhausted survivor, and it
    still records `beBudgetExhausted` / `beBudgetExhaustedAssumedBound`
    exactly as before. Pruning is sound: a pruned arm's every later query
    would carry the same UNSAT constraints. What it loses are declines an
    infeasible arm would have recorded.
  - `Path.nilDeref` is set on `nilDerefFork`'s nil edge (`runtime_heap.nim`).
    `forkPath` carries it, and `forkPathMerged` ORs both sides, because a
    closure descent starts from a fresh root. `RawResult` /
    `SatCandidate.nilDerefOnPath` carries it to the finding (both the
    label hit and `routeRaise`'s raise). `emitReplayWitness` returns
    `roInconclusive` without running `fn` when it is set.
    `replayInScope(tRaisedExn("NilAccessDefect"))` is now `false`, for
    `stkNilAccess`'s reason.
- **Consumer-visible (for S11's migration note).**
  - Two new `ResourceBudget` fields: `maxSeqLen` (default 128) and
    `seqQueryRLimit` (default 20M). Each enters the settings cache key only
    when it is not the default (`;msl=` / `;sqr=`), so default keys are
    unchanged apart from the walker version.
  - Verdicts change:
    - A finding whose witness needs a string or seq longer than 128
      elements is `sxUnknown` + `beSolverUndef` naming `maxSeqLen`. It was
      `sxSat` when Z3 finished, and a hang when it did not. Raise
      `maxSeqLen` to search further. The `>1000`-byte RangeDefect in
      `163rev_intoffset_range` is the pinned instance.
    - A within-cap string query that needs more than 20M units is
      `sxUnknown` + `beSolverUndef` (was a slow `sxSat` or a hang).
      Byte equalities with a constant are decided in character form, so
      queries built from them (`s[i] == 'a'`) are much faster and find
      their witness where they used to exhaust a budget.
    - Some UNSATs arrive where a decline did: `r6_n21_pairloop_member`
      N21-1/2/3-unsat and `r6_r5_pairloop_counter` R5-2 (below).
    - A dead label after a concretely bounded loop is `sxUnsat`
      (was `sxUnknown [beBudgetExhausted]`).
    - A `symexAssume` that really bounds a loop within `maxLoopUnwind`
      records no exhaustion kind (was `beBudgetExhaustedAssumedBound`).
    - A replay candidate whose path went through a nil dereference, and
      any `tRaisedExn("NilAccessDefect")` candidate, stays `sxUnknown`
      (`roInconclusive`) instead of running the SUT. A clean-path
      `sxRaised NilAccessDefect` is unchanged: it was never replayed.
  - `beSolverUndef` messages carry the reason.
    `beBudgetExhaustedAssumedBound`'s message no longer says the k-unroll
    cannot check the bound.
  - New exported `symexLoopIterations` (a per-thread counter of loop
    bodies walked, like `symexZ3CallCount`), `loopPruneRLimit` and
    `defaultLoopPruneRLimit`.
  - The walker bump to 161 invalidates every symex cache entry.
- **Different mechanisms, reported and not fixed here.**
  - Byte tests other than an equality with a constant stay in the lowered
    `int2bv8(str.to_code(str.at(s, i)))` form, which Z3 decides slowly
    next to the byte-domain constraint `str.in_re s (re.* (re.range
    "\u{0}" "\u{ff}"))` on every string input (each cheap alone). That
    covers `s[i] == s[j]` and a byte compared with a symbolic value.
    Ordering comparisons on `s[i]` are already declined
    (`seUnsupportedStringOp`, CR-17). A lowering that produced the
    character or integer-code form directly would be the general fix.
  - The string index is lowered as `ite(bvslt c 0, ubv_to_int c - 2^64,
    ubv_to_int c)` even for a constant `c`, and is not folded before it
    reaches Z3.
  - The concolic solves (`concreteBranchOutcome`, `concretelyInfeasible`,
    `runConcolicCollectImpl`'s `pcSatByConcreteInputs` check, the G2 flip
    solve) do not go through `checkCapped` and are not capped. The first
    two have concrete pins (lengths fixed by the draws) and
    `concreteBranchRLimit`. The flip solve has a caller `timeoutMs` plus
    `rlimit`. The `pcSatByConcreteInputs` soundness check has no bound at
    all; its lengths are pinned by the draws.
  - Windows risk to watch: `tsymex_r6_b7r_bytescan` and
    `tsymex_r6_b7r2_pathscope` pass on the symex-mingw leg and do not
    finish on Linux. If a query of theirs needs more than 20M units on
    the Windows Z3 build too, it turns `sxUnknown` there. That would be
    the same bound doing its job, not a new defect, but it would be a red
    on that leg.

**Linux blind spot (the six r6 hangers, run at 900 s under `dt-bounded`).**
- `b1_stringbacked`, `b3_scanpair` and `n10_coverage_matrix` now terminate
  and pass on c and cpp. N10 needed one re-pin (below).
- `nulwitness` now terminates and passes on c and cpp. With the capped
  query alone its NW-5 (nine byte equalities on a 9-byte string) ended
  `sxUnknown [beSolverUndef … seqQueryRLimit = 20000000]`; the character
  form decides it.
- These four leave `scripts/sweep.sh`'s skip list.
- `b7r2_pathscope` still runs past 900 s on c and cpp; B7r2-1a, which
  ended `sxUnknown` before, now passes before the kill.
- `b7r_bytescan` ran to the end in 570 s at the first S8k commit (failing
  only B7R-6). With the final code it runs past 900 s on c. One of its
  `seq[byte]` scan queries is SAT in 2.1M units from its own SMT-LIB text
  but ran past 20M in the walker (the process-dependence above).
- These two stay skipped.
Pins: `tests/tsymex_rfc0005_s8k_bounds.nim`.
- **(1)** The far-colon label is `sxUnknown` with only the `maxSeqLen`
  `beSolverUndef` (RED: killed at 300 s by `dt-bounded`). A length
  contradiction stays `sxUnsat` under the cap. A 100-byte witness is
  found. Past the cap: a 130-byte witness and a bare 130-byte length are
  declined, not `sxUnsat`. `maxSeqLen: 160` finds the 130-byte witness,
  and `s[129] == 'q'` on it in its character form (about 5 s; RED: over
  300 s unbounded in the lowered form). A small `seqQueryRLimit` declines
  that query with the bound named. Both fields key the cache only when not the default.
- **(2)** A dead label after `while i < 3` is `sxUnsat` (RED: `sxUnknown`),
  and the live one is still `sxSat`. A 4×4 nested loop is `sxUnsat` with
  `symexLoopIterations == 20` body walks (37 queries). With the
  feasibility checks switched off and nothing else changed, it measured
  9330 walks, 34211 queries and `sxUnknown [beBudgetExhausted]`. A
  symbolic trip count still records `beBudgetExhausted`.
- **(3)** `nilWriteOnNaN` under `tRaisedExn("NilAccessDefect")` and
  `nilWriteCaught` (the nil write inside `try … except NilAccessDefect`
  around a label) are `sxUnknown` with no replay refutation, and the
  process survives. RED: the test binary died with SIGSEGV. Plus the
  `replayInScope` table.
- The `>= 161` floor.

Re-pinned, each checked against real Nim:
- `phase15_CR2_cachekey` pin (161).
- `163rev_intoffset_range`: its three searches run with range checks on
  again (S8i had turned them off because the query never returned). Each
  is `sxUnknown` with only the `maxSeqLen` decline. That is honest: the
  RangeDefect is real (the oracles raise it) but needs a 1001-byte string.
  The range-checks-off searches stay as the `sxUnsat` W8 placeholder pin.
- `configdefaults`: `ResourceBudget` has 14 fields; the full-override
  merge and the partial-literal test cover the two new ones.
- `r6_n20_boundedloop`: `symexAssume(n >= 0 and n < 3)` now records no
  exhaustion kind. The loop runs at most twice in Nim; the old pin
  recorded the unconditional fork. The magnitude-useless assume still
  pins `beBudgetExhaustedAssumedBound`.
- `r6_n10_coverage_matrix` N10d-5-decline: `sxUnsat`, the verdict its
  own comment said was expected (`s.len == 0` refutes the fallback loop's
  guard).
- `r6_n21_pairloop_member` N21-1-unsat, N21-2-unsat and N21-3-unsat, and
  `r6_r5_pairloop_counter` R5-2: `sxUnsat`, the verdicts their comments
  said the pre-S8k k-unroll could not deliver (each pinned `sxUnknown` as
  an honest decline). Each literal's own replay test shows Nim agrees:
  N21-1's literal always raises, so "done" is unreachable; N21-2's and
  N21-3's never raise; R5-2's loop always ends with `i == 6`, so "stale" is unreachable.

**As landed (S8n, walker 162) — the precision remainder.** Four places the
walker, or the witness bridge, gave up on code whose behaviour is fully
determined. S8i, S8h and S8m reported them. Every expected value was probed
against the pinned toolchain (Nim 2.2.10, debug build) by an oracle test that
runs the SUT itself; c and cpp are identical.

1. A concolic `if` on a closure call that returns normally stayed
   ambiguous. The RFC's S8i note says the closure's ground axioms are
   "guarded by the whole caller pc". They are not: they are guarded by the
   body's own branch conditions (the descent starts from an empty pc). The
   real cause is simpler. The axioms live in the run-wide
   `currentClosureCallAxioms` pool, which `trySolve` asserts through
   `pathRoots`, and `concreteBranchOutcome`'s two scratch solves never
   asserted it. The per-occurrence result was free under the pins, so both
   solves were SAT and the walk stopped at the `if`.
2. `renderAsChoices` had no `ref` / `ptr` arm. A SUT with a ref or ptr
   parameter could not be passed to `assertCoveredBy`, or run as a `symex`
   phase: `{.error: "renderAsChoices: unsupported witness shape".}` at
   compile time.
3. A callee that read `result` before writing it (`result += 100`) had
   the read fall to the module-level-global arm of `lower`'s `iekVar`:
   `feGlobalReadUnmodelled` on the caller. Nim zero-initialises `result`.
4. A variant-returning closure declined on the caller
   (`seUnsupportedCompoundSortLeaf` + `feUnsupportedOp`). `buildClosure`
   derives the funcSym's range sort from the return type, and a variant
   has no single-leaf sort. `defaultZero` also had no variant arm, so a
   bare `return` of a variant (closure or callee) and an untouched variant
   result were `feUnsupportedOpHavoc`.

- **Runtime.**
  - `pathRoots` is split. The run-wide pools (closure axioms,
    `stripDecompConds`, `containerCardConds`) move to `globalRoots`, which
    `pathRoots` appends after the path's own facts, in the same order.
    `concreteBranchOutcome` and `concretelyInfeasible` assert
    `globalRoots()` too. Each pool is definitional or true of every real
    input, so it prunes no execution the draws describe.
  - `lower`'s `iekVar` arm: an unbound `result` inside a callee or closure
    frame reads `unwrittenResultZero()`, the innermost `CallFrame`'s
    `retTy` zero value, when `defaultZeroTotal` says it has one. Otherwise
    (no frame, a void frame, a type with no zero) it keeps the global-read
    decline. The SUT's own frame is not covered (below).
  - `defaultZero` gains an `itVariant` arm: discriminator ordinal 0 and
    every plain and arm field its own zero. `variantZeroTotal` (and so
    `defaultZeroTotal`) holds only when that is a legal value of the type:
    the discriminator's type holds 0, 0 is a legal tag
    (`discriminatorDomain`), and every field has a zero. A multi-variant,
    or a variant failing `variantZeroTotal`, still raises, through the one
    pre-existing variant raise site (its category-c marker reworded to
    name both), so the `r6_n36_raise_class_audit` inventory is unchanged.
    The first cut added a second marked raise and moved that audit's
    `runtime.nim` and category-c counts by one; the gate caught it. This
    reaches every `defaultZero` site: `completeReturn`'s
    bare return, the `isCall` untouched-result fall-through, and the
    closure's.
  - `closureRetStructured(t)` (a variant). `buildClosure` gives such a
    funcSym a Bool placeholder range instead of deriving one.
    `applyClosureGround` makes the per-occurrence result a fresh variant
    (`allocateSym`), not a fresh constant of the range sort. Its allocation
    facts (the discriminator's legal tags) join `currentClosureCallAxioms`.
    `retBindEq`'s variant arm already binds each exit's value.
  - `renderAsChoices` becomes a wrapper over `renderInto`, which threads
    the cells rendered so far. A ref / ptr renders as one integer tag, then
    its pointee: 0 = nil; 1 = a new cell, followed by the pointee; k + 2 =
    the k-th cell already rendered (an alias or a cycle), with nothing
    after it. The bounds are `[0, 1 + cells so far]`. So the encoding is
    total over cyclic witnesses and keeps aliasing, and a tree-shaped
    witness is all 0 / 1 tags. `renderAsChoicesVersion` does not move: no
    ref witness could render, or persist, before.
- **Consumer-visible (for S11's migration note).**
  - Concolic collection: an `if` on a closure call that returns now records
    its decision (`branchTrace` gains it and every decision after it;
    `ambiguousBranches` drops).
  - `assertCoveredBy` and the `symex` phase accept SUTs with `ref` / `ptr`
    parameters. `SymexFinding.witnessChoices` for them uses the tag
    encoding above.
  - Programs that were `sxUnknown` now get verdicts: a callee or closure
    reading `result` before writing it (`feGlobalReadUnmodelled`), a
    variant-returning closure (`seUnsupportedCompoundSortLeaf`,
    `feUnsupportedOp`), and a variant result left untouched or returned
    bare (`feUnsupportedOpHavoc`).
  - The walker bump to 162 invalidates every symex cache entry.
- **Different mechanisms, reported and not fixed here.**
  - The SUT's own frame reading `result` before writing it
    (`proc sut(x: int): int = result += 3`) is still
    `feGlobalReadUnmodelled`. The IR carries no return type for the SUT's
    own frame (the call stack is empty there), so there is no type to take
    the zero of.
  - An augmented assignment to a field of `result` (`result.a += x` on a
    tuple result) is `feUnsupportedStmtKind` ("LHS `result.a` is not a
    simple variable"). This is the general augmented-field-assign gap, not
    a `result` one.
  - `result.add 'z'` on a `string` result is `seUnsupportedStringOp`
    (`string add (non-string arg)`): a char append is unmodelled.
  - A closure returning any other multi-leaf or non-scalar type (a tuple of
    more than one field, a `string`, a `seq`) still declines as a variant
    did (`feUnsupportedOp` from `buildClosure` or `symValFromRawAst`, or
    `seUnsupportedCompoundSortLeaf` from the sort derivation). The `closureRetStructured` route would carry them
    too, but each needs its `retBindEq` arm checked, and this slice did not
    widen past the variant.
  - A multi-variant (two `case` sections) has no zero value, so its
    untouched or bare-returned result stays `feUnsupportedOpHavoc`.
  - A callee that assigns a multi-variant or a `distinct` result
    (`result = MV(k: kb, b: 3, j: ka, c: 1)`, `result = D(3)`) is
    `weInternalWalkerFault` ("retBindEq: kind mismatch svMultiVariant vs
    svBV64", and `svDistinct vs svBV64`): the assigned value reaches the
    binding as a 64-bit int. Found while moving the havoc-site pins off the
    single-case variant; pre-existing (the assignment path is untouched
    here). The re-pins below use never-assigned results for that reason.

Pins: `tests/tsymex_rfc0005_s8n_precision.nim`. It covers:
- (1) true and false closure conditions decided (RED: `ambiguous=1`,
  `branchTrace.len` 2 and 0), and an int-valued closure result compared;
- (2) nil, a cell, a cycle, an alias against two equal cells,
  determinism, a `ptr`, and `assertCoveredBy` over a ref-param and a
  ptr-param SUT (RED: the compile-time `{.error.}`);
- (3) `result +=` in a callee, a `bool` result, and a closure (RED:
  `feGlobalReadUnmodelled`);
- (4) a variant closure result on both arms with a dead label (RED:
  `seUnsupportedCompoundSortLeaf`), and a bare return's zero value (RED:
  `feUnsupportedOpHavoc`);
- the `>= 162` floor.

Re-pinned, each checked against real Nim:
- `phase15_CR2_cachekey` pin (162).
- `rfc0005_s7_closure`: the sink audit reads `pathRoots` and `globalRoots`
  (same five pools, same order) and pins that `pathRoots` appends
  `globalRoots()`.
- `rfc0005_s8i_models` (5b): `pred(7)` is true in Nim, so the outer `if`
  now records `armTaken == 0` after the body's `v == 0` (was: the walk
  stopped there, ambiguous).
- `rfc0005_s8m_exits` (5): the variant bare return is its zero value, so
  the dead label is `sxUnsat` with no `feUnsupportedOpHavoc`.
- `r6_r2_zerodefault_result` T5h-2: the untouched variant result is its
  zero value (`sxSat`, no decline; a non-zero value there is `sxUnsat`).
  T5h-3 keeps the decline pin on a never-assigned multi-variant.
- `rfc0005_s6b_ops`: the havoc-site kind pin moves to a never-assigned
  multi-variant result.
- `rfc0005_s8l_exits` (1): a bare return of a variant is its zero value
  (dead label `sxUnsat`, no `feUnsupportedOpHavoc`); the havoc-site pin
  moves to a never-assigned multi-variant.

**As landed (S8o, walker 163) — S8k's termination remainder.**

*The symex-mingw red (P0).* S8k's character form matched Z3's `int2bv` by
its printed name, `int_to_bv`. That is Z3 5.x's spelling; the Windows leg's
Z3 4.13.4 prints `int2bv` (and `bv2int` where 5.x prints `ubv_to_int`). On
Windows the rewrite never fired, the byte tests reached Z3 lowered, and
B7R-6, B7r2-1a and B7r2-1a-red ran out of `seqQueryRLimit` (`sxUnknown`).
Linux (5.1) never saw it. `seqLenCaps` now matches every operator by decl
kind, read off terms built in the running Z3 (`SeqCapKinds`). The one
exception is `seq.last_indexof`: its kind is Z3's shared internal ordinal
(45100 on 4.13.4, 49165 on 5.1), and its name is the same on both, so it
stays name-matched. Measured with the three checks copied into probes, on
c, against the 4.13.4 shared library (`dt-bounded` plus
`LD_LIBRARY_PATH`):

| check | a696d80 | f6d8887 | S8o |
|---|---|---|---|
| B7R-6 | `sxSat` 95 s | `sxUnknown` 1194 s | `sxSat` 79 s |
| B7r2-1a | `sxSat` 73 s | `sxUnknown` 1181 s | `sxSat` 78 s |
| B7r2-1a-red | `sxSat` 176 s | (CI: `sxUnknown`) | `sxSat` 120 s |

On Linux 5.1 the same probes are `sxSat` in 83 s, 83 s and 218 s.

*The rest of the slice.*
- **Byte against byte, and byte against an input.** Both take the
  character form. `s[i] == s[j]` becomes `c == d`, or one side `""` and
  the other `"\xff"`. A byte against an 8-bit input `x` becomes
  `c == str.from_code(bv2nat(x))`, or `x == 0xFF` and `c == ""`. It
  applies only when `x` is an input: `bv2nat` of a computed term was not
  measured. Measured from their own text on 4.13.4: 2.5M units lowered
  against 51k, and 8.5M against 185k. In the walker (5.1) both lowered
  forms ran past 20M units (`sxUnknown`).
- **Constant bit-vector to Int.** `bvTermToZ3Int` folds a numeral to its
  Int value. Z3 builds a signed `bv2int` of a constant as an unevaluated
  `ite`, and every constant string index reached the query in that form.
- **`pcSatByConcreteInputs`.** Runs under `concreteBranchRLimit` with
  `random_seed = 0`; it had no bound. An exhausted check is `false`.
- **`seq.last_indexof` and the incremental core.** Proof by construction:
  the only check under assumptions in `src/` is `checkCapped`'s step 2,
  and it is skipped when `lastIndex` is set. Every other check, and every
  model, comes from a one-shot `check()` of a fresh solver, and the walker
  builds no quantifier. A guard test pins the skip: removing
  `not lastIndex` turns its `sxSat` into `sxUnsat`.
- **Z3 cost depends on history.** It is per-context, not per-process, and
  it is Z3's behaviour. SMT-LIB text loaded into fresh contexts
  reproduced a query's unit count exactly (33,858,060) before and after
  80M units of unrelated work in other contexts. A second solver in the
  same context, on the same text, went from past 40M to `sxSat` at
  3.25M. Every query of one walk shares one context, so a walk's earlier
  queries shape later ones. The effect is deterministic for a given SUT
  and Z3 build. Fixing it would need one context per query, which means
  translating every query; that was not done. Documented at
  `checkCapped`.

Pins: `tests/tsymex_rfc0005_s8o_termination.nim`.
- (0) `s[19] == 'q'` within 1M units: RED on 4.13.4.
- (1) pair and input forms within 1M units: RED on 5.1 (`sxUnknown`), plus
  an `sxUnsat` byte contradiction.
- (2) the numeral fold: RED was a compile error.
- (3) the concolic bound: RED was "was true".
- (4) the rfind guard.
- The `>= 163` floor.

Re-pinned:
- `phase15_CR2_cachekey` (163).
- `g1b_concolic` R7: at `queryRLimit = 1`, `pcSatByConcreteInputs` is now
  `false`. The check runs under that bound and proves nothing (it was
  `true` only because the check was unbounded). Its "degrading early
  asserts nothing false" intent moves to a companion: the same trace under
  the default budget decides the branch, and the check proves the draws.

*Different mechanisms, reported and not fixed here.*
- **`b7r_bytescan` still runs past 900 s on Linux c.** It hung the same
  way at the S8n base. Five checks pass before the kill (B7R-1 through
  B7R-2c).
  - **Where it stalls.** B7R-3 (`sutByteScanPairFound`, the B3 scan-pair
    shape over `seq[byte]`). The walk's sixth solver check, step 1 of
    `checkCapped` under a 10M `rlimit`, does not return within 300 s.
  - **The query.** `str.indexof(data, "\0", bv2int(start)) ==
    bv2int(start + 4)`. `start` is a symbolic `int` parameter, allocated as
    a 64-bit bit-vector, so the signed `bv2int` bridge (an `ite` over
    `bvslt`) sits inside a string query. No byte test is involved.
  - **Standalone, in a fresh 5.1 context,** the same SMT-LIB text is
    bounded: `unknown` at 10M units in 36 s. With `start` fixed it is SAT
    in 28 ms. The 4.13.4 CLI is also `unknown` at 10M, in 8 s.
  - **Mechanism.** Inside the walk's shared context, Z3 stops polling the
    resource counter on this query. This is the per-context effect above,
    on a bit-vector-to-Int bridge into the string theory.
  - **What would fix it.** Keeping `start` out of the bit-vector domain
    (allocating it as an Int, or declining the bridge the way
    `runtime_strings` already declines a bit-vector bound). That is a
    change to parameter allocation.
- **`b7r2_pathscope` now ends in 528 s on c, every check `[OK]`.** It
  stays on `sweep.sh`'s skip list next to `b7r_bytescan` until it has also
  been measured on cpp and under gate load.
- **B7R-6's walk forks 2^15 target-hit solves.** Each of the sixteen
  conjuncts of its `symexAssume` forks, giving 32,768 trivial UNSAT
  solves (about 3 s in all). The cost is small, but the fork is not
  needed.

**As landed (S8p, walker 164) — S8n's precision remainder.** The six
places S8n reported, plus one fault found on the way. Every expected value
was probed against the pinned toolchain (Nim 2.2.10, debug build) by an
oracle test that runs the SUT itself.

1. A callee assigning a multi-variant or `distinct` result was
   `weInternalWalkerFault` ("retBindEq: kind mismatch"). Two causes. A
   multi-variant constructor had no IR: the parser declined it and left an
   int placeholder, which `retBindEq` then met against the multi-variant
   `retSym`. And `retBindEq` had no `svDistinct` or `svMultiVariant` arm,
   so a `D(3)` result (the identity pass-through, a plain int) and a
   passed-through multi-variant hit the kind-mismatch raise.
2. A multi-variant had no zero value (`feUnsupportedOpHavoc` on an
   untouched or bare-returned result).
3. The SUT's own frame reading `result` before writing it was
   `feGlobalReadUnmodelled`: the IR carried no return type for the SUT.
4. A field write on a value tuple or object was `feUnsupportedStmtKind`.
   This covered plain assignment as well (`o.a = x`: "unsupported nnkAsgn
   shape"), not only `result.a += x`.
5. `s.add(c)` with a `char` was `seUnsupportedStringOp`.
6. A closure returning a tuple of more than one field, a `string` or a
   `seq` declined (`feUnsupportedOp`, `seUnsupportedCompoundSortLeaf`).
   An index read straight off such a call (`h(x)[0]`) was a
   `weInternalWalkerFault`: `lowerLeafInExpr` asserted that the index
   container was a variable or a field.

- **IR / parser.**
  - New `iekMultiVariantLit` (`mvlTy`, `mvlAxisTags`, `mvlAxisFields`,
    `mvlPlainFields`), with its emit, render, canonical (`Ex<MVL:`),
    abstraction and defect-fork-scan arms. The parser builds it when every
    axis's discriminator is a literal naming an explicit, non-`else` arm.
    A symbolic discriminator, or one that falls in an `else` arm, keeps the
    old decline.
  - `SymexProgram.retTy` carries the SUT's return type (nil for a void
    SUT). `canonicalize(prog)` appends `;ret=<type>` only when it is
    non-nil, so every void SUT's key is unchanged.
  - `valueFieldTy` / `valueFieldWrite`. `o.a = v`, `o.inner.b = v` and
    `o.a op= v` (`+=`, `-=`, `*=`, and `&=` on a string field) become an
    assignment of the root: a rebuilt `iekTupleLit` whose written field is
    the new value and whose other fields are reads of the old ones, one
    level per `.`. Every step of the chain must classify `itTuple`. A
    ref/ptr step keeps the heap-write arms, a variant arm field keeps its
    decline (its discriminant check is not modelled on this route), and so
    does a positional element (`q[0] += b`). A ranged int field declines
    unless the value is itself the range-checked conversion (`=`), and
    always for `op=`. The rebuilt write has no per-field `RangeDefect`
    fork. An augmented write's overflow check is the binop's own, as for a
    variable.
  - `s.add(c)` with a `char` argument (`typeKind == ntyChar`) is
    `s := s & c`.
  - `liftIndexContainer`: an `isIndex` container that is not a variable or
    a field chain over one is bound to a synthetic `let` first, before the
    index is parsed (Nim evaluates the container first).
- **Runtime.**
  - `retBindEq` compares a `distinct` by its base value (`ejectBase`), and
    a multi-variant per axis: the discriminators equal, each arm's fields
    equal under `variantDiscEq(disc, tag)`, and the plain fields equal. A
    genuine (non-placeholder) `seq` binds its length and its data array;
    it was an in-band `feUnsupportedOp`. The two call-return drains share
    one `retBindWiredKinds` set, which gains `svMultiVariant`, `svSeq` and
    `svDistinct`.
  - `defaultZero` builds a multi-variant's zero value when
    `multiVariantZeroTotal` holds: every axis's discriminator type holds 0
    and 0 is an explicit arm's tag, and every field has a zero. A
    multi-variant whose ordinal 0 falls in an `else` arm is not covered
    (below). It still raises through the one pre-existing variant raise
    site, whose marker is reworded, so the `r6_n36_raise_class_audit`
    inventory is unchanged.
  - `unwrittenResultZero` reads `WalkerStatics.sutRetTy` when the call
    stack is empty (the SUT's own frame), so an unbound `result` there is
    its return type's zero value.
  - `iekStrConcat` turns a char right operand into the 1-byte string
    (`needleAsStr`).
  - `closureRetStructured` covers a multi-variant, a tuple, a `string` and
    a `seq` as well as a variant: the funcSym gets a Bool placeholder
    range, and each occurrence's result is a fresh `allocateSym` value bound
    by the ground axioms.
- **Consumer-visible (for S11's migration note).**
  - Programs that were `sxUnknown` now get verdicts: a callee assigning a
    `distinct` or multi-variant result (was a walker fault), a multi-variant
    constructor, an untouched or bare-returned multi-variant result, the
    SUT reading its own `result` before writing it, field writes and
    `op=` on value tuples and objects, `s.add(c)` with a char, a closure
    returning a tuple, `string` or `seq` (and an index read off such a
    call), and a callee returning a `seq` (was `feUnsupportedOpHavoc`).
  - The canonical program form of a value-returning SUT carries its return
    type. The walker bump to 164 invalidates every symex cache entry.
- **Different mechanisms, reported and not fixed here.**
  - A multi-variant whose ordinal 0 falls in an `else` arm has a legal Nim
    zero value, but `multiVariantZeroTotal` requires an explicit ordinal-0
    arm on each axis, so it keeps `feUnsupportedOpHavoc`. The havoc-site
    pins now use that shape.
  - A callee returning an `array` is still `feUnsupportedOpHavoc`:
    `retBindEq` has no `svArray` arm. The havoc-site pins that used a `seq`
    result moved to an `array` result.
  - A field write on a variant arm field (`v.a = x`) and a positional
    tuple-element write (`q[0] = b`, `q[0] += b`) stay
    `feUnsupportedStmtKind`. `rfc0005_s3_monotonicity`, `s1b_kinds`,
    `s1c_verdict` and `augmented_assign` moved their Class-B trigger to the
    positional form.
  - Comparing an element of a `seq[uint8]` against a literal
    (`let v = @[x, 1'u8]; if v[0] == 7`) is `weInternalWalkerFault`
    ("field 'bv8' is not accessible ... kind = svBV64"). It is pre-existing
    and does not depend on a call: the local literal alone faults. It was
    found while probing the new `seq` result binding.

Pins: `tests/tsymex_rfc0005_s8p_precision.nim`. It covers:
- (1) a `distinct` result, a multi-variant result on both axes, and a
  multi-variant passed through a callee (RED: `weInternalWalkerFault`);
- (2) an untouched and a bare-returned multi-variant's zero value (RED:
  `feUnsupportedOpHavoc`);
- (3) the SUT's own `int`, `bool` and tuple `result` read before any write
  (RED: `feGlobalReadUnmodelled`);
- (4) `result.a += x`, `o.a = x`, `-=`/`*=` (one operand through
  `nnkHiddenAddr`), a nested write that changes only its own field, and the
  overflow check of a field `+=` (RED: `feUnsupportedStmtKind`);
- (5) `result.add 'z'` and a symbolic char appended (RED:
  `seUnsupportedStringOp`);
- (6) closures returning a two-field tuple, a `string` and a `seq`, and an
  index read off the call (RED: `feUnsupportedOp`, `weInternalWalkerFault`);
- (6b) a `var` parameter's field writes reaching the caller, `&=` on a
  string field, and a variant arm field write that still declines;
- the `>= 164` floor.

Re-pinned, each checked against real Nim:
- `phase15_CR2_cachekey` pin (164).
- `r6_n27_placeholder_read_audit`: 70 -> 74 `runtime.nim` markers (the
  four lines of `retBindEq`'s seq binding, behind the placeholder guard).
- `r6_r6_emit_roundtrip`: the `iekMultiVariantLit` arm, a sentinel and its
  round-trip test.
- `r6_a1_variantlit` A1-5 and `tot1_totality_corpus`'s A1 row: a literal
  multi-variant constructor is modelled (`sxSat`, and a dead twin
  `sxUnsat`); the corpus row now pins the symbolic-discriminator decline.
- `r6_r2_zerodefault_result` T5h-3: an untouched multi-variant is its zero
  value; T5h-4 pins the `else`-arm multi-variant's decline.
- `rfc0005_s6b_ops`, `rfc0005_s8l_exits`: the no-zero result pins move to
  the `else`-arm multi-variant; the composite-result havoc pins move from
  `seq` to `array` results. `tot1_totality_corpus`'s A6-rider row likewise.
- `phase15_S11_mutation` `addChar`: `sxSat`, witness `'c'`.
- `r6_lows_declines` N30 and `r6_n16_closure_zerodefault` N16-4: a string
  closure result is modelled; N30-2 pins the classified decline on an
  `array` closure result.
- `r6_n37_raise_residue` N37-4: the tuple closure is no longer declined by
  `buildClosure`; the pin moves to `lowerHofCall`'s
  `seNestedSeqUnsupported`.
- `rfc0005_s3_monotonicity`, `rfc0005_s1b_kinds`, `rfc0005_s1c_verdict`,
  `augmented_assign`: the Class-B `feUnsupportedStmtKind` trigger is a
  positional tuple-element `+=`; `augmented_assign` also pins the field
  `+=` as modelled (`sxUnsat`).

**As landed (S8q, walker 165) — S8o's termination remainder.**

*B7R-3: the offset parameter is an Int.* The stalled query was
`str.indexof(data, "\0", bv2int(start)) == bv2int(start + 4)`: `start`, an
`int` parameter, was a 64-bit bit-vector, and every use of it in the
string query went through Z3's signed `bv2int` (an `ite` over `bvslt`).
Rewritten with `start` an Int (its range asserted, `start + 4` as Int
addition) the query is SAT in 0.09 s on the 4.13.4 CLI; the bridged text
is `unknown` at 10M units and SAT only at 100M (8.5 s). `collectScanPairOffsetParams` (`dsl_parser.nim`) now marks
an entry-proc `int` param that reaches a B3 scan-pair's loop index,
traced as B4's `collectIntOffsetParams` traces its offsets (one `var i =
<param>` rebind, one call boundary); the two share one collector,
parameterised by the loop shape. `IRParam.isScanPairOffset` carries the
mark, and `runSymexImpl` gives such a param with no declared or asserted
range its type's full range, so the existing `promoteSound` path
allocates it: a Z3 Int stamped with its width (every `+`/`-`/`*` on it
keeps its `overflowCondInt` fork), with `low(T) <= x <= high(T)` in the
initial path condition, logged as an `AbstractionEntry`. That is the
bit-vector's own value set, so no verdict can change except by Z3
answering. Two limits, both deliberate:
- only under `isOptimised` (the default); `isExact` keeps the
  bit-vector and the bridge;
- a param B4 already marks (`isIntOffset`) keeps that unstamped
  promotion unchanged.

The walker-level fix was chosen over bounding the check.
- **A wall-clock `timeout`** would make verdicts depend on the machine,
  which every other bound here avoids.
- **A context of its own per capped query** was built and measured. Z3's
  translator rejects string terms: translating a query holding
  `str.indexof` into a fresh context raised `Sort of polymorphic function
  'seq.indexof' does not match the declared type` (Z3 5.1). A Z3 API
  error voids the run's verdict (S8m), so B7R-1 through B7R-2c went
  `sxUnknown` and `s8o_termination` crashed. It would not have decided
  B7R-3 anyway: S8o measured the bridged query `unknown` at 10M units in
  a fresh 5.1 context. Item 4 (per-context cost history) is therefore not
  changed. It stays documented at `checkCapped`; the only route past it is
  one context per query, which needs a translation Z3 does not provide
  for string terms.

*B7R-6: a conjunctive assume is one assume per conjunct.*
`symexAssume(a and b)` and `symexAssume(a); symexAssume(b)` are the same
program: `a` is evaluated, and `b` is evaluated (and may raise) only when
`a` holds; either way the run is filtered unless both hold. The parser
now emits the split form, conjunct `k`'s preamble after assume `k-1`.
Parsed whole, D1c's guard temporaries (`let sc = a; if sc: sc = b`) are
chained, not nested, so every path forked at every conjunct whose right
side reads an index. A 12-conjunct assume made 2049 Z3 calls (2^11 + 1),
and now makes 13: the target solve plus one UNSAT raise solve per
conjunct.

*Timings.* Measured on the slice sha under gate-like load (S8p's `-j 6`
gate sweep running, plus five other `dt-bounded` runs; load average about
9 on 6 cores):

| suite | backend | S8o (5f85893) | S8q |
|---|---|---|---|
| `b7r_bytescan` | c | killed at 900 s (5 of 26 checks) | 51 s, 26/26 |
| `b7r_bytescan` | cpp | killed at 900 s (5 of 26 checks) | 54 s, 26/26 |
| `b7r2_pathscope` | c | 528 s, 11/11 (S8o, unloaded) | 279 s, 11/11 |
| `b7r2_pathscope` | cpp | 754 s, 11/11 | 277 s, 11/11 |

Both suites are off `sweep.sh`'s skip list. Before the assume split,
`b7r_bytescan` on c took 109 s (B7R-6 alone was about 80 s).

*Skipped-suite per-check comparison* (every `[OK]`/`[FAILED]` line, base
5f85893 against the slice, c and cpp; the c base is S8o's log of the
code-identical 5dc201f): no check goes from `[OK]` to
`[FAILED]`. `b7r_bytescan` goes from 5 `[OK]` then a kill to 26 `[OK]` on
both backends; `b7r2_pathscope` is 11 `[OK]` on both shas and both
backends; `snd3_6_equality_loop` is 3 `[OK]` on both.

Pins: `tests/tsymex_rfc0005_s8q_termination.nim`.
- (1) `start` promoted over `int`'s range (RED: no abstraction entry);
  B7R-3's shape SAT within `seqQueryRLimit = 2M` with a replayed witness
  (RED: `sxUnknown`, "canceled"); the overflow obligation on the promoted
  param (`OverflowDefect` at `high(int)`); a negative start still raises
  `IndexDefect` at the entry read.
- (3) a 12-conjunct assume in at most 13 Z3 calls (RED: 2049); short
  circuit kept (a guarded read never raises, an unguarded one does);
  contradictory conjuncts `sxUnsat`.
- The `>= 165` floor.

Re-pinned:
- `phase15_CR2_cachekey` (164 -> 165, after S8p).
- `phase15_A1_assertarg` cell 4: `symexAssume((x + y) > 0 and (x - y) <
  100)` against its hoisted twin. Both are `sxSat`, but the split assume
  orders the path condition differently, so Z3 returns a different model
  (inline `(-6291457, 274871877636)`, hoisted `(0,
  4611686018427387904)`). The pin now checks both witnesses against the
  real conditions (both hold in Nim, no overflow) instead of their
  equality. The inline form is also now faithful where the twin is not:
  it evaluates `x - y` only once `x + y > 0` holds.

*Different mechanisms, reported and not fixed here.*
- **D1c `and` chains fork 2^(n-1) paths everywhere else.** The guard
  temporaries chain (`let sc2 = sc1; if sc2: ...`), so the path where
  `sc1` is false still forks at every later `if`, unpruned. Only
  `symexAssume` is split here. `if a and b and c:`, `while`,
  `symexAssert(a and b ...)` and `let x = a and b ...` with index-reading
  right sides keep the blow-up. Nesting each guard inside the previous
  one (`if sc: ...; sc = b; if sc: ...`) would make it linear for all of
  them.
- **Other scan shapes keep the bridge.** Only the B3 scan-pair's index is
  traced. A Q1/B0 skip-while scan or a pair loop seeded from an `int`
  param still bridges it into the string query as a bit-vector, and so
  does any param under `isExact`.
- **B4's `isIntOffset` promotion is still unstamped.** It carries no
  width and no range, so arithmetic on such a param has no overflow
  obligation (the existing, tracked gap at `runSymexImpl`).
- **`tsymex_snd3_6_equality_loop` no longer hangs.** It is still on
  `sweep.sh`'s skip list ("hangs on BOTH backends"). It passed, all 3
  checks, at base 5f85893 (c: S8o's log; cpp 89 s) and at this slice
  (c 53 s, cpp 65 s). Its entry is stale.
- **CLAUDE.md** still says six `tsymex_r6_*` suites hang on Linux; none
  of the six is skipped any more.
**As landed (S8r, walker 165, no bump) — the symex-mingw shard 2 runner loss.**

*The suite.* `tsymex_163rev_intoffset_range`, index 9 of shard 2's 123. S8k
added its three range-checked label searches, whose RangeDefect witness is
a string longer than 1000 bytes. Every shard 2 suite was run on Linux
against the 4.13.4 shared library at 671fef5 (peak RSS of the test
binary, 10 GB container cap): this one grew to 10,219 MB and was killed at
510 s. No other suite passed 100 MB. A CI run with the watchdog below
(run 36628492946, the pre-fix sha) killed it at 240 s with a 2,391 MB
peak working set, and the shard finished with its log.

*Two unbounded checks in `checkCapped`, both on Z3 4.13.4 only.*
- **Step 1b was not theory-free.** It sets `smt.string_solver = none` as
  a solver parameter. Z3 4.13.4's default (combined) solver ignores it:
  `str.len(x) < 0` is UNSAT there, SAT on 5.1. So step 1b ran the
  uncapped string search, which does not poll `rlimit`. Z3's simple
  solver honours the parameter on both builds. `querySolver` now probes
  the linked Z3 once per thread (`theoryFreeSimple`) and uses the simple
  solver for `seqTheory = false` when the default one ignores it. On 5.1
  nothing changes.
- **Step 2 searched the long strings too.** Its caps sit behind the
  assumption literal, so preprocessing does not see them. For the query
  `len(s) > 1000` under the 128 cap, the 4.13.4 CLI took 2.3M units and
  992 MB to answer UNSAT. The sibling query ran out of memory at 3 GB
  before reaching the 20M `rlimit`. New step 1c: the caps are ASSERTED
  into the theory-free query. If that is UNSAT (and 1b was not), the cap
  takes part in the only refutation visible without a string search, so
  the result is `zsUnknown` with the cap message. That is the same verdict
  step 2 gives on a core naming the cap, and no sequence-theory check
  runs.

After the fix, on 4.13.4: `intoffset_range` passes every check in 123 s
with a 1,410 MB peak. One step 2 (the `indexof` form: its theory-free
abstraction lets `str.indexof` go below -1, so 1c is SAT) still costs 58 s
and 1.2 GB.

*Attribution in CI.* Each corpus suite now runs through
`scripts/run-ci-suite.ps1`. The script compiles the suite, then polls the
test binary every 2 s. It kills the binary past 240 s of wall clock or a
6 GB peak working set, and reports that suite as failed. It prints
`<== suite rc wall peakWS` per suite. The shard step then finishes and
keeps its log.

*Ten registered suites never ran on the leg.* `derive-ci-suites.ps1` pairs
the quotes in the `test` task's list, comments included. The comment
`split(s, "")` shifted that pairing. From there on, each suite name parsed
as the text between two entries. As a result, `tsymex_rfc0005_s8g_models`
through `s8o_termination` were registered but never reached the corpus
(380 of 390 `tsymex_*` names were parsed). The script now removes `#`
comments before it pairs quotes. That adds those nine suites and this
slice's pin: the corpus is 380 suites, 127/127/126 across the shards.
None of them has run on Windows before.

Pins: `tests/tsymex_rfc0005_s8r_theoryfree.nim`.
- (1) `str.len(x) < 0` is SAT with `seqTheory = false`. RED on 4.13.4:
  `zsUnsat`.
- (1') A companion that is UNSAT with the theory.
- (2) The range-checked >1000-byte search is a recorded `maxSeqLen`
  decline. RED on 4.13.4: killed. With (1) alone fixed, step 2 still
  used more than 4 GB.
- Both pass on 5.1 before and after the fix. The RED needs the 4.13.4
  library.

*Different mechanisms, reported and not fixed here.*
- **Context history moved two scan-pair checks on 4.13.4.** Both have the
  same `hit` query, `str.indexof(data, NUL, bv2int(start)) ==
  bv2int(start) + 4`, where `start` is an int parameter in BV form.
  - `b3_scanpair` B3-1 read `sxRaised` before this slice (CI run
    36628492946) and `sxSat` after it (run 36635331030).
  - `b7r_bytescan` B7R-3 went the other way: `sxSat` before, `sxRaised`
    after (run 36635331030, scan-tail).
  - Traced on Linux against 4.13.4 at 671fef5: the walk's earlier step-1b
    checks ran the full sequence theory in the shared context, and the
    `hit` query's step 1 then went SAT in 13 s. With step 1b theory-free,
    the same step 1 exhausts its 10M units, and so does step 3. The path
    records `beSolverUndef` at `sevError`, so it is not pruned. The real
    ScanError raise (no NUL) is the verdict.
  - This is S8o's per-context cost effect. The query itself is S8q's:
    with S8q's `isScanPairOffset` Int allocation (3771cc0) and this slice
    on top, 4.13.4 gives B7R-3 `sxSat` in 1 s (the whole suite in 7.5 s)
    and B3-1 `sxSat`.
- **Step 2 on 4.13.4 is still a string search** whenever the theory-free
  abstraction cannot see the cap's conflict (the 58 s case above). Adding
  the sequence functions' range facts to the theory-free query would close
  it: `str.len >= 0` and `-1 <= str.indexof < str.len`.
- **`tsymex_r4_strip` runs 2.6 times longer on 4.13.4 than at a696d80**
  (91 s against 35 s wall, 51 s against 21 s user). It passes.

**As landed (S8s, walker 167) — S8p's precision remainder.** The five
places S8p reported, plus three soundness faults found on the way. Every
expected value was checked against the pinned toolchain (Nim 2.2.10, debug
build) by an oracle test that runs the SUT itself.

1. `seq[uint8]` literal: a `seq[uint8]` element compared against a literal
   (`let v = @[x, 1'u8]; if v[0] == 7`) was `weInternalWalkerFault`.
   `lowerSeqLit` lowered each element with no prototype. An int literal
   therefore became a 64-bit value, and `storeSeqElem` read its `bv8`.
2. `else` arm at ordinal 0: a multi-variant whose ordinal 0 falls in an
   `else` arm had no zero value (`feUnsupportedOpHavoc`). The cause was
   in `allocateSym`, and it was also a soundness fault. The multi-variant
   arm constrained each axis's discriminator to the disjunction of its
   arms' ordinals. That set included the `else` arm's sentinel -1 (0xFF on
   a `u8` discriminator) and left out every ordinal the `else` arm covers.
   So an input whose `k` fell in an `else` arm was unreachable, which is a
   false `sxUnsat`. A zero-valued callee result also contradicted its own
   allocation, which is why `multiVariantZeroTotal` required an explicit
   ordinal-0 arm.
3. `array` results: a callee or closure returning an `array` was havoc
   (`feUnsupportedOpHavoc`), or `feUnsupportedOp` for the closure.
   `retBindEq` had no `svArray` arm.
4. Field writes: a field write on a variant (`v.a = x`, `v.a += x`) and a
   positional tuple-element write (`q[0] = b`, `q[0] += b`) were
   `feUnsupportedStmtKind`.
5. `r6_n43_parity` on cpp: `tsymex_r6_n43_parity` did not compile. The
   failing statement was `validDefault`'s `f = low(F)`. There `F` was
   `std/atomics`' `AtomicInt8`, which cpp imports as `std::atomic<NI8>`.
   Its `operator=` is deleted.

Found on the way:

- (a) `retBindEq` guarded a variant's `else`-arm fields with
  `variantDiscEq(disc, -1)`, which no legal discriminator satisfies. So a
  callee's `else`-arm fields were never bound to its result. This was a
  free value and a false `sxSat`: a dead label behind them (`r.e != 0`
  after a zero result) was `sxSat`, and replay did not refute it.
- (b) The multi-variant witness emitter rendered an `else` arm as
  `DiscTy(-1)`. This was a compile error in every SUT taking such a
  multi-variant as input. It had never been reached, because of (2).
- (c) With (2) fixed, an input axis with a `range` discriminator and an
  `else` arm could take its `else` values. The emitter rendered no branch
  for them (the `default` fallback), so a clean `sxSat`'s witness would not
  reach its label. RFC-0005 S8f had fixed the same thing for a single
  `case`.

- **Runtime.**
  - `lowerSeqLit` lowers each element against the element type's
    prototype (`bvConst(elemTy, 0)` for an int, a bool for a bool), as
    `lowerTupleLit`'s fields do.
  - `discriminatorDomain`'s body is split out as `discDomainOf`.
    `axisDiscriminatorDomain(ax)` applies the same decision to one axis of
    a multi-variant.
  - `allocateSym`'s multi-variant arm constrains each axis's discriminator
    to that domain: the explicit tags, the enum ordinals an `else` arm
    covers, and for a `range` discriminator with an `else` arm its
    declared range. The single-case variant already did this.
    `multiVariantZeroTotal` then asks the same question
    `variantZeroTotal` does: is 0 a legal tag?
  - `armSelected(disc, tagOrd, arms)` guards an arm's field binding in
    `retBindEq`, for the variant and the multi-variant. An `else` arm
    (key -1) is selected exactly when no explicit arm is.
  - `retBindEq` binds an `svArray` element-wise and joins
    `retBindWiredKinds`. `closureRetStructured` covers `itArray`.
  - `lowerVariantFieldSet` lowers the new `iekVariantFieldSet`. The result
    is the receiver with one field replaced: the plain field, or the arm
    field in every arm that declares it. The new value lowers against the
    old one's prototype. A receiver with no such slot (its constructor
    already declined) degrades with `seVariantFieldOnDeclinedCtor`.
  - `validDefault` writes `low(F)` through a size-matched integer and
    `copyMem`. It no longer uses `f = low(F)`.
- **IR / parser.**
  - `iekVariantFieldSet` (`vfsRecv`, `vfsFieldName`, `vfsTags`, `vfsVal`)
    has its emit, render, canonical (`Ex<VFS:`), abstraction and
    defect-fork-scan arms.
  - `valueFieldTy` / `valueFieldWrite` now go through `fieldStep`. A step
    is `recv.name` on a tuple, `recv[<int literal>]` on a tuple, or
    `recv.name` on a variant or multi-variant (a plain or arm field, never
    a discriminator). The receiver may itself be a field, element or
    checked-field step.
  - A variant step rebuilds with `iekVariantFieldSet`. A tuple step
    rebuilds with `iekTupleLit`, as before.
  - When a step is an arm field (`valueFieldChecked`), the plain-assign
    arm parses the read of the LHS before the value. That read's
    `isVariantField` forks the out-of-arm `FieldDefect`. Nim checks the
    field before it evaluates the value: `v.vb = 100 div x` with `v` in the
    other arm raises `FieldDefect` at x = 0, not `DivByZeroDefect`. The
    `op=` arm already reads the LHS first.
- **Witness.** The multi-variant emitter renders an `else` arm as one
  branch per enum ordinal it covers. For a `range` discriminator (at most
  2^16 values) it renders one branch over the range minus the explicit
  tags, with the discriminator bound to the selector's `let`. Both follow
  the single-case emitter.
- **Consumer-visible (for S11's migration note).**
  - **Newly reachable.** A multi-variant input whose discriminator falls
    in an `else` arm is now reachable. Labels behind it were a false
    `sxUnsat`.
  - **Now bound.** A callee's variant or multi-variant result binds its
    `else`-arm fields. Labels that depended on them were a false `sxSat`.
  - **`sxUnknown` programs that now get verdicts:**
    - a `seq[uint8]` literal compared against a literal
    - a multi-variant result whose ordinal 0 is in an `else` arm
    - an `array` callee or closure result
    - variant and multi-variant field writes
    - positional tuple-element writes
  - **cpp.** An SUT whose cell holds an `Atomic` compiles.
  - **Cache.** The canonical program form changes for any SUT with a
    variant field write. The walker bump to 167 invalidates every symex
    cache entry.
- **Different mechanisms, reported and not fixed here.**
  - **`else`-covered constructor.** A variant constructor naming an
    `else`-covered tag (`S8sVE(vk: s3B, ve: 1)`) is still
    `feUnsupportedExprKind` ("else-covered/unresolved-tag variant
    constructor unmodeled"). A field write on its value then degrades with
    `seVariantFieldOnDeclinedCtor`. The S8s pin for an `else`-arm field
    write therefore takes the variant as an input.
  - **Local `Table` / `HashSet` in a callee.** A callee building a local
    `Table` or `HashSet` and returning it (`var t: Table[string, int];
    t["a"] = n; result = t`) is `weInternalWalkerFault`. The failures are
    `lower`'s `iekTableSet` `doAssert recv.kind == svTable` and its
    `iekSetIncl` twin. A callee assigning a `ref` result through
    `new(result)` is `weInternalWalkerFault` as well ("retBindEq: kind
    mismatch svRef vs svBV64"). All three were found while picking the new
    havoc-site pins. A `Table` passed through a callee is a clean
    `feUnsupportedOpHavoc`: `retBindEq` does not bind `svTable`, `svSet`,
    `svRef` or `svPtr`.
  - **No zero value.** An untouched `distinct` result has no modelled zero
    value (`feUnsupportedOpHavoc`, "kind itDistinct"), although Nim's
    default is the base type's zero. So does any type with a `HashSet` or
    `Table` field.
  - **`bool` discriminator.** A multi-variant with a `bool` discriminator
    on any axis is `weInternalWalkerFault` ("multi-variant axis disc must
    be a BV kind (got svBool)"). This is `allocateSym`'s one raise-audited
    site, kept as it was. A single-case `bool` variant is modelled.
  - **Array-element `op=`.** An array element's `op=` (`a[0] += b`) is
    still `feUnsupportedStmtKind`. `fieldStep` takes a positional step only
    on a tuple. This is the Class-B trigger the pins below moved to.

Pins: `tests/tsymex_rfc0005_s8s_precision.nim`. It covers:
- (1) an input byte in a `seq[uint8]` literal, a constant byte literal and
  a signed 8-bit literal (RED: `weInternalWalkerFault`);
- (2) an untouched and a bare-returned multi-variant with ordinal 0 in an
  `else` arm (RED: `feUnsupportedOpHavoc`), plus a single-case one;
  - an input's `else`-covered discriminators on both axes (RED: a compile
    error in the witness emitter);
  - a `range` discriminator's `else` values in the witness (RED, with the
    emitter's range branch removed: the witness renders `r == 0`, and
    replaying it raises `FieldDefect`);
  - dead labels on a callee's `else`-arm fields (RED: `sxSat`, with
    `armSelected` reverted);
- (3) a callee's `array` result (assigned, untouched, passed through) and
  a closure's (RED: `feUnsupportedOpHavoc`, `feUnsupportedOp`);
- (4) variant field writes:
  - in-arm, `+=`, plain, `else` arm, through a `var` parameter, nested
    under an object, a tuple inside an arm, on a multi-variant
    (RED: `feUnsupportedStmtKind`);
  - the out-of-arm write raising `FieldDefect`, with the field check
    before the value;
  - a symbolic discriminator;
  - positional tuple writes, nested and mixed with named ones;
- (5) the n43 cpp build, pinned by `tsymex_r6_n43_parity` compiling on
  cpp (RED: `use of deleted function ... std::atomic<signed char>::operator=`);
- the `>= 167` floor.

Re-pinned, each checked against real Nim:
- `phase15_CR2_cachekey` pin (167).
- `r6_r6_emit_roundtrip`: the `iekVariantFieldSet` arm, two sentinels
  (arm field, plain field) and their round-trip tests.
- `rfc0005_s8p_precision` (6b): a variant arm field write is modelled
  (`sxSat`, witness 6).
- The no-zero result pins moved from the `else`-arm multi-variant (now
  modelled) to one with a `HashSet` arm field:
  - `r6_r2_zerodefault_result` T5h-4
  - `rfc0005_s6b_ops`
  - `rfc0005_s8l_exits`
- The composite-result havoc pins moved from an `array` result (now
  bound) to a `Table` passed through the callee:
  - `rfc0005_s6b_ops` (dead, live, fresh)
  - `tot1_totality_corpus`'s A6-rider row
- `r6_lows_declines` N30-2: the closure decline is pinned on a `Table`
  result.
- The Class-B `feUnsupportedStmtKind` trigger is now an array element's
  `+=`:
  - `rfc0005_s3_monotonicity`
  - `rfc0005_s1b_kinds`
  - `rfc0005_s1c_verdict`
  - `augmented_assign`

**As landed (S8t, walker 168) — S8q's termination remainder.**

*`and`/`or` chains lower to nested guards.* `lowerShortCircuitParts`
(`dsl_parser.nim`) takes a whole same-operator chain, flattened by
`flattenShortCircuitChain` (a builtin, boolean, same-operator operand is
descended into; a different operator is one operand), and lowers it with
one guard temporary whose guards nest:
`let sc = a; if sc: (<b's reads>; sc = b; if sc: (<c's reads>; sc = c))`
(`if not sc` for `or`). A pure operand joins the one before it flat, as
D1c's fast path did. Before, each binary node had its own temporary,
chained (`let sc2 = sc1; if sc2: ...`), so the path on which an early
operand was false reached every later guard as a fresh fork. A
12-operand chain with raising reads made 2049 Z3 calls in `if`, `let`,
`symexAssert(not ...)`, `while` and an `or` chain; it now makes 13 (the
target solve plus one UNSAT `IndexDefect` solve per read). Short-circuit
order is unchanged: operand k's hoisted reads run only inside operand
k-1's guard. S8q's per-conjunct `symexAssume` split stays (it forks
nothing at all).

`mkShortCircuitWhile` flattens the guard's `and` chain too. `A` is the
longest plain prefix (the first operand hoists nothing, the rest are
pure) and `B`, the rest, is lowered nested inside the body
(`while A: <B>; if not B: break; body`). When the first operand hoists,
the rotation re-runs the whole chain's nested lowering. Before, the split
was only at the top binary node, so `(X and Y) and B` with a hoisting `X`
was rotated with `preA & preB`, which ran B's reads outside A's guard,
and a long guard forked 2^(n-1) paths. The pin
`while s.len > 0 and s[0] == 'a' and i < s.len and s[i] == 'a'` (with
`s.len <= 3`) was `sxUnknown` (`beBudgetExhausted`) for `tIndexError`
and is now `sxUnsat`.

*Every scan offset is a width-stamped Int.* `collectScanOffsetParams`
(was `collectScanPairOffsetParams`) traces an entry `int` param to a
Q1/B0 skip-while scan's index and a B6 pair loop's counter as well as a
B3 scan-pair's (`scanOffsetIndex`); `IRParam.isScanPairOffset` is renamed
`isScanOffset`. In `runSymexImpl` a B4 accumulating-scan offset
(`isIntOffset`) takes the same path: with no declared range it gets its
type's range and goes through `promoteSound`, a Z3 Int stamped with its
width, range in the initial path condition, every `overflowCondInt` fork
kept. It was an unstamped Int with no range, so arithmetic on it had no
overflow obligation. The R3 note measured the stamp without a range
(`b4_readcstring` past 15 minutes); with the range it runs in 90 s under
load. Under `isExact` an offset param (either kind) is promoted the same
way when arithmetic is checked (`acOverflow`): the stamped Int over the
type range has the bit-vector's values and defects, so only Z3's ability
to answer changes. Under `isExact` an asserted range is not used for it,
only the type range. With unchecked arithmetic `isExact` keeps the
bit-vector, because a bit-vector wraps and an Int does not.

*Skip list and CLAUDE.md.* `tsymex_snd3_6_equality_loop` passes all 3
checks at a58856d in 26-47 s (c) and 43-62 s (cpp), and at this slice in
49 s (c) and 62 s (cpp), with the host at load average 20-24. It is off `sweep.sh`'s skip list and
`derive-ci-suites.ps1`'s Windows one, both now empty. `CLAUDE.md` says no suite is known to hang on Linux/podman.

*Skipped-suite per-check comparison.* The only skipped suite at the base
was `snd3_6_equality_loop`: 3 `[OK]` at a58856d on c and cpp, and 3
`[OK]` at this slice on c and cpp. No check goes from `[OK]` to
`[FAILED]`.

Pins: `tests/tsymex_rfc0005_s8t_termination.nim`.
- (1) 12-operand chains in `if`, `let`, `symexAssert`, `while` and an
  `or` chain within 13 Z3 calls (RED: 2049 each); short-circuit kept in
  `if`, `or` and a mixed chain (a guarded read never raises, an
  unguarded one does); the hoisting-first-operand `while` guard (RED:
  `sxUnknown`).
- (3) a B4 offset promoted over `int`'s range (RED: no abstraction
  entry); its `OverflowDefect` at `high(int)` (RED: `sxRaised` with
  witness `(@[], -1)`, which in Nim raises `IndexDefect`, not
  `OverflowDefect`); the B4 hit still reachable, replayed.
- (2) a Q1/B0 offset promoted, its hit replayed and its `OverflowDefect`
  found (RED: the suite killed at 900 s in this test); a pair-loop offset
  promoted (RED: no entry, `beBudgetExhausted`); under `isExact` a
  scan-pair offset promoted and B7R-3's shape SAT within 2M units (RED:
  `sxUnknown`, "canceled").
- The `>= 168` floor.

Re-pinned:
- `phase15_CR2_cachekey` (167 -> 168).
- `phase15_A2a_chokepoint_audit`: the boolean and/or branch parses every
  operand in one loop, so exactly 1 line (was 2, LHS and RHS) carries the
  `A2b EXCLUSION (boolean and/or` marker on a bare `parseExpr(`.

*Different mechanisms, reported and not fixed here.*
- **Alternating `and`/`or` chains still multiply paths.** An operand
  with the other operator (`(a or b) and (c or d) and ...`) is lowered by
  its own recursive parse, whose guard forks two paths that both go on
  into the rest of the outer chain. m such operands with raising reads
  give 2^m paths. Nesting across operators would need the chain lowered
  as one decision tree.
- **A hoisting first operand in a `while` guard whose body has
  `continue`** still declines (`feUnsupportedOp`, R14 Case 2). The
  rotation is unsafe there and there is no `A` to split on.
- **An `isIntOffset` param `promoteSound` turns down stays an unstamped
  Int**: banned by the ban scan, unsigned, `isLoose`, or `isExact` with
  unchecked arithmetic. Under unchecked `isOptimised` the wrap scan bans
  any arithmetic it cannot prove, so a B4 offset with arithmetic stays an
  unbounded Int that does not wrap where Nim does. The bit-vector would
  wrap, but B4's `iekStrSubstr` bound declines a bit-vector (CR-17), so
  the fix is not a revert. It is pre-existing.
- **The false `OverflowDefect` at the base** (`sutAccOverflow`, witness
  `(@[], -1)`) is gone with the stamp. How the unstamped offset produced
  an `OverflowDefect` at all was not traced; no other shape was probed
  for it. *(Corrected by S8w: the finding's `raisedTypeId` was
  `IndexDefect`, not `OverflowDefect`. E6 surfaces a reachable Defect
  with its own type whatever the target, and `data[-1]` is a real
  `IndexDefect` that replays. See S8w's note.)*
- **`tsymex_snd3_6_equality_loop` is unverified on Windows.** Its
  `scripts/derive-ci-suites.ps1` skip entry is removed too (the list is
  now empty): it passes in under 65 s on Linux, and S8r's per-suite
  watchdog (`scripts/run-ci-suite.ps1`, 240 s) bounds it in the corpus
  shards and names it if it hangs. The next symex-mingw run is its
  Windows verification; no Windows runner ran it in this slice.

**As landed (S8t2, walker 168, no bump) — S8t broke the Windows build.**
symex-mingw at fa7e172 (run 36667380693) was red on two jobs, both inside
the Nim compiler while it expanded the symex macro: scan-tail
`tsymex_r6_nulwitness` (exit 1, about 5 s after the last import) and
corpus shard 2 `tsymex_rfc0005_s8t_termination` (0xC00000FD,
STATUS_STACK_OVERFLOW, still compiling). The Windows `nim.exe` main thread
has a 1 MB stack.

*Cause.* `emitStmt` turns the parsed IR into a builder expression with one
Nim call per IR node, so the builder's AST is as deep as the IR, and the
compiler semchecks it by native recursion. S8t's nested short-circuit
guards (`mkIf` / `mkBranch` / `mkBlock` per operand) add about 7 AST levels
per chain operand where D1c's chained guards were flat. The macro's own
recursion (`lowerShortCircuitParts`, `flattenShortCircuitChain`) runs in
the compile-time VM, whose calls do not use the native stack, and is not
the cause.

*Reproduced on Linux* with the compile under `ulimit -s` in the dev
container (`nim c --compileOnly`):

- `tsymex_r6_nulwitness` compiles at 256 KB at 29a4d26 and overflows
  (SIGSEGV) at 256 KB at 92d3970; both compile at 512 KB and 1 MB, so
  Linux frames are smaller than the Windows build's.
- A 40-operand chain with raising reads compiles at 1 MB at 29a4d26 and
  overflows at 1 MB at 92d3970.
- `tsymex_rfc0005_s8t_termination` overflows at 256 KB at 92d3970.

*Fix.* `boundEmittedDepth` (`dsl_parser.nim`) post-processes the body and
callee-table builders: any call subtree taller than `emitHoistHeight` (24)
is bound, innermost first, to a fresh `let` in a statement-list expression
and referenced by its symbol. The walk is iterative. Every call in a
builder is a pure `mk*` constructor over literals and bound symbols, so the
value built is unchanged, and a builder no taller than the bound is emitted
exactly as before. It runs after `placeDeclineScopes`, which reads the
builders as emitted. With it, the 40-operand chain, `nulwitness`,
`s8t_termination` and `D1c_shortcircuit` all compile at 256 KB.

*IR identity.* The IR `lowerShortCircuitParts` builds is untouched; only
its emission changed. The runtime-built `SymexProgram` was dumped
(`canonicalize(prog)` and the full `repr(prog)`) for every SUT that
`s8t_termination` (14), `D1c_shortcircuit` (7) and `nulwitness` (9) pass to
`symexFind`, at 92d3970 and with the fix: the dumps are byte-identical.
No walker bump, no gate.

*Guard.* `tsymex_rfc0005_s8t_termination` gains a 40-operand chain SUT: a
compile-time check that its raw builder is over 200 levels tall and the
emitted one at most `emitHoistHeight + 8`, and a run that solves it. Built
on the symex-mingw leg, the file is itself the 1 MB compile check. The
manual Linux check is the compile under a 1 MB stack:
`podman run ... bash -c 'ulimit -s 1024; nim c --compileOnly --threads:on
tests/tsymex_rfc0005_s8t_termination.nim'`.

**As landed (S8u, walker 169) — S8s's precision remainder.** The six
places S8s reported, plus soundness and fault gaps found on the way. Every
expected value was checked against the pinned toolchain (Nim 2.2.10, debug
build) by an oracle test that runs the SUT itself.

1. **`else`-covered constructor.** A variant constructor naming a tag only
   an `else` arm covers (`S8uVE(vk: u3B, ve: x)`) was
   `feUnsupportedExprKind`. The parser now builds the variant literal on
   the `else` arm, for the single-case variant and for each multi-variant
   axis. It still declines when no arm, explicit or `else`, covers the tag.
2. **Local `Table` / `HashSet`.** A callee building a local
   `Table[string, int]` or `HashSet[int]` (`var t: Table[string, int];
   t["a"] = n; result = t`) was `weInternalWalkerFault`: the uninitialised
   local lowered to no container, and `lower`'s `iekTableSet` /
   `iekSetIncl` asserted on the receiver. The local is now the empty
   container (the new `iekZeroValue`, `default(T)`), and `retBindEq` binds
   a table or set result (size, presence and data). Shapes the theory does
   not back (`Table[int, int]`, `HashSet[string]`) decline in-band with a
   scoped error, never a walker fault.
3. **`new(result)`.** `new(x)` on a local, `var` parameter or `result`
   now allocates exactly as `x = new T` does (`mkNewT`), so a callee's
   `new(result)` is a fresh heap cell whose fields are zero. `retBindEq`
   binds a `ref` / `ptr` result by address. The mismatch that faulted
   ("retBindEq: kind mismatch svRef vs svBV64") is now an in-band
   `feUnsupportedOpHavoc` backstop for any kinds that still disagree.
4. **`bool` discriminator.** A multi-variant with a `bool` axis allocates,
   constructs, zero-initialises and reassigns. The axis discriminator is an
   `svBool`; its tag constants go through `discConst`, which yields a bool
   for a `bool` discriminator and a bit-vector otherwise.
5. **Zero values.** An untouched `distinct` result is its base type's
   zero. A `ref` / `ptr` is `nil`. A backed `Table` / `HashSet`, alone or
   as a field, is the empty container. Unbacked container shapes keep
   having no zero value (`feUnsupportedOpHavoc`).
6. **Array element writes.** `a[k] = v` and `a[k] op= v` at a constant
   index `k` on an `array` whose index range starts at 0 rebuild the array
   with one element replaced (`fieldStep`'s new array step). Before, both
   were `feUnsupportedStmtKind`.

Found on the way:

- (a) The call cache replays a callee's path-condition delta, not its heap
  effects. Once a `ref` result binds, a second cached `mkNode(x)` would
  reuse the first call's cell, and the two results would alias. The cache
  now admits only a callee that left the allocation counters and heap
  handles unchanged (`heapUnchanged`).
- (b) `iekTableSet` stored 0 in place of a value that lowered as an
  unbounded Int (a promoted `int`). That was a wrong table content and so
  a potential false verdict. The value now converts to 64 bits
  (`bv64Operand`); any other kind declines.
- (c) `iekSetIncl` / `iekSetExcl` asserted their element was a 64-bit
  bit-vector (`weInternalWalkerFault` on an Int-promoted element). They
  now convert it the same way, or decline.
- (d) A table with a non-`string` key allocates as a declined, inert
  placeholder. A key read or write on it then lowered the key against a
  string prototype, and `coerceIntLit` raised (`weInternalWalkerFault`).
  Every key site now declines it with `seUnsupportedTableKeyType`.
- (e) A `bool` discriminator's reassignment (`isVariantReassignSymbolic`)
  and `discFromRhs` had no `svBool` arm.

- **Runtime.**
  - `defaultZero` / `defaultZeroTotal` cover `itTable` and `itSet` (backed
    shapes only, `containerZeroBacked`), `itDistinct` and `itRef` /
    `itPtr`.
  - `lower`'s `iekZeroValue` arm returns `defaultZero` when it is total,
    otherwise a fresh value and an in-band `feUnsupportedOpHavoc`.
  - `retBindWiredKinds` gains `svRef`, `svPtr`, `svTable`, `svSet`.
  - `containerRecvDeclined` replaces the table / set receiver asserts.
  - `variantLitArms` selects the `else` arm (key -1) when no explicit arm
    names the tag.
  - `heapUnchanged` gates call-cache admission.
  - `retBindKindsAgree` sends a top-level kind mismatch between a call's
    `retSym` and its returned value through the call-return drains'
    path-level `feUnsupportedOpHavoc` decline (a tainted fork), ahead of
    `retBindEq`'s lowering-sink backstop.
- **IR / parser.**
  - `iekZeroValue` (`zvTy`) has its emit, render (`default(T)`), canonical
    (`Ex<Zero:`), abstraction and defect-fork-scan arms.
  - `zeroValueForType` emits `iekZeroValue` for tables and sets, and
    recurses through `distinct`.
  - `fieldStep` takes `recv[<int literal>]` on an array whose index range
    starts at 0 (`arrayIndexFromZero`), bounds-checked.
  - The statement parser lowers `new(x)` to `mkNewT`.
- **Consumer-visible (for S11's migration note).**
  - **`sxUnknown` programs that now get verdicts:**
    - a variant or multi-variant constructor naming an `else`-covered tag
    - a callee building and returning a `Table[string, int]` or
      `HashSet[int]`
    - a `ref` result allocated with `new(result)`, or any `ref` / `ptr` /
      table / set callee result
    - a multi-variant with a `bool` discriminator
    - an untouched `distinct`, `ref` or container-holding result
    - an array element write at a constant index, `=` and `op=`
  - **Walker faults that are now scoped declines:** a non-string-keyed
    table's key access, an Int-promoted set element, a kind mismatch in
    `retBindEq`.
  - **Cache.** The canonical program form changes for any SUT with an
    uninitialised table or set local. The walker bump to 169 invalidates
    every symex cache entry.
- **Different mechanisms, reported and not fixed here.**
  - **Array low bound (false `sxUnsat`).** An index read on an array whose
    index range does not start at 0 ignores the low bound: with
    `var a: array[1..3, int] = [7, 8, 9]`, `a[1] == 7` is `sxUnsat`. The
    read selects position 1 of the Z3 array, not position 0. This slice's
    writes decline on such an array (`arrayIndexFromZero`) rather than
    compound the error; the read path is untouched.
  - **Array type aliases.** `type Arr3 = array[3, int]` classifies as
    `uninterp[__unsupported:Arr3]`, so a value of the alias is opaque.
  - **Anonymous `range` discriminator.** A variant whose discriminator is
    an inline `range[lo..hi]` (not a named type) fails at compile time in
    `dsl_typebridge.nim` ("node is not a symbol").
  - **Symbolic-index array write.** `a[i] = v` / `a[i] += v` with a
    non-constant `i` is still `feUnsupportedStmtKind`.
  - **Other container shapes.** Tables other than `Table[string, int]` and
    sets other than `HashSet[int]` still decline (scoped, in-band).
  - **Closure-returning callee.** A callee returning a closure
    (`proc mkF(t: int): proc(y: int): int`) is `weInternalWalkerFault`:
    `allocateSym(itUninterp)` raises ("uninterpreted-ref allocation lands
    with cluster E") when the call allocates its `retSym`. With S8u binding
    `Table`, `HashSet`, `ref` and `ptr`, every kind a callee can return
    through the composite-result `feUnsupportedOpHavoc` sites binds; the
    closure is the one shape that would reach them, and it faults first.
    Those sites keep their audit entries and are now reached only by a kind
    mismatch (`retBindKindsAgree`).
  - **Enum without ordinal 0.** An untouched result holding an enum whose
    first ordinal is 1 is, in real Nim, zero memory: ordinal 0, no value of
    the enum (probed). The walker's free `retSym` constrains the field to
    the enum's ordinals, so it excludes the value Nim actually returns. A
    label reading that field (`ord(v.a) == 0`) would be a false `sxUnsat`.
    The no-zero pins below use this type only with labels that do not read
    the field.

Pins: `tests/tsymex_rfc0005_s8u_precision.nim`. It covers:
- (1) an `else`-covered constructor, with a dead label (RED:
  `feUnsupportedExprKind`);
- (2) a callee's local `Table[string, int]` and `HashSet[int]`, witnesses
  and dead labels (RED: `weInternalWalkerFault`), and an unbacked
  `Table[int, int]` declining in-band (RED: `weInternalWalkerFault` from
  `coerceIntLit`);
- (3) `new(result)` with an untouched field's zero and a dead label (RED:
  `weInternalWalkerFault`);
- (4) a multi-variant with a `bool` axis, both axis values, replayed (RED:
  `weInternalWalkerFault`);
- (5) an untouched `distinct` result and one holding a `HashSet[int]` and a
  `Table[string, int]`, with dead labels (RED: `feUnsupportedOpHavoc`);
- (6) an array element's `=` and `+=` at a constant index, with dead labels
  (RED: `feUnsupportedStmtKind`);
- the `>= 169` floor.

Re-pinned, each checked against real Nim:
- `phase15_CR2_cachekey` pin (169).
- `r6_r6_emit_roundtrip`: the `iekZeroValue` arm, two sentinels (a table
  and a set) and their round-trip tests.
- The no-zero result pins moved from a `HashSet[int]` arm field (now
  modelled) to an arm field of an enum with no ordinal 0:
  - `r6_r2_zerodefault_result` T5h-4
  - `rfc0005_s6b_ops`
  - `rfc0005_s8l_exits`
- The composite-result havoc pins over a `Table` passed through a callee
  now check the bound result: `rfc0005_s6b_ops`'s dead targets are exact
  `sxUnsat`, its live target `sxUnsat` and its fresh pair exact `sxSat`,
  with no errors. The two free-`retSym` guards moved to the untouched
  no-zero result. `tot1_totality_corpus`'s A6-rider row left the §0
  corpus (the run is exact) for its own suite: `sxSat` with no errors, and
  a dead twin `sxUnsat`.
- `rfc0005_s6b_ops` (d): the `feUnsupportedOpHavoc` audit counts 14 sites.
  The two new ones are fresh: `iekZeroValue`'s fallback and `retBindEq`'s
  kind-mismatch backstop.
- `r6_n36_raise_class_audit`: two marked `raise newException` sites fewer
  in `runtime.nim` (`retBindEq`'s kind mismatch, `defaultZero`'s
  `itDistinct`), both category-c, and one marked `raise (ref Symex*)`
  fewer (`defaultZero`'s `itRef` / `itPtr`).
- `rfc0005_s8i_models` (4): the declined construction's arm field is now
  an enum with no ordinal 0 (a `ref int` one is modelled). A new pin
  checks the `ref` arm construction and its reassignment: `sxSat`, no
  errors, replayed.
- The Class-B `feUnsupportedStmtKind` trigger is now an array element's
  `+=` at a symbolic index (`q[b and 1] += b`, always in bounds):
  - `rfc0005_s3_monotonicity`
  - `rfc0005_s1b_kinds`
  - `rfc0005_s1c_verdict`
  - `augmented_assign`

**As landed (S8w, walker 171) — S8t's remainder.**

*Alternating `and`/`or` chains join.* The guard `if`s that
`lowerShortCircuitParts` synthesizes carry `ifJoin`
(`IRStmt.ifJoin`, rendered `ifj(`, canonical `St<Ij:`). For a one-arm
`ifJoin` with no `else` the walker walks the guarded arm, and
`mergeJoinPaths` (`runtime.nim`) joins the survivor with the skip path.
The join applies when there is exactly one survivor, the taint and heap
state are equal, and the arm's `pc`/`dspc` extend the base's. Env
entries the arm left alone are shared (`sameSV`, identity by hash-consed
handle and metadata). Differing scalars become `ite(cond, arm, skip)`:
bool, BV of the same signedness, float, and a stamped Int of the same
width and sign (with the interval hull). The arm's extra path facts
enter as `cond => facts`, in `pc` and in `dspc`. If anything else
differs, the two paths are returned unjoined, which is the pre-S8w
behaviour. The chain's short-circuit order is unchanged. Only the
paths after a guard are merged, and a raising read still forks its
Defect inside the arm. With 6 alternating pairs (`(a or b) and (c or d)
and ...`, `(a and b) or ...`, and in a `let`), the base made 133, 130 and
379 Z3 calls; this slice makes at most 16.

*A `while` guard with `continue` is rotated.* R14 Case 2 (the first
operand hoists) and Case 3 (an `or` guard, or another shape with a
preamble) declined when the body had a `continue`. Now they use
`mkRotatedContinueWhile` (`dsl_parser.nim`). The body goes into a
labelled block (S8m's break targets), and each of its `continue`s
becomes `break` out of that block (`retargetContinue`). So a `continue`
lands on the rotation's trailing guard refresh, and the next test sees
the loop's current state. Nested `while`s own their `continue`s and are
not entered. `retargetContinue` walks with a work list; it rewrites the
body in place and adds one labelled block, so the emitted builder grows
by a constant depth, which S8t2's `boundEmittedDepth` bounds like any
other. Rebased on S8t2, `s8w_remainder`, `s8t_termination`,
`r6_nulwitness`, `D1c_shortcircuit` and `r14_continue_guard` all compile
under `ulimit -s 256` (and 1024) in the dev container.

*A turned-down B4 offset is stamped and wraps.* `runSymexImpl` has an
`isIntOffset` param that `promoteSound` turns down (`offsetStamp`: the
ban scan, unsigned, or `isExact` with unchecked arithmetic). It is now
stamped with its own width and signedness and confined to its declared
range or its type's window (`intWindow`), with an `aeTypeRange`
abstraction entry (none for `uint64`, whose window does not fit an
`int64` interval). `lowerArith` wraps a stamped Int's result
(`wrapIntToWidth`) when the Nim operation wraps:
- unsigned `+ - *`;
- signed `+ - * div` when `acOverflow` is off (`currentArithWraps`).

The wrap is `ite(lo <= r <= hi, r, lo + (r - lo) mod 2^w)`, and it is
skipped when `r`'s interval already fits. Checked signed arithmetic
keeps its `overflowCondInt` forks. A bit operation or shift on a stamped
Int bridges at its own width and signedness (`stampedIntToBV`). Before,
a shift failed the walker's assertion, and a bit operation bridged
unsigned at 64 bits.

The same bridge now treats an unstamped Int (`.len`, `find`, `indexOf`,
`parseInt`) as a signed 64-bit `int`, or takes the other operand's
signedness against a BV. `(s.find('a') and -2) < 0` was a false
`sxUnsat` (CR-1a's `svIntToBV` stamps unsigned), and `s.find('a') shr 1`
was a walker fault.

*The base's `OverflowDefect` finding was a correct `IndexDefect`.*
At a58856d, `symexFind(sutAccOverflow, tRaisedExn("OverflowDefect"))`
returned `sxRaised` with `raisedTypeId` `IndexDefect` and witness
`(@[], -1)`. The same happens with `tIndexError()`, and with the
`start + 1` removed. E6 surfaces any reachable Defect with its own type
whatever the target, and `data[-1]` raises `IndexDefect` in Nim. S8t's
note and test comment read it as a false `OverflowDefect`; both are
corrected, and S8t's test now also checks the type. Probes at this tip
(B4, Q1, B3 and B6 shapes; `tIndexError` and
`tRaisedExn("OverflowDefect")`; `isExact` and `isLoose`) found no
`sxRaised` whose witness fails to replay as the reported type.

*Skipped-suite per-check comparison.* The skip list is empty (S8t
emptied it), so there is nothing to compare.

Pins: `tests/tsymex_rfc0005_s8w_remainder.nim`.
- (1) 6 alternating pairs in `if` (both nestings) and `let` within 16
  Z3 calls (RED: 133, 130, 379); guarded reads in an alternating chain
  never raise; an unguarded one raises and replays.
- (2) a hoisting-first-operand guard with `continue`: the exit after a
  `continue` is reached, a stale guard's extra iteration is dead, the
  guarded read never raises, and `r14_case2_degrade`'s shape is SAT; an
  `or` guard with `continue` (Case 3) is SAT, its read never raises
  (RED: `sxUnknown`, `feUnsupportedOp`).
- (3) under unchecked `isExact` and `isOptimised`, `start + 1 < start`
  and `start * 4 < 0` are SAT at the wrap (RED: false `sxUnsat`); the
  B4 hit replays. A bit-banned offset's `OverflowDefect` is found, typed
  and replayed (RED: `sxUnknown`); its hit replays. `(start and -2) < 0`
  is SAT (RED: false `sxUnsat`); a shift on a banned offset is SAT (RED:
  walker fault). `(s.find('a') and -2) < 0` and `(s.find('a') shr 1) < 0`
  are SAT (RED: false `sxUnsat`, walker fault).
- (4) B4 with a negative offset under both targets: `sxRaised`,
  `IndexDefect`, replays as `IndexDefect`.
- The `>= 171` floor.

Re-pinned:
- `phase15_CR2_cachekey` (169 -> 171; 170 is S8v's).
- `r14_case2_degrade` test 1 and `r14_continue_guard` R14-6: `sxUnknown`
  -> `sxSat`, with the witness checked against Nim's loop.
- `rfc0005_s8t_termination`: the B4 `OverflowDefect` test's comment,
  plus a `raisedTypeId == "OverflowDefect"` check.
- `r6_n27_placeholder_read_audit`: `sameSV`'s svSeq arm has 2 marked
  identity lines (74 -> 76 in `runtime.nim`).

*Different mechanisms, reported and not fixed here.*
- **`isLoose` leaves an `isIntOffset` param unstamped.** This is by
  design: ADR-0001's `isLoose` is opt-in unsound, and the offset is
  treated like every other `isLoose` int. Its shifts and masks bridge as
  a signed 64-bit `int`.
- **The join declines on anything but scalars.** If an operand's
  hoisted code writes a string, seq, tuple, heap cell or ref, allocates,
  or leaves more than one survivor, the two paths go on unjoined. An
  alternating chain whose operands do that still forks 2^m paths.
- **B6 with a negative offset is `sxUnknown`** (`beBudgetExhausted`,
  k-unroll 5) for `tIndexError`. It is a precision gap, not a false
  verdict. The pair loop's guard stays satisfiable past the bound.
- **`data.len.uint` in an unsigned B4 scan declines on its path**
  (`lowerConvIntReinterpret`, `feUnsupportedOpHavoc`: a same-width
  signedness reinterpret of the Int-sorted `len`). The target stays SAT
  with a replaying witness, and the decline is S6b's scoped one. A
  `uint` offset's wrap (`start + 1 < start` at `high(uint)`) is SAT.
- **Unchecked `low(T) div -1` is modelled as its wrap, `low(T)`.** In C
  it traps (x86 `idiv`, SIGFPE) rather than wrapping. Before S8w it was
  modelled as the out-of-window `-low(T)`, so neither form matches the
  trap. A witness that depends on it would fail to replay.

**As landed (S8aa, walker 172) — S8w's remainder.**

*A zero divisor with overflow checks off is a trap.* Nim emits its
`div`/`mod` zero check only under `overflowChecks`. With it off (`{.push
overflowChecks: off.}`, or `acOverflow` off in the model), `x div 0` and
`x mod 0` reach the C division, which traps: probed on the pinned
toolchain, debug build (the build a witness is replayed in), c and cpp,
both print `SIGFPE: Arithmetic error.` and abort, with no `except` arm
run. The non-replaying witnesses at the base: with `arithChecks:
{acDivByZero, acRange}`, `x div y` returned `sxRaised` `DivByZeroDefect`
at `(0, 0)`; with `arithChecks: {}`, `x div y == -1 and y == 0` and `x mod
y == x and y == 0` were `sxSat` at `(0, 0)`. Each witness aborts the
process on replay. `lowerArith` now routes a zero divisor into S8i's
survivor-only trap sink (`arithTrapConds`) whenever `currentArithWraps`
holds, and into the `DivByZeroDefect` fork (gated on `acDivByZero`)
only with `acOverflow` on. The checked build still raises
`DivByZeroDefect`, and that witness replays.

S8w's suspect, `low(T) div -1`, was already modelled at 32 and 64
bits: S8i confines the path off it (`arithTrapConds`), and the probe
confirms C traps there (`low(int) div -1`, `low(int) mod -1`, and the
`int32` pair all abort). At 8 and 16 bits C promotes to `int`, so
`low(int8) div -1 == low(int8)` and `mod` is 0, which is the wrap the
model gives. None of the shapes tried (let, callee, while, chain,
return, assignment, stamped B4 offset, range, `parseInt`) reproduced the
"wrap to `low(T)`" S8w recorded. They are pinned. No other operator has
the trap shape: probed the same way, `shl`, `shr` and `ashr` by a count
>= the width or negative never trap (x86 masks the count: `5 shl 64 ==
5`, `5 shl 65 == 10`), and unsigned division traps only at zero.

*The short-circuit join covers store shapes and multi-path operands.*
`mergeJoinPaths` no longer requires one survivor with equal heap state.
- Env values that differ are joined by `joinSV`: `ite` over the
  string term, the seq's array term and length (neither side a
  placeholder, equal element type), refs and pointers of the same
  pointee, and tuples and arrays field by field, on top of S8w's
  scalars.
- Heap arrays that differ are joined key by key (`ite` over the
  array terms). The heap key set, live refs, allocation counters,
  freshness count and nil-deref flag must be equal (`sameHeapMeta`).
  `heapDepth` is a per-path deref budget, not program state, so the
  join takes the max.
- n survivors with guards `G_i` (their `pc` tail and `dspc` tail
  past the base) join as a fold `ite(G_1, v_1, ite(G_2, v_2, ...))`,
  with `cond => OR R_i` in `pc` and `cond => OR G_i` in `dspc`. One
  survivor is S8w's join unchanged.
The chain's own guard temporary keeps S8w2's connective form (`cond and
v` / `e or v`, not an `ite`); every other entry goes through `joinSV`.
Anything else (allocation in an operand, unequal taint, a table, set
or variant that differs) still returns the paths unjoined. With 6
pairs the base made 114 (string), 378 (seq), 296 (heap cell) and 732
(two-survivor callee) Z3 calls; this slice makes at most 16 (24 for the
two-survivor callee).

*B6 with a negative start raises.* `iekStrInOptionRegion`'s member test
required nothing of the start. Z3's `str.substr` at a negative offset
is "", which the region accepts, so a negative start was certified
defect-free and the first scan's `IndexDefect` (`s[-1]`) was never
walked: `sxUnknown` (`beBudgetExhausted`) when the fallback's unroll
ran out, and a false `sxUnsat` when it did not. The member test now
conjoins `start >= 0`. A negative start is `sxRaised` `IndexDefect`,
and the witness replays.

*A same-width reinterpret of an Int-sorted value is modelled.*
`lowerConvIntReinterpret` on an `svInt` (`data.len.uint`,
`s.find(c).uint`) declined (`feUnsupportedOpHavoc`). It now reduces
the value into the target window (`lo + (v - lo) mod 2^w`, skipped
when the interval already fits) and stamps the target width and
signedness. So a `len` stays itself and `find`'s -1 becomes
`high(uint)`. Pinning it exposed a literal bug: at an unsigned 64-bit
`svInt` proto, `coerceIntLit` built a `uint64` literal above
`high(int64)` from its two's-complement `int64` (`high(uint)` as -1),
so `s.find('a').uint == high(uint)` was a false `sxUnsat` and
`s.len.uint > high(uint) - 2` a false `sxSat` (with the reinterpret
modelled and the literal not yet fixed). Such a literal is now
`ival + 2^64`. The same bug reached S8w's stamped `uint` offsets.

Pins: `tests/tsymex_rfc0005_s8aa_remainder.nim`.
- (1) unchecked `x div 0` (signed, `isOptimised` and `isExact`;
  `uint32`) is not a `DivByZeroDefect` (RED: `sxRaised` at `(0, 0)`);
  with no checks, no execution continues past `x div 0` or `x mod 0`
  (RED: `sxSat` at `(0, 0)`). The checked build's `DivByZeroDefect` is
  found and replays. `low(T) div -1` and `mod -1` at 32 and 64 bits
  stay dead, `low(int8) div -1` wraps and replays, a safe division keeps
  its quotient, and a stamped B4 offset divided by -1 traps at
  `low(int)`.
- (2) 6-pair chains whose operands append to a string, append to a
  seq, add to a heap cell, rebind a local ref, rebind a ref in a heap
  cell, or leave two survivors, each within 16 (24) Z3 calls, with
  their witnesses checked. The string chain's impossible length is
  `sxUnsat`. A raising read on one of two survivors still raises and
  replays.
- (3) B6 with a negative start: `sxRaised` `IndexDefect` that replays,
  also on a short region (RED: `sxUnknown`, `beBudgetExhausted`).
- (4) the unsigned B4 scan's hit with no decline, replayed (RED:
  `feUnsupportedOpHavoc`); `find`'s -1 as `high(uint)` (RED: decline,
  then false `sxUnsat`); `len.uint == 3` SAT and `s.len <= 4 and
  s.len.uint > high(uint) - 2` UNSAT (RED: decline; the unbounded form
  was a false `sxSat` before the literal fix). Unbounded, the second is `sxUnknown` (`beSolverUndef`,
  `maxSeqLen`), which is honest.
- The `>= 172` floor.

Re-pinned:
- `phase15_CR2_cachekey` (171 -> 172).
- `r6_n27_placeholder_read_audit`: `joinSV`'s svSeq arm has 5 marked
  lines, a placeholder guard and the reads it gates (76 -> 81 in
  `runtime.nim`).
- `rfc0005_s6b_ops`: the `feUnsupportedOpHavoc` site count loses the
  reinterpret (14 -> 13).
- `r6_b2_intwidth` item2-1/item2-2: `uint(q)` on a B4 scan's
  Int-sorted result was pinned as S6b's decline (`sxUnknown`,
  `feUnsupportedOpHavoc`); it is now `sxSat` with no decline, and the
  witness is checked against Nim's scan.

*Different mechanisms, reported and not fixed here.*
- **A `var` ref parameter written by a callee is a walker fault.**
  `proc noteR(cur: var Box, b: Box) = cur = b`, called once and with no
  chain, returns `sxUnknown`: `seUnsupportedCompoundSortLeaf`, then
  `weInternalWalkerFault` ("sort mismatch at array store value:
  expected (_ BitVec 64), got Ref..."). It is sound (the path is
  tainted), and the same at the base. The join pins use a local rebind
  and a heap-cell rebind instead.
- **Exact `start div y` with a stamped Int offset and a BV divisor ran
  past 900 s** (a probe; nonlinear Int division under the wrap). It is
  not pinned here.
- **The join still declines** on allocation inside an operand and on
  tables, sets, variants and distinct values that differ.
- **A shift by a count outside `0 ..< width` is modelled as Z3's
  `bvshl`/`bvlshr`/`bvashr` (0 or all sign bits)**, but the machine
  masks the count (`5 shl 64 == 5`). It is C UB and does not trap, so a
  witness that depends on it can fail to replay and a verdict on it can
  be wrong. It is not this slice's trap shape.
- **`acDivByZero` off with `acOverflow` on** leaves the continuation
  unconstrained at a zero divisor: the user turned the check off.
  That is a policy choice, left as it is.

**As landed (S8v, walker 173) — S8r's termination remainder.** Both
items were measured on Linux against the Z3 4.13.4 shared library (the
symex-mingw leg's build), as the peak RSS and user time of the test binary.

*1. `checkCapped` step 2 on the `indexof` form.* Step 1c poses the caps
against the query with no sequence theory (`querySolver`'s `seqTheory =
false`). That treats every string function as uninterpreted, so `str.len(x)` and `str.indexof(s, t,
i)` could take any integer. S8r's range-checked search is `idx =
str.indexof(s, ":", 0)`, with `idx != -1`, `idx < len(s)` and `idx`
outside `0..1000`. Under the 128 cap the theory-free query still had
`idx <= -2`, so step 1c was SAT and step 2 ran the sequence theory under
the cap's assumption literal. On 4.13.4 that is a string search.
Step 1c now also asserts `seqRangeFacts`, the range the theory gives each
such term, and checks the query with the facts twice: first without the
caps, where an UNSAT is the query's own (`zsUnsat`), then with them, where
an UNSAT is the cap decline as before. The facts are:
- `str.len(x) >= 0`;
- `r = str.indexof(s, t, i)`: `r = -1`, or `0 <= r`, `i <= r` and `r +
  len(t) <= len(s)`;
- `r = str.last_indexof(s, t)`: `r = -1`, or `0 <= r` and `r + len(t) <=
  len(s)`.

The brief's `str.indexof < str.len` is wrong for an empty needle, since
`str.indexof(s, "", len(s)) = len(s)`, so the bound subtracts the needle's
length instead. Each fact is valid in the theory, so the facts never
refute a real model. The pin checks each fact's negation against the
theory. `str.len` and `str.indexof` are matched by
decl kind, which `SeqCapKinds` probes from the linked Z3. `last_indexof` is
matched by name, as in `seqLenCaps`.

*Only step 1c takes the facts, not step 1b.* The first cut
(`df5b9bf`/`ce99594`) asserted them in every theory-free query, 1b
included. That is sound too, since a 1b UNSAT stays the query's own. But
the gate killed `tsymex_r6_b1_stringbacked` and `tsymex_r6_n36_raise_degrade`
(rc 137). The machine was at load 40 on 6 cores. Alone, both pass at base
and at the slice, so the kill was load. The deterministic count is what
moved. On Z3 5.1, with `-d:symexQueryStats`:

| `b1_stringbacked` | queries | total `rlimit` | user |
|---|---|---|---|
| aa800f3 | 57 | 60.4M | 283 s |
| facts in 1b and 1c | 59 | 115.5M | 457 s |
| facts in 1c only (`381a26e`) | 57 | 60.4M | 287 s |
| facts in 1c, uncapped check first (landed) | 57 | 60.4M | 286 s |

In B1-1, a SAT query that took 18.8M units at base ran out its 20M budget
with the facts in 1b. The walk then needed two more queries to reach the
same verdict. The facts' terms stay in the walk's shared context, and Z3's
cost follows what the context holds (S8o). Step 1c runs only after step 1
came back UNSAT and 1b found no theory-free refutation. So in 1c the terms
reach the context only on the way to a cap decline or to step 2.
`n36_raise_degrade` has 88 queries in all four runs, with the same 8
`[OK]`. Its total was 605M units at aa800f3, 322M with the facts in 1b
and 1c, 269M with the facts in 1c only, and 282M as landed.

*The facts alone are checked first.* `381a26e` (pushed rebased as
`0bb545b`) asserted the facts only beside the caps. The symex-mingw leg
(run 36695764841) then failed the scan-lift UNSAT companions:
`q1_scanlift` Q1-P1b, Q1-1b and Q1-2b, `r6_b5_chained` B5-1b and B5-3b,
`r6_b7r_bytescan` B7R-1b, `phase15_A1_loopguard`, `q1_sibling_collision`,
`r6_b4_readcstring`, `r6_n31_block_counter`, `r6_r3_svint_overflow` and
`retest_char_needle`. Each came back `sxUnknown` where `sxUnsat` was due.
They reproduce on Linux against 4.13.4, `q1_scanlift`'s three on 5.1
too, and pass at 219f152. A scan's
closed form clamps its index at the bound, so `i > s.len` is UNSAT, but
theory-free the refutation needs `str.indexof`'s upper bound, a fact.
With the facts only beside the caps, step 1c's UNSAT read as the cap's,
where step 2's core had found the query's own UNSAT. The gate had run on
`ce99594` (facts in 1b), so it never saw this arrangement. With the
uncapped check, all twelve suites pass on 4.13.4. It runs on the same path
as step 1c, after the facts are built, so `b1_stringbacked`'s count is
unchanged (table above).

On 4.13.4 at aa800f3 against this slice:

| suite | aa800f3 | S8v |
|---|---|---|
| `rfc0005_s8r_theoryfree` | 53 s wall, 1,217 MB, 40 s user | 0.1 s wall, 53 MB, 0.0 s user |
| `163rev_intoffset_range` | 115 s wall, 1,412 MB, 83 s user | 0.3 s wall, 57 MB, 0.2 s user |

Every check passes on both shas. All three of `intoffset_range`'s range-checked searches
are now step 1c declines.

*2. `tsymex_r4_strip` was not slower at aa800f3.* S8r measured it at its
pre-fix head. Measured again on 4.13.4 (the machine under gate load, so
user time is the comparison):

| sha | user |
|---|---|
| a696d80 (S8r's number) | 21 s |
| 671fef5 | 47 s |
| 674b3b4 (d1c0f82's parent) | 51 s |
| aa800f3 | 22 s, 26 s, 26 s |
| S8v | 25 s, 27 s |

The source difference between 674b3b4 and d1c0f82 is only S8r's fix. The
cost was S8r's first mechanism: on 4.13.4, step 1b ran the full sequence
theory because the default solver ignores `smt.string_solver = none`.
`strip`'s capped UNSATs paid for that search. Nothing is left to fix.

Pins: `tests/tsymex_rfc0005_s8v_termination.nim`.
- (1) The `indexof` query under the 128 cap is UNSAT as step 1c poses it
  (no sequence theory, with the facts). RED: `zsSat`, on 5.1 as well as
  4.13.4. Two companions:
  - without the cap it stays SAT (a 1002-byte string satisfies it);
  - an empty needle at `len(s)` is not refuted.
- (1') Each emitted fact's negation is UNSAT with the theory (RED: no
  facts).
- (2) End to end, S8r's range-checked search is a `maxSeqLen` decline
  from step 1c under `seqQueryRLimit = 200_000`. RED on 4.13.4: step 2
  ran and declined with "whether the query is UNSAT on its own was not
  decided: Z3: canceled".
- (3) A loop scan's index past `s.len` is `sxUnsat`. RED at `381a26e`
  on 4.13.4 and on 5.1 (a `maxSeqLen` decline).
- The `>= 173` floor.

Re-pinned: `phase15_CR2_cachekey` (172 -> 173; 170 was reserved for S8v, and S8w and S8aa landed first at 171 and 172).

*Different mechanisms, reported and not fixed here.*
- **Step 1c declines some queries that are UNSAT on their own.** Suppose a
  query needs the sequence theory to be refuted, but its theory-free form
  (now with the range facts) is refuted only by the cap. Step 1c declines
  it with the cap message. Before S8r, step 2's core could have proven it
  UNSAT. The range facts make this happen more often, because more
  step 1c queries now hit the cap. An example is `str.indexof(s, ":",
  0) > 200 and not str.contains(s, ":")`. Deciding these again would mean
  running step 2 behind 1c's UNSAT with a bounded budget. That brings back
  the 4.13.4 string search this slice removes.
- **Other sequence functions stay unranged.** `str.at`, `str.substr`,
  `str.to_code` (`-1..255` under the byte domain), `str.to_int` (`>= -1`)
  and `str.++` (`len(a ++ b) = len(a) + len(b)`) get no facts. No
  measured query needed them. A cap conflict that runs through one of them
  still reaches step 2.

**As landed (S8ae, walker 174) — S8v's remainder.** Both items are in
`seqRangeFacts`, the facts step 1c asserts beside its theory-free query.
Step 2 is unchanged and still never runs behind a step 1c UNSAT.

*1. UNSAT through a relation between two functions.* `s.find(':') > 200
and ':' notin s` lowers to `str.indexof(s, ":", 0) > 200 and not
str.contains(s, ":")`. With the theory it is UNSAT: a `contains` that is
false makes `indexof` -1. Theory-free the two are unrelated. S8v's range
fact lets `indexof > 200` through only when `len(s) > 200`, so the
uncapped fact check is SAT and the capped one UNSAT, and step 1c declined
it on the cap. The same held for `s.startsWith("abc") and s.find("abc")
> 150`, `s[1..2] == "ab" and s.find("ab") > 150`, and `s[140] == ':' and
':' notin s`. All four were `sxUnknown` at d9ea440, on Z3 5.1 and 4.13.4.

The fence offered two ways to decide them. Both were measured.

- *A bounded step 2 behind step 1c's UNSAT.* This was measured with a
  probe build that ran step 2 under `rlimit` X after each step 1c cap
  decline and took its answer when the core was empty. Its core decided
  the `contains` pair. But on the `startsWith` and slice shapes it named
  the cap, as it did before S8r (Z3's cores are not minimal), so those
  stayed declines. `rlimit` does not bound it on a query that is SAT only
  past the cap:

  | Z3 | suite / query | X | slowest step 2 | peak RSS |
  |---|---|---|---|---|
  | 5.1 | `s.len > 210 and s[205] == 'x'` | 50k | 0.04 s | 62 MB |
  | 5.1 | same | 200k | 49.1 s | 1,182 MB |
  | 4.13.4 | `rfc0005_s8r_theoryfree` | 50k | 0.48 s | 83 MB |
  | 4.13.4 | same | 200k | 4.7 s | 611 MB |
  | 4.13.4 | same | 1M | 61.2 s | 9,064 MB |
  | 4.13.4 | `163rev_intoffset_range` | 1M | 72.6 s | 9,084 MB |

  Without the probe the three suites take 0.3 s. No X both decides the
  prefix and slice shapes and stays bounded, so this was not landed.
- *A sound theory-level refutation (landed).* The facts now also link
  two functions over the same haystack `s` and needle `t`. A link is
  made only when both terms are already in the query, so no
  `str.contains` term is built that the query does not hold:
  - `str.contains(s, t)`, `str.prefixof(t, s)`, `str.suffixof(t, s)`:
    `len(t) <= len(s)`;
  - `str.indexof(s, t, i) >= 0` implies `str.contains(s, t)`, and with `i
    = 0` the converse;
  - a prefix `t` has `str.indexof(s, t, 0) = 0`;
  - a prefix or suffix is contained;
  - a piece `p` of `s` at `i` (`str.at(s, i)`, `str.substr(s, i, n)`)
    with a root equality `p = t` makes `t` contained. With `0 <= i <
    len(s)` it also gives `0 <= str.indexof(s, t, j) <= i` for `0 <= j <=
    i`.

  A needle is matched by AST id. A char needle (`needleAsStr`'s
  `str.from_code(bv2nat(#x3a))`) is matched as the literal it folds to,
  which is what a byte test's character form compares against. The
  uncapped fact check now refutes all four shapes. That UNSAT is the
  query's own, so they are `sxUnsat` again, with no sequence-theory
  search at all.

  There is no `seq.last_indexof` link. A query holding one never
  reaches step 1c: `checkCapped` decides it by the uncapped step 3, as
  before (`s.rfind(':') > 200 and ':' notin s` was already `sxUnsat`).

*2. Range facts.* These are added:
- `c = str.at(s, i)`: `len(c) = 1` when `0 <= i < len(s)`, else 0.
- `r = str.substr(s, i, n)`: `len(r) = min(n, len(s) - i)` when `0 <= i <
  len(s)` and `0 < n`, else 0.
- `k = str.to_code(c)`: `k >= -1`, and `k >= 0` iff `len(c) = 1`. `k <=
  255` holds when `c` is `str.at` of a byte leaf, a string whose
  byte-domain constraint is one of the query's roots (`byteLeafIds`,
  factored out of `seqLenCaps`). That bound holds in every model of the
  query, not of the theory alone. With no byte-domain root no upper
  bound is claimed.
- `v = str.to_int(x)`: `v >= -1`.
- `x = y` over sequences: `len(x) = len(y)`.

The last fact was not on the fence's list, but without it the others see
nothing. Theory-free, Z3's rewriter folds `str.len` of a literal to a
numeral, so `str.at(s, 200) == "x"` never reached the length of
`str.at(s, 200)`. The rewriter folds `str.len(a ++ b)` to `len(a) +
len(b)` too, with the theory off. So `str.++` needs no fact of its own:
`len(s ++ t) > 300` under two 128 caps was already a step 1c UNSAT at
d9ea440. What it lacked was the equality. `x == s & t and len(x) > 300`
is now UNSAT under the caps on `s` and `t`, where it was SAT theory-free.
A `str.++` branch was written and then removed, since the rewriter made
it vacuous.

*Validity.* On free operands Z3 proves most facts' negations UNSAT with
the theory. It leaves a prefix's first index, the pieces' index bounds and
the byte bound (even beside the byte-domain root) `unknown` within 5M
units. The pin therefore checks each fact two ways against the linked
Z3's own semantics:
- its negation is never SAT with the theory;
- it rewrites to `true` on every ground instance with strings over `{"a",
  "\xff"}` of length at most 3 and integers in `-1..4`.

A mutant `at` fact (`i <= len(s)`) fails both checks.

Termination, measured against d9ea440 on the test binary built with
`-d:symexQueryStats`:

| Z3 | suite | wall (base / slice) | peak RSS | Z3 rlimit units |
|---|---|---|---|---|
| 5.1 | `r4_strip` | 114.8 s / 117.0 s | 268 / 268 MB | 20,028,658 / 20,031,362 |
| 5.1 | `q1_scanlift` | 4.6 s / 3.4 s | 64 / 63 MB | 3,124,577 / 3,124,577 |
| 5.1 | `r6_b5_chained` | 2.9 s / 3.1 s | 77 / 70 MB | 1,405,871 / 1,608,521 |
| 5.1 | `rfc0005_s8r_theoryfree` | 0.1 s / 0.1 s | 50 / 50 MB | 39,202 / 39,202 |
| 5.1 | `rfc0005_s8v_termination` | 0.2 s / 0.2 s | 62 / 62 MB | 43,233 / 43,233 |
| 5.1 | `163rev_intoffset_range` | 0.3 s / 0.5 s | 63 / 63 MB | 164,217 / 164,217 |
| 4.13.4 | `r4_strip` | 41.6 s / 43.1 s | 76 / 76 MB | 20,058,845 / 20,059,931 |
| 4.13.4 | `q1_scanlift` | 2.8 s / 3.3 s | 61 / 62 MB | 2,972,540 / 3,152,948 |
| 4.13.4 | `r6_b5_chained` | 2.1 s / 3.9 s | 72 / 73 MB | 1,377,412 / 1,573,533 |
| 4.13.4 | `rfc0005_s8r_theoryfree` | 0.1 s / 0.1 s | 52 / 52 MB | 28,904 / 28,904 |
| 4.13.4 | `rfc0005_s8v_termination` | 0.2 s / 0.3 s | 64 / 64 MB | 33,016 / 33,016 |
| 4.13.4 | `163rev_intoffset_range` | 0.3 s / 0.4 s | 57 / 57 MB | 128,133 / 128,133 |

Wall times were taken on a loaded host (load average about 25) and move by
up to a second either way. The rlimit totals (`-d:symexQueryStats`) are
deterministic, and the query and assert counts are identical in every row.
The extra facts cost `r6_b5_chained` 14% more solver work on both
versions and `q1_scanlift` 6% on 4.13.4. No query changed outcome, and none
approaches a budget.

Pins: `tests/tsymex_rfc0005_s8ae_remainder.nim`.
- (1) End to end, `sxUnsat` for the four shapes above. RED at d9ea440: a
  `maxSeqLen` decline on each, on Z3 5.1. Two companions:
  - `find > 5 and in` stays `sxSat`;
  - `(s & t).len > 300` stays a `maxSeqLen` decline.
- (1) The example query is UNSAT theory-free with the facts and no cap.
  RED: SAT.
- (1') Each relational fact is valid, by the two checks above. RED: the
  facts were missing.
- (2) Step 1c posed on its own (theory-free, facts, caps): `str.at`,
  `str.substr`, `str.to_code` past the cap, the byte bound, the
  no-byte-domain companion, `str.to_int < -1`, and the concatenation
  equality. RED at d9ea440: SAT for each, except the `str.++` case, whose
  first RED form (`len(s ++ t)`) passed at base and was replaced by the
  equality form. Each companion is SAT without the cap.
- (2') Each range fact is valid, by the same two checks.
- (2) End to end, `(s & t).len > 300` under `seqQueryRLimit = 200_000` is a
  step 1c decline, with no "was not decided".
- The `>= 174` floor.

Re-pinned: `phase15_CR2_cachekey` (173 -> 174).

*Different mechanisms, reported and not fixed here.*
- **The links are syntactic.** A needle is linked to a `contains`,
  `indexof` or piece only through the same AST, or through the literal
  a char needle folds to. A chain of equalities (`p = y`, `y = t`) or a
  computed needle that is equal but not identical gets no link. Such a
  query is still a step 1c cap decline when it is refuted only through
  the relation.
- **Relations not covered.** No fact relates `str.replace_all`, regex
  membership (`str.in_re`) or `str.from_int` to the other functions.
  None relates `str.indexof` from a nonzero start to `str.contains` in
  the converse direction, and none covers word equations (`s = a ++ b`
  with a `contains` on a part). A query refuted only through one of these
  is still a step 1c cap decline. Each one needs its own valid fact.
- **`seq.last_indexof` queries skip step 1c altogether.** They go to the
  uncapped step 3 (S8k's `lastIndex`), which is the one place the
  uncapped sequence theory still runs. That is unchanged here.

**As landed (S8y, walker 176) — the n36_raise_degrade / s1c_verdict
runtime.** `tsymex_r6_n36_raise_degrade` (8 OK, unchanged) took ~992 s
standalone at ec1519c, past the sweep's 900 s kill, and
`tsymex_rfc0005_s1c_verdict`'s N36-shape test ~640 s. Both walk the same
readCString pair loop, and every hit of the target past it is tainted.

*Bisect.* Measured by Z3 `rlimit` for every check in `checkCapped`, not by
wall time: on the shared host (load 15-30 on 6 cores) the same query
sequence took anywhere from 467 s to 756 s.

| sha | landing | N36-1 units | N36-1 exhausted 10M halves | s1c N36 test |
|---|---|---|---|---|
| 857b9b1 | S8s | 50.8M | 4 | 34.8M, 1 |
| 29a4d26 | S8r | 84.1M | 8 | 71.3M, 6 |
| 5509ef0 / ec1519c / 219f152 | S8t / S8t2 / S8u | identical to 29a4d26 (same md5 for the whole suite) | 8 | 6 |

*Mechanism.* S8r's step 1c ran in the walk's Z3 context: ten extra
checks per test, all SAT, deciding nothing. Z3 keeps what a check built
in its context, and later checks there start from it (`checkCapped`'s doc
comment). After those checks the pair loop's 3- and 4-iteration target
solves (0.27M and 2.06M units before S8r) ran out of both halves of
their 20M budget. With 1c removed, or moved to a context of its own, the
walk's query sequence is 857b9b1's unit for unit. That isolation
(prototyped as 4d34954, not landed) did not survive S8v: S8v's range
facts build terms in the walk's context, and on S8v's a061df3 the
isolation took n36 from 49.6M/42.8M units per test to 70.3M/70.3M (s1c
from 88.0M to 66.7M). On this tip, with the floor fix below, it changed
N36's units by less than 1%. It is not landed. What did not move with
any of it is the floor: two five-iteration exit hits per test (the break
on a fifth empty key, and the unroll-bound survivor), each spending its
whole 20M tainted budget, about 80% of the suites' CPU, before and after
S8r.

*Floor, replayed.* The five-iteration queries (q103: four pairs then an
empty key; q106: five pairs), dumped before their check and replayed in
fresh contexts under 10M units (one model-search half; Z3 5.1):

| variant | q102 (4 pairs) | q103 | q106 |
|---|---|---|---|
| as emitted | SAT 3.8M | out | out |
| `random_seed=1` | SAT 3.2M | out | out |
| `smt.seq.split_w_len=false`, `smt.relevancy=0`, `smt.arith.solver=2`, `smt.phase_selection=0`, `encoding=ascii` | | | out in every case |
| byte-domain regex dropped on substring-defined strings (NR) | | SAT 2.5M | out |
| each `str.indexof(s, "\0", i)` a fresh Int, with `s = pre ++ x ++ "\0" ++ post`, `len(pre) = i`, `ix = i + len(x)`, `"\0" notin x` (split) | SAT 1.3M | SAT 9.0M | SAT 5.7M |
| split plus chain facts (`pre_j = pre_i ++ x_i ++ "\0"` when `start_j = ix_i + 1`) | SAT 0.71M | SAT 4.2M | SAT 4.7M |
| split plus chain plus NR | SAT 0.64M | SAT 1.26M | SAT 4.66M |
| `str.prefixof("a\0" x 8, s)` (most of the witness given) | | SAT 9.0M | |

The split is an equivalence for a one-character needle `c`: `indexof(s,
c, i) = ix >= 0` holds exactly when `s` has a `c` at `ix >= i` with none
in `s[i, ix)`, which is the split's `pre`/`x`/`c`/`post` decomposition
with `len(pre) = i` and `c notin x`. The `-1` arm is `c notin s[i..]` or
`i` out of range. It is the only variant that makes q106 SAT, and only
at about half the budget. It is a lowering change of its own, so it is
slice S8ag.

*Fix.* Two changes, walker 175 -> 176:
- **(a) Implied byte-domain constraints dropped** (`dropImpliedByteDomains`,
  `checkCapped`, after `seqLenCaps`). A string whose root `x in
  (\x00..\xff)*` is implied by a definition `x == t` in the query, `t`
  built by `str.++` / `str.substr` / `str.at` from byte literals and from
  strings whose own byte-domain constraint stays, loses that constraint.
  Every character of `t` is one of those characters, so the two queries
  have the same models. A justifying string is never itself dropped, and
  a definition under a disjunction justifies nothing.
- **(b) A tainted hit at least as deep as an exhausted one is declined.**
  `Path.loopIters` records, for each `while` a path ran through, how many
  times its latest execution entered the body. It is set at the loop's
  forks and inherited below them, and a closure return merge joins the
  caller's. When a tainted target-hit solve runs out of budget
  (`rlimit` spent >= the solve's bound), its depths go to
  `WalkCtx.budgetOutDepths`. A later tainted hit at least as deep in each
  of those loops is not solved: `solveTargetHit` returns `sxUnknown`, and
  the caller records the same classified `beSolverUndef` a solver unknown
  gets. That voids `sxUnsat` exactly as spending the budget would have.
  What is given up is a candidate on a tainted path (it only feeds S10's
  replay, never wins). A clean hit is always solved.

*Measured* (rlimit per test, the two main N36 tests; tip 58e52af):

| | N36-1 | N36-1-noblock | exhausted 10M halves | 20M budget-outs |
|---|---|---|---|---|
| 58e52af | 51.4M | 51.4M | 3 + 3 | 1 + 1, plus the sibling solved to exhaustion |
| with S8y | 46.0M | 26.2M | 4 + 2 | 1 + 1, sibling declined |

Whole n36 suite: 368 s at 58e52af and 367 s with S8y, at load ~6
(S8ae's facts had already brought the tip down). The number that moves
is the bound, not this run's time: before S8y, how many hits ran out of
budget depended on what the context held (8 exhausted halves at S8r).
Now at most one tainted budget-out per loop depth can happen, and each
later hit that deep is declined without being solved. Wall times
standalone at the fix: n36 367 s; s1c_verdict (25 OK) 275 s.

*Pin.* By counts, never wall time. `symexTargetSolveStats` counts
target-hit budget-outs and S8y declines. `tsymex_rfc0005_s8y_budget_decline`:
- (a) the drop and its three non-drops;
- (b) under a 2M `seqQueryRLimit`, the pair loop has exactly one
  budget-out and at least one decline, and each decline is a classified
  `beSolverUndef`, never `sxUnsat`. It is RED with the decline disabled
  (4 budget-outs, 0 declines);
- (b) a clean loop ahead of an unsolvable factoring query still has every
  hit solved (>= 2 budget-outs, 0 declines).

N36-1, N36-1-noblock and s1c's N36 test each check `budgetOut <= 1`.

*Not fixed here.* The first five-iteration hit still spends its full 20M
(S8ag). A hit whose step 1 runs out but whose uncapped step 3 finds a
model spends 10M plus, and is not a budget-out, so the bound does not
cover it. How many such hits there are still depends on the context.
`-d:symexQueryStats` records the context's running `rlimit` total as each
query's cost, so its per-query figures overstate the spend (S8ac's
`rlimitDelta`). An unchecked solver's statistics read the context's
counter without a check, which this slice uses (`rlimitCountNow`).

**As landed (S8z, walker 177) — S8u's remainder.** The seven places S8u
reported, plus two soundness gaps and three faults found on the way. Every
expected value was checked against the pinned toolchain (Nim 2.2.10, debug
build) by an oracle test that runs the SUT itself.

1. **Array low bound.** An index read or write on an array whose index
   range does not start at 0 selects position `i - lo`, bounds-checked
   against `lo .. hi` (`isIndex.ixLo`, `isIndexAssign.iaLo`, and
   `arrayIndexConds` / `arraySelect` / `arrayStore` in the walker).
   `var a: array[1..3, int] = [7, 8, 9]; a[1] == 7` was a false `sxUnsat`;
   a param's witness and a symbolic index read are exact. An array
   indexed by an enum, a `char`, an `int8` / `uint8` or a `range` also
   classifies (`arrayIndexBounds`; it was a macro-time error).
2. **Enum without ordinal 0.** Nim zero-fills an untouched enum, so its
   value is ordinal 0 even when no member has it (probed: an untouched
   result field, result and local all read `ord == 0`). `defaultZeroTotal`
   now counts such an enum total, and a call's free `retSym` admits
   ordinal 0 beside the members (`allocEnumZeroLegal`, set only by
   `freshRetSym`). `ord(v.a) == 0` on an untouched result was a false
   `sxUnsat`. A `range` that excludes 0 stays non-total: Nim rejects its
   implicit zero at compile time, and a discriminator must start at 0.
3. **Array type alias.** `type Arr3 = array[3, int]` classifies as the
   array (it was `uninterp[__unsupported:Arr3]`).
4. **Inline `range` discriminator.** `case d: range[0..2]` compiles and is
   modelled; a `lo..hi` arm label (`of 0..1:`) is one arm per ordinal. Both
   were compile errors in `dsl_typebridge.nim`.
5. **Symbolic-index array write.** `a[i] = v` and `a[i] op= v` are
   modelled: the parser writes through a temporary (`mkIndexAssignStmt`
   with the low bound) and the walker stores into the `svArray`. As in
   Nim, the index is checked before the value is evaluated:
   `a[5] = raiser()` raises `IndexDefect`, not the value's exception
   (probed).
6. **Closure-returning callee.** A callee whose `result` is a closure it
   built (`result = proc(y: int): int = y + t`) hands the caller that
   closure (`svClosure` through `completeReturn` and the call's
   post-binding; the call cache is skipped for it). Before, the call's
   `retSym` allocation raised in `allocateSym(itUninterp)`
   (`weInternalWalkerFault`). Any other closure value (a `nil` result, a
   free closure) is a scoped `ceUnsupportedHof` placeholder.
7. **Container shapes.** A `Table[string, V]` value and a `HashSet[T]`
   element of any fixed-width integer type (`int8` .. `uint64`, `char`,
   `byte`, an enum, a `range`) or `bool` are modelled in the 64-bit cell:
   stored sign- or zero-extended (`cellOf`), read back truncated
   (`cellValue`), and a set's size bounded by its element's domain
   (`HashSet[bool]` holds at most 2 members, `HashSet[E]` at most `|E|`:
   `cellDomain` / `containerCardConds`). Witnesses render through
   `readTableStrIntAs[T]` / `readSetIntAs[T]`. The shapes enumerated, and
   what still declines scoped:
   - `Table[K, V]` with a non-`string` key: the model and the S8f
     registry / extractor are keyed by string
     (`seUnsupportedTableKeyType`).
   - `Table[string, V]` / `HashSet[T]` with a `string`, `float`, tuple,
     object, `seq` or other non-integer `V` / `T`: every operation would
     need a different cell sort (`seUnsupportedTableValType`,
     `seUnsupportedSetCharInterop`).
   - A `char` / `byte` / `uint8` container as a witness only: `char` and
     `uint8` classify to the same IRType, so the renderer cannot name the
     element type (`feUnsupportedWitnessType`). Such a container built
     inside the SUT is modelled.
   - `seq[T]` element shapes are unchanged by this slice.
   - An array indexed by `bool`, or wider than 4096 elements
     (`maxArrayIndexSpan`), declines as an unsupported type.

Found on the way:

- (a) **`pairs` loops (false `sxSat`).** `for i, x in pairs(c)` bound `i`
  to the ELEMENT and never bound `x`: a label reading `i` alone was a
  false `sxSat` (the index of an `array[3..5, T]` "reached" 0), and one
  reading `x` was `feGlobalReadUnmodelled`. `i` is now the index (Nim's
  `lo + k` over an array, in the index variable's type; the position over
  a seq). A single-variable `for t in pairs(c)` declines scoped.
- (b) **Uninitialised composite locals.** `var a: array[3, int]`,
  `var r: Obj` and `var v: Variant` were a decline that left the name
  unbound; the next element write or field read faulted
  (`weInternalWalkerFault`: `recv.kind == svArray` in `isIndex`,
  `lowerConvIntWidth` on an enum field). They are now `default(T)`
  (`iekZeroValue`), with the in-band `feUnsupportedOpHavoc` fallback for a
  field or element that has no modelled zero.
- (c) Two `weInternalWalkerFault`s in declined container reads became
  scoped declines: a `Table[string, string]` index read (`eqBV`'s kind
  assert; `declinedIndexEnv` now binds the declined read's result), and a
  `HashSet[string]` membership decline message that read `.width` on a
  string type.
- (d) The symbolic-index array write's backstop for a value whose
  representation cannot be aligned to the element's drops the write, so it
  records `feUnsupportedStmtKind` (dcSubstituted, a stale env), never the
  fresh class: the `feUnsupportedOpHavoc` site audit stays at 14.
- (e) **A proc value compared with `nil`** (`f == nil` on a closure a
  callee returned). `nil` fell to the generic unsupported-literal dummy,
  an int 0, and the walker compared the `svClosure` with it:
  `weInternalWalkerFault` (`coerceIntLit`) whenever the closure path was
  walked first. That order holds on the cpp backend and not on the c
  backend, so only the cpp run showed it. The parser's nil-compare arm
  now declines it scoped (`ceUnsupportedHof`, a bool placeholder) on the
  path that reaches it.

- **Consumer-visible (for S11's migration note).**
  - **`sxUnknown` programs that now get verdicts:** the seven items and
    (a) / (b) above.
  - **Verdicts that change:** a label over an array with a nonzero low
    bound, over an untouched enum with no ordinal 0, or over a `pairs`
    loop's index could have been a wrong `sxUnsat` / `sxSat`.
  - **Cache.** The canonical program form changes for an index on an array
    with a nonzero low bound (`;lo=`). The walker bump to 177 invalidates
    every symex cache entry.
- **Different mechanisms, reported and not fixed here.**
  - **No clean no-zero type remains.** With S8z, every type that allocates
    free without a decline of its own has a modelled zero (the only
    exception, a `range` excluding 0, cannot be an untouched result in
    Nim). The no-zero result pins therefore moved to a `HashSet[string]`
    arm field, whose allocation adds `seUnsupportedSetCharInterop`
    (dcNoAnswer): those pins are now `sxUnknown`, where they had been a
    taint-only `sxUnsat` or a replay-confirmed `sxSat`.
  - **Seq element `op=`.** `s[i] += v` on a `seq` is still
    `feUnsupportedStmtKind` (the Class-B trigger the S1b / S1c / S3 and
    `augmented_assign` pins now use).
  - **Seq element write order.** `s[i] = f()` on a `seq` evaluates `f()`
    before the bounds check; Nim checks the index first. The array path
    is ordered correctly (item 5); the seq path is unchanged.
  - **`char` renders as `uint8`.** A `char` scalar or `seq[char]`
    witness renders as `uint8`; the container case is declined (item 7).
  - **`low(a)` / `high(a)` on an array** are `feUnsupportedExprKind`.
  - **Array witness index type.** An `array[1..3, int]` witness is
    rendered as `array[0..2, int]`; the values are positional, so replay
    is exact, but the type is not the parameter's.
  - **Macro-VM closure capture (for S8x).** A nested proc inside
    `classifyObjectRecordFields`' per-`case` loop that captured the loop's
    `var enumOrdinals` made the VM keep one closure environment across
    iterations without re-zeroing it: a multi-variant's second axis got its
    enum tags twice, and its witness `case` failed to compile ("duplicate
    case label"). Caught in this slice by the S8s / S8u pins and fixed by
    making `tagOrdOf` a top-level proc; the same hazard class as S8x's
    element aliasing, for S8x's audit to cover.

Pins: `tests/tsymex_rfc0005_s8z_remainder.nim`. It covers:
- (1) a low-bound literal read with a dead label (RED: false `sxUnsat` /
  false `sxSat`), a param witness replayed (RED: `sxRaised`), a symbolic
  index read;
- (2) an untouched enum field with no ordinal 0 (RED: `sxUnknown`);
- (3) an array alias param (RED: `feUnsupportedParamType`);
- (4) an inline `range` discriminator with a range label (RED: compile
  error "node is not a symbol");
- (5) `a[i] = v`, `a[i] += v`, the index-before-value order and a
  low-bound write, with dead labels (RED: `feUnsupportedStmtKind`);
- (6) a closure-returning callee, exact with a dead label, and a `nil`
  closure result, and a closure compared with `nil`, as scoped declines
  (RED: `weInternalWalkerFault`; the nil compare on cpp);
- (7) `Table[string, int32]`, `Table[string, enum]`, `Table[string,
  bool]`, `HashSet[uint16]`, `HashSet[int8]`, `HashSet[enum]`,
  `HashSet[bool]`, `HashSet[char]`, with witnesses, dead labels and
  domain-bounded sizes, and the scoped declines (RED:
  `feUnsupportedWitnessType`, `seUnsupportedSetCharInterop`,
  `weInternalWalkerFault`);
- (8) `pairs` over a low-bound array, an enum-indexed array and a seq, and
  uninitialised array, object and variant locals (RED: false `sxSat`,
  `feGlobalReadUnmodelled`, `weInternalWalkerFault`, compile error for the
  enum-indexed array);
- the `>= 177` floor.

Re-pinned, each checked against real Nim:
- `phase15_CR2_cachekey` pin (177).
- `r6_n43_parity`: the bad-value / bad-element cells moved from `int32`
  (now backed) to `string`; `int32` is asserted allocatable.
- The no-zero result pins moved from an enum field with no ordinal 0 (now
  modelled) to a `HashSet[string]` arm field, and now expect `sxUnknown`
  (see "No clean no-zero type remains"):
  - `r6_r2_zerodefault_result` T5h-4
  - `rfc0005_s6b_ops` (two tests)
  - `rfc0005_s8l_exits`
  - `rfc0005_s8i_models` (4): the declined construction's arm field.
- The Class-B `feUnsupportedStmtKind` trigger is now a seq element's `+=`
  (`q[b and 1] += b` on `@[p.x, p.y]`):
  - `rfc0005_s3_monotonicity`
  - `rfc0005_s1b_kinds`
  - `rfc0005_s1c_verdict`
  - `augmented_assign`
- `r6_n36_raise_class_audit`: one marked `raise newException` site fewer
  in `runtime.nim` (the array read's two per-bound copies of "isIndex:
  non-int index kind" are one, in `arrayIndexConds`), category-c.
- `r11_range_invariant_audit`: three new direct `bvRangeConds` calls in
  `runtime.nim` (4 -> 7): a second one inside `rangeCondsIfNeeded`
  (helper-internal), and two marker-exempt sites, `arrayIndexConds`
  (`index-defect-check`) and `inCellDomain` (`container-cell-domain`).
- `r6_itesv_mergedegrade` "vulnerable array in the else / then branch":
  `sxUnknown` -> `sxRaised` (`IndexDefect`, the witness replays). The
  SUT reads `arr[i]` before its bounds guard; the uninitialised
  `var arr: array[3, string]` was a decline that tainted every path and
  hid the reachable Defect ((b) above). Never an `sxSat`.

**As landed (S8ac, walker 178) — S8aa's remainder.**

*A `var` parameter is the caller's location.* The typed AST gives a `var`
formal's every use as `nnkHiddenDeref` over the symbol, which the parser read
as a `ref` dereference. A `var` REF parameter (`proc noteR(cur: var Box, b:
Box) = cur = b`) therefore stored a `Ref` into the pointee's heap array
(`weInternalWalkerFault`, "sort mismatch at array store value"), and a read of
one was `heUnresolvedRef`. `isVarIndirection` now treats that deref as the
variable itself, in expressions and as an assignment target.

Probing the neighbouring shapes found a false `sxSat` the fence did not name.
#140's write-back is by name (`varArgs`, formal to caller variable), so it
covers a plain local only. A `var` actual that is a location (`setI(h.n, v)`,
`o.a`, `s[0]`, an array element, `p[]`, `noteR(h.cur, b)`) was never written
back, and the caller kept the old value (`h.n == 1 and v != 1` after
`setI(h.n, v)` was `sxSat`). Every walked user call now goes through
`userCallStmt`. For each such actual it binds the location's value to a
temporary, passes the temporary, and assigns it back to the location through
the ordinary assignment lowering (`parseAsgn`, factored out of
`parseStmtInner`). The write-back runs on the normal exit and on a raised
exit: the call is wrapped in a `try` whose `finally` is the write-back. That
is copy-in/copy-out. Nim passes the address, and the two agree unless the
callee can reach the location another way while it runs. So the call
declines (`feUnsupportedOp`, scoped) when another argument names the same
root variable, or when, for a heap location, another argument's type can hold
a ref to the cell (`varActualMayAlias`).

Three more channels lost the write-back (each a false `sxUnsat`, plain local
included):
- The call cache replays only the callee's `pcDelta`. A call with a `var`
  argument is no longer cached.
- A raise escaping the callee forked the caller's path without the callee's
  writes. `isCall`'s escaped loop now applies them.
- `routeRaise` searched every enclosing try for a matching `except` before
  looking for a `finally`. So in `try: (try: raise finally: u = v) except
  E: ...` the outer handler ran without the inner `finally`, and `u == v`
  was a false `sxUnsat` in plain source. A try whose arms do not match but
  which has a `finally` now takes the raise first (`pendingRaise`), as Nim
  does. The separate top-down finally scan after the handler loop is gone.

*An unchecked `div` of a stamped offset stays linear.* `-d:symexQueryStats`'s
`rlimit` is the context's step counter, cumulative over the walk, so it never
showed a query's own cost. Each stat now also records `rlimitDelta`, the steps
that query spent. The counter is read from the query's own first solver
(`querySolver`), before it is checked. The exit dump and
`symexQueryStatsSummary` report the sum as `drlimit`.

The counter moves by about one unit per solver created (found by S8y), and
Z3's search depends on it. The first cut read the counter from a solver made
just for the read, once per query. That moved the counter under every later
check, so the stats build returned a different `dy_hit` model than the plain
build: `@[210, 254, 0]` instead of `@[140, 240, 0]` on Z3 5.1, and
`@[64, 254, 0]` instead of `@[222, 4, 0]` on 4.13.4 (walker 174). S8ad
carried that first cut (`cd983fd`) for its own step pins. Reading the counter
from a solver the query builds anyway makes the two builds agree on both
versions. "measuring the steps does not change the model" pins this inside
one binary, so it does not depend on the Z3 version or the walker. The same
walk runs twice: once with `symexQueryStatsPaused` set, which skips the read
and the record as the plain build does, and once recorded. The two must
return the same model. With the probe-solver read put back, the pin fails
(`@[134, 222, 0]` recorded against `@[182, 86, 0]` paused, on 5.1 at walker
176).

With it, S8aa's probe traced to one term. S8w wrapped an unchecked signed
quotient on a width-stamped Int with `wrapIntToWidth`, i.e. `q mod 2^64` of a
quotient that is already nonlinear (`start div y`, `y` a bitvector
`bv2int`'d). The query ran past 900 s (unbounded `queryRLimit`), or out of
`seqQueryRLimit` when a scan's seq was in it: 40M steps for `p div y == 3`
and 20M for `start div y == 3`. A truncated quotient is never further from
zero than its dividend, so the only quotient outside the window is `low(T)
div -1`. `lowerArith` now selects `low(T)` for exactly that case, which is
linear, and drops `bDiv` from the wrap. The same probe is 0.91M steps in all.
The two quotients are `sxSat` at 0.47M and 0.80M.

A bitvector route (`int2bv` of the stamped dividend, `bvsdiv`, `bv2int`
back) was tried and is worse on Z3 5.1. `start div y == 3` went back to
`seqQueryRLimit`, and the dead probe took 31M steps. It is not landed.

*A shift count is masked to the operand width.* Probed on the pinned
toolchain, c and cpp, debug and release. Nim 2.2.10's codegen emits `x <<
(n & (W-1))` for `shl`, and `x >> (n & (W-1))` (arithmetic when signed) for
`shr`: `5 shl 64 == 5`, `5 shl 65 == 10`, and `n = -1` shifts by `W-1`. The
int8, int16 and int32 masks are 7, 15 and 31. The mask is in Nim's C output,
not left to the machine, so the result is the same with gcc (Linux, mingw)
and msvc.

The model used Z3's saturating `bvshl`/`bvlshr`/`bvashr`. Non-replaying
witnesses at the base:
- `n == 64 and x == 5 and (x shl n) == 0` was `sxSat` at `(5, 64)`.
- `n >= 64 and x != 0 and (x shl n) == x` was a false `sxUnsat`.
- `3'u32 shl 33 == 6` was `sxUnsat`.
- `int8 shl int` faulted the walker (`binBV: width mismatch`).

`shiftCountBV` now masks the count on its own bit pattern and moves it to the
operand's width. The fence called this C UB; it is not, because Nim masks
first.

*The short-circuit join covers allocation and container state.*
`sameHeapMeta` became `heapMetaExtends`. A survivor's bookkeeping must extend
the skip path's:
- the same heap keys and nil-edge flag;
- each counter at least the skip path's;
- each live-ref list the skip path's followed by what the body minted.

A fresh ref's facts are in the survivor's own `pc`, so the join holds them
as `cond => R`. The joined path takes the largest counters and every minted
ref (`joinHeapMeta`). Two survivors minting the same name for their first
`new T` share one constant, constrained under each one's own `G_i`.

`joinSV` now also joins:
- a table: its data and presence arrays and its counter;
- a set: its members and counter;
- a distinct value: its constant and its base. G4's eject pin carries
  over by congruence.
- an object variant with the same arms: its discriminator and every field.
  A field of an unselected arm is never read as a value.
- an opaque ref.

A multi-axis variant and a closure still decline, and the paths stay apart,
which is exact.

With 6 pairs, the base's Z3 calls against this slice's:

| Operand writes | Base | S8ac |
|---|---|---|
| a heap cell, with a fresh `Box` | 87 | 8 |
| a heap cell, with a fresh `Box` (dead target) | 441 | 9 |
| a local, with a fresh `Box` | 75 | 8 |
| a `Table` | 168 | 7 |
| a `Table` (dead target) | 315 | 8 |
| a `HashSet` | 150 | 7 |
| a distinct value | 229 | 13 |
| an object variant | 87 | 8 |

Pins: `tests/tsymex_rfc0005_s8ac_remainder.nim`, with a `.nim.cfg` that sets
`-d:symexQueryStats`.
- (1) Every `var` ref shape: rebind, conditional, read, nested, through a
  field, and field write. RED: `weInternalWalkerFault`.
- (1) Located actuals: heap field, value field, seq and array element, `p[]`.
  RED: each dead target a false `sxSat`.
- (1) The cache, the raise, a raising field actual, and an expression-position
  call. RED: `sxUnsat`.
- (1) The inner `finally` under an outer `except`. RED: `sxUnsat`.
- (1) The aliasing call declines, scoped.
- (2) The dead quotient and the scan's hit, each at most 5M steps with no
  `beSolverUndef`. RED: past 900 s.
- (2) Both quotients `sxSat` within 5M. RED: `sxUnknown`.
- (2) `rlimit` monotone and the deltas within it.
- (3) Every witness above, with its value checked in compiled code.
- (4) Each chain within 16 Z3 calls (20 for distinct), with its witness
  checked, and the dead ones `sxUnsat`.
- The `>= 174` floor.

*Different mechanisms, reported and not fixed here.*
- **A local distinct value with no distinct-typed parameter is a walker
  fault.** `var m = Meters(0); m = m + Meters(1)` in a SUT with no `Meters`
  parameter is `weInternalWalkerFault` (`reboxDistinct: distinct sort
  'Meters' not allocated`). It is the same at the base. The join pin takes
  `m0: Meters` as a parameter.
- **`start < 0 and y > 1 and start div y == start` (UNSAT) is still
  `sxUnknown`.** It runs to `seqQueryRLimit`, 40M steps, when a scan's seq is
  in the query. It is nonlinear Int division by a `bv2int` term, and Z3's
  nonlinear core is not complete under the sequence theory. The honest
  verdict is `beSolverUndef`. It is not a hang, and the bitvector route above
  does worse.
- **A `var ptr` parameter passed `addr x`** is `heUnsafeCast`, the existing
  scoped decline. **A routine declared inside the SUT** is
  `feUnsupportedStmtKind`, also existing.
- **Copy-in/copy-out declines on possible aliasing.** The check is by
  argument (same root, or a type that can reach the cell). A callee that
  reaches the location through a global is not in the symex fragment.

**As landed (S8ag, walker 183) — S8y's remainder: the one-character
`str.indexof` split.** Two changes. (1) `iekStrFind` with a needle that
folds to a one-character literal lowers to a fresh Int with split axioms
in place of Z3's `str.indexof`. That covers the three closed forms of the
scan idiom: Q1's `tryRecognizeScanIdiom`, B3's `tryRecognizeScanPairIdiom`
and B4's `tryRecognizeAccumulatingScan`. All three emit `iekStrFind`, and
`lowerStrArm` is its only lowering. A caller's own `s.find(':')` takes
the same path. (2) A tainted target hit that finds a model only after
half its budget comes under S8y's scoped decline. Walker 182 -> 183.

*1. The split.* `lowerIndexSplit` returns a fresh Int `ix` and fresh
strings `pre`, `x` and `post`. The needle is `c`, the start `i`. Every
query that reaches `ix` asserts (`indexSplitAxioms`):

- (F) `ix = -1`, or: `ix >= 0`, `s = pre ++ x ++ c ++ post`, `len(pre) =
  i`, `ix = i + len(x)` and `c notin x`;
- (N) `ix = -1` implies `i < 0`, or `i > len(s)`, or `c notin s[i ..]`,
  where `s[i ..]` is `str.substr(s, i, len(s) - i)`.

`c notin t` is asserted as `t in (allchar & ~c)*`
(`str.in_re`/`re.inter`/`re.comp`), which for a one-character `c` holds
exactly when `not contains(t, c)` does, so the proof below is the same for
either. The regex is the one that works. Stated as `not contains`, round 6's
B1-3 (`tsymex_r6_b1_stringbacked`, `data.len == 37` after a NUL scan)
regressed on Z3 5.1. Its hit runs out at 20M (the suite goes RED, 528 s).
As the regex it is SAT in 122k offline, against 20M+ out, and the suite is
back to base. On 4.13.4 the same query is 224k as the regex and 549k as
`not contains`. Regex in (F) with `not contains` in (N) still had B1-3's
hit run out in-process on 5.1, so both arms take the regex.

*Equivalence.* Z3 follows SMT-LIB's `str.indexof(s, t, i)`. It is -1 when
`i < 0` or `i > len(s)`. For a non-empty `t` it is the least `j >= i` with
`t` at `j`, or -1 when there is none. With `|t| = 1` the empty-needle rule
(`i` itself) never applies. Write `r = str.indexof(s, c, i)`. For every
`s` and `i`:

- *(F) and (N) have a model with `ix = r`.*
  - If `r >= 0`, then `0 <= i <= r < len(s)`, `s[r] = c`, and there is no
    `c` in `s[i ..< r]`. Take `pre = s[0 ..< i]`, `x = s[i ..< r]` and
    `post = s[r + 1 ..]`. (F)'s second arm holds, and (N) holds because
    `ix != -1`.
  - If `r = -1`, take `ix = -1`. (F)'s first arm holds. (N)'s consequent
    holds because `i` is outside `0 .. len(s)` or `s[i ..]` has no `c`.
- *Every model has `ix = r`.*
  - If `ix != -1`, (F)'s second arm holds. `len(pre) = i`, so `i >= 0`.
    `s[ix] = c` with `ix = i + len(x)`, so `ix < len(s)`. And `s[i ..<
    ix] = x` holds no `c`. So `ix` is the first `c` at or after `i`, which
    is `r`.
  - If `ix = -1`, (N) gives `i < 0`, `i > len(s)`, or no `c` in `s[i ..]`.
    Each of those makes `r = -1`.

The boundary cases are the ones SMT-LIB names:
- `i = len(s)`: `s[i ..]` is `""`, so the result is -1, as Z3 gives.
- `i > len(s)`: (N)'s second disjunct gives -1. (F) cannot hold, since it
  needs `len(s) >= i + 1`.
- `i < 0`: (F) needs `len(pre) = i`, which is impossible, so -1.

Nothing about `c` beyond its length is used, so `"\0"` and `"\xff"` are
covered alike.

So a query with `ix` and its axioms has exactly the models the query with
`str.indexof` had, extended by `pre`, `x` and `post`. A split's axioms
mention only its own fresh constants beside `s` and `i`, so a query that
never reaches `ix` can omit them. `indexSplitRoots` adds the axioms of the
splits a query reaches. It closes over a reached split's `s` and `i`,
which may hold another split.

*Chain fact* (`indexSplitChain`). Take two splits `a` and `b` of one
haystack `s` (the same AST). If `a.ix >= 0`, `b.ix >= 0` and `b.i = a.ix +
1`, then `b.pre = a.pre ++ a.x ++ c_a` and `a.post = b.x ++ c_b ++ b.post`.

It is valid. By (F), `a.pre ++ a.x ++ c_a` is the prefix of `s` of length
`a.ix + 1`, and `b.pre` is the prefix of length `b.i`. The lengths are
equal, so the prefixes are equal. The second equation follows by
cancelling that prefix from the two decompositions of `s`.

The fact is guarded by its own premise. So it is asserted for every
ordered pair of reached splits of one haystack, with no syntactic match on
`b.i`. That matters because readCString's next start is a call's return,
`p1 = ix + 1`, a separate equation in the query.

*Every solver site gets the axioms.* The split's Int is free without them.
That would never cause a false UNSAT, but it could give a wrong witness.
The sites are:
- `globalRoots`, and through it `pathRoots`, `loopArmInfeasible`,
  `concreteBranchOutcome` and `concretelyInfeasible`;
- the concolic soundness pin;
- `z3CheckBounded`.

`tsymex_rfc0005_s7_closure`'s drain audit lists the new pool. Step 1c
(`seqRangeFacts`) also ranges a split's Int (-1, or `i .. len(s) - 1`). It
links the Int to `contains` as S8ae's `str.indexof` facts do, so `s.find(':')
> 200 and ':' notin s` is still refuted theory-free.

*2. N36-1's exit hits.* At 2f576ee on Z3 5.1:
- the pair loop's first five-iteration exit hit (`loopIters` [4], S8y's
  q103/q106 floor) ran out of its tainted 20M budget;
- the [3] hit before it spent 10.2M, with step 1 out and step 3 SAT;
- S8y declined the deeper hits after the budget-out.

On the split, every tainted hit in the file is SAT, and none costs more
than 1.34M on 5.1. The [4] hit that ran out is SAT in 0.9M. The four hits
S8y declined ([4] and [5], twice each) are SAT candidates. On 4.13.4 the
dearest is [5] at 4.2M, which was 2.2M at base.

With `not contains` in the axioms (an earlier draft), [5] cost 11.6-13.1M
and the second [5] ran out. The figures vary by context, as S8y's note
found. The verdicts are unchanged: N36-1, N36-1-noblock and s1c's N36 test
are still `sxUnknown`. No hit changed between SAT and UNSAT.

*3. The slow-SAT bound.* `solveTargetHit` now handles a tainted hit that
returns `sxSat` after spending at least half its budget
(`classifyTargetSolve`: `budgetOutFloor div 2`):
- spending that much means `checkCapped`'s capped step 1 ran out, and the
  uncapped step 3 found the model;
- the hit records its loop depths in `w.budgetOutDepths`, as a budget-out
  does, and is counted in `symexTargetSolveStats.slowSat`;
- a later tainted hit at least as deep is declined: classified
  `beSolverUndef`, which voids `sxUnsat`.

What is given up is a further tainted candidate beside the one the slow
hit found. A clean hit is always solved. `symexTargetSolveStats.units`
now totals the target-hit `rlimit`, which gives the per-test cost pins.

In the earlier draft with `not contains`, N36-1 without the bound solved
the second [5] hit and ran out of budget there: budgetOut=1, declined=0,
203 s. With the bound it had budgetOut=0, declined=1 and slowSat=1, in
118 s. With the regex no N36 hit reaches half its budget, so the bound
does not fire there. Section (5) pins it on the pair loop under a 400k
budget, where it does fire on 5.1.

*Measured.* Target-hit `rlimit` per suite (`-d:s8agTrace`, summed per
hit) and wall time standalone at load 15-27, base 2f576ee against S8ag.
Every suite has the same OK count at base and at S8ag.

| suite | Z3 5.1 base | Z3 5.1 S8ag | Z3 4.13.4 base | Z3 4.13.4 S8ag |
|---|---|---|---|---|
| n36_raise_degrade (8 OK) | 62.3M, 428 s, 2 out | 8.2M, 41 s, 0 out | 12.4M, 94 s | 15.3M, 95 s |
| s1c_verdict (24 OK) | 54.3M, 323 s, 1 out | 2.7M, 31 s, 0 out | 7.4M, 77 s | 8.6M, 79 s |
| q1_scanlift (13) | 0.82M | 0.15M | 0.71M | 0.19M |
| r6_b5_chained (9) | 0.62M | 0.57M | 0.64M | 0.40M |
| r6_nulwitness (14) | 0.13M | 0.26M | 0.25M | 0.12M |
| r6_b4_readcstring (13) | 0.24M | 0.40M | 0.41M | 0.22M |
| s8r_theoryfree (3) | 0.01M | 0.02M | 0.01M | 0.01M |
| s8v_termination (7) | 0.01M | 0.02M | 0.01M | 0.01M |
| s8ae_remainder (16) | 0.04M | 0.10M | 0.12M | 0.06M |
| r4_strip (5) | 20.03M | 20.03M | 20.04M | 20.04M |

r4_strip's 20M is its own adversarial pin (strip idempotence), unchanged.

On Z3 4.13.4, n36 and s1c cost more than at base: +23% and +15%. The
verdicts and per-hit statuses are identical, and nothing runs out. The
extra cost is in the deepest pair-loop hits ([5]: 2.2M at base, 4.2M
here), where the regex costs 4.13.4 more than `not contains` did (8.3M and
4.0M in the earlier draft). That draft broke B1-3 on 5.1, which is the leg
every Linux run takes, so the regex stays. Nothing on 4.13.4 nears a
budget.

Each hit's status (SAT, UNSAT or unknown) is identical at base and S8ag in
q1, b5, nulwitness, b4, s8r, s8v, s8ae and r4, on both Z3 versions. The
moves are these, and every one is intended:
- n36 on 5.1: [4] unknown -> SAT, twice; and the four hits S8y declined
  ([4] and [5], twice each) are now SAT candidates.
- s1c on 5.1: the last tainted hit ([5], out at 20.0M) is SAT in 0.5M.
- On 4.13.4, n36 and s1c are identical per hit.
- The r6 suites b1_stringbacked, b3_scanpair, n10_coverage_matrix,
  b7r_bytescan and b7r2_pathscope are identical per check at base and
  S8ag, on both Z3 versions. b1_stringbacked takes 67 s on 5.1, against
  432 s at base.

*Pins.*
- `tsymex_rfc0005_s8ag_indexsplit` (15):
  - (1) a 300-instance randomized differential of the axioms against Z3's
    `str.indexof`. It is RED on two mutants: the found arm without `c
    notin x`, and an off-by-one not-found range.
  - (1) the -1 boundary cases, and the chain fact on 150 random two-scan
    instances.
  - (2) Q1, B3 and B4 each lower through a split and give `sxSat` with a
    witness that satisfies the program.
  - (3) S8ae's step 1c link, the context guard, and the needles that are
    not split.
  - (5) `classifyTargetSolve` (slow SAT at half the budget, budget-out at
    all of it, an UNSAT or an unbounded solve never costly). Under a 400k
    budget, the pair loop has a costly hit (`budgetOut + slowSat >= 1`)
    with declines after it. With no budget-out the costly hit was a slow
    SAT, which is Z3 5.1's case: 0 out, 1 slow, 3 declined. Z3 4.13.4's
    case is 1 out and 5 declined. The result is `sxUnknown`, and each
    decline is a classified `beSolverUndef`.
  - The `>= 183` floor.
  - At 2f576ee the file does not compile (`IndexSplit`).
- N36-1, N36-1-noblock and s1c's N36 test now pin `budgetOut == 0` (it was
  1 at 2f576ee, so these are RED there), `slowSat <= 1`, and `units < 40M`.
- `tsymex_rfc0005_s8y_budget_decline`'s tight budget drops from 2M to
  20k, and its pin from `budgetOut == 1` to `>= 1`. At 2M the pair loop
  no longer runs out on Z3 5.1. At 20k a shallow hit runs out on both
  versions: 2 budget-outs on each, with 22 declines on 5.1 and 24 on
  4.13.4. A shallower hit walked after the first budget-out can run out
  too.

*Different mechanisms, reported and not fixed here.*
- **S8y's own suite is red on Z3 4.13.4 at 2f576ee.** "one tainted
  budget-out; every later hit as deep is declined" fails with
  `budgetOut=1 declined=0`: the only budget-out there is the deepest hit,
  [5]. That is the symex-mingw leg's Z3, so S8y alone would ship a Windows
  red. S8ag's retuned budget passes on both versions.
- **Which mechanism fires depends on the Z3 build, and on the process's
  earlier contexts.** In the same pair loop at the same budget, one run
  has a slow SAT and the next a budget-out: at 100k on Z3 4.13.4, a
  standalone run against the same walk after the file's earlier tests.
  So the pins require a costly hit and its declines, not which kind it
  was.
- **The per-hit cost still depends on the context.** In the earlier
  `not contains` draft, the same [5] hit cost 11.6M in one build and 13.1M
  in another (s1c's N36 test: 17.9M against 29.5M units). Adding a probe's
  own `rlimitCountNow` call was enough to move it. Offline, one dumped
  query's cost does not track its in-process cost: n36's [5] query is
  unknown at 20M offline on 5.1 and SAT in 1.3M in the walk. So the pins
  bound counts and a ceiling, not a figure, and encodings were chosen on
  in-process runs.
- **The encoding of `c notin t` decides Z3's cost, and the two versions
  disagree.** The regex is far cheaper on 5.1 (n36 8.2M against 53.5M as
  `not contains`), and required for B1-3. On 4.13.4 it is dearer on the
  deepest pair-loop hits (n36 15.3M against 8.3M). No single encoding was
  best on both. Asserting both forms was tried offline and was no better.
- **Only literal one-character needles split.** `find("ab")`, a computed
  needle, and `rfind` / `seq.last_indexof` still lower to the sequence
  theory's own functions.
- **The chain facts are all-pairs over the splits of one haystack** that a
  query reaches. That is quadratic in the scans of one string. It is
  cheap at N36's five-deep chains (the totals above), but it is not
  bounded.
- **"Use per-query rlimit deltas" (S8y's remainder item) needed no new
  mechanism here.** Two call sites already measure a query's own spend,
  not the context's running total, and neither is this slice's to
  duplicate. `solveTargetHit`'s budget/slow-SAT classification
  (`classifyTargetSolve`, above) has read `rlimitCountNow(w.z3)` before
  and after each target-hit solve since S8y itself (`spentBefore` /
  `spent`); S8ag only adds the slow-SAT arm on top of that existing
  delta, it does not change how the delta is taken. The `-d:symexQueryStats`
  debug build's own per-query figure (`SymexQueryStat.rlimitDelta`) was a
  different, separately-landed fix: S8ac moved its base read from a
  probe-only solver (which shifted the context's counter under every
  later check) to the query's own first solver
  (`noteQueryRLimitBefore`/`querySolver`), landed on the channel ahead of
  this slice's rebase (9b820d3). Both are per-query deltas already; S8ag
  keeps them as the one mechanism each, and adds neither a third nor a
  duplicate.

**As landed (S8ai, walker 182) — S8ae's remainder.** All three items are
in `seqRangeFacts` and its use in `checkCapped`'s step 1c. Step 2 still
never runs behind a step 1c UNSAT, and a step 1c UNSAT without the caps is
still the query's own.

*1. Semantic links.* The facts now group terms into the query's equality
classes, a union-find over AST ids:
- every sequence equality among the roots joins its two sides;
- every term joins the class of what `Z3_simplify` folds it to, so a
  computed `"a" ++ "b"` meets the literal `"ab"`.

A link between two terms is made when their haystacks and needles are in
the same classes. When they differ in AST, the link is guarded by their
equality (`implies(t == y, ...)`), so each fact is still valid in the
theory on its own. Theory-free, the guard follows from the query's
equalities by congruence, or from the rewriter. A literal needle in a
literal haystack (`str.contains("ab:", ":")`) is folded with Z3's own
rewriter. `t == ":" and s.find(t) > 200 and ":" notin s` was a
`maxSeqLen` decline at 58e52af. It is now `sxUnsat` by step 1c's uncapped
check, as are:
- a chain of equalities (`y = ":"`, `t = y`);
- an equal haystack (`x = s`);
- a computed needle;
- a piece equal to the needle through a chain.

*2. New facts.* Each is valid in the theory:
- **`str.indexof` from two starts.** For `0 <= j <= i`:
  - `r_j >= i` implies `r_i = r_j`;
  - `r_i >= 0` implies `0 <= r_j <= r_i` (the converse direction).

  A suffix `t` is found from every start `0 <= i <= len(s) - len(t)`, at
  `len(s) - len(t)` at the latest.
- **`r = str.replace_all(s, t, u)`.**
  - `r = s` for an empty `t`, or when `not str.contains(s, t)`.
  - `len(r)` compares with `len(s)` as `len(u)` compares with `len(t)`.
  - With literal `t` and `u` (`len(t) >= 1`), the growth bound
    `len(t) * len(r) <= len(u) * len(s)`, with `>=` when `u` is the shorter.
  - Its kind is probed by parsing `str.replace_all`, since its builder
    (`Z3_mk_seq_replace_all`) is optional in nim-z3. The walker never emits
    it, so this only reaches SMT-LIB-parsed or hand-built queries.
- **`str.in_re(s, R)`.** `len(s)` lies within the word lengths of `R`
  (`regexLenBounds`), over these constructors:
  - `to_re` of a literal;
  - range and allchar;
  - concatenation, union and intersection;
  - plus and opt;
  - `loop` and `^`, with their counts as decl parameters or as integer
    arguments.

  Any other constructor reads as `0..unbounded`.
- **`x = str.from_int(n)`.**
  - `len(x) = 0` for `n < 0`;
  - otherwise `len(x)` is the number of decimal digits of `n`: exact below
    `10^20`, and at least 21 above;
  - `str.to_int(x)` is `n` for `n >= 0`, else -1.
- **Word equations.** `h` is in the class of `a_1 ++ ... ++ a_k`. A part
  equal to the needle, a literal part holding it, or a part that contains
  it makes `h` contain it:
  - it is found from `0 <= i <= offset`, at most within that part;
  - `seq.last_indexof` is at least the part's offset;
  - a prefix of the first part is a prefix of `h`, and a suffix of the
    last part is a suffix of `h`;
  - for a needle of length at most 1, `h` contains it only if some part
    does.
- **`L = seq.last_indexof(s, t)`.**
  - `L >= 0` iff `str.contains(s, t)`;
  - a prefix gives `L >= 0`;
  - a suffix gives `L = len(s) - len(t)`;
  - a piece equal to `t` at an in-range `i` gives `L >= i`.

Each new kind is probed from the linked Z3 (`SeqCapKinds`). A kind that
shares its ordinal with another probed operator is disabled (-2), and a
`^` that probes as `loop` is read as `loop`. The `replace_all`, regex and
`from_int` checks pass on Z3 5.1 and 4.13.4 alike, so none of those kinds
is disabled on either.

*Validity.* Each fact is checked in two ways against the linked Z3's
semantics, as S8ae's are:
- its negation is never SAT with the theory under 1M units;
- it rewrites to `true` on every ground instance with strings over `{"a",
  "\xff"}` of length at most 3 and integers in `-1..4`.

A hand-built mutant of each kind fails at least one check. The mutants
are:
- a `replace_all` that never grows when `len(t) <= len(u)` (the
  direction reversed);
- a loop `{1,3}` capped at length 2;
- every non-negative `from_int` at least two digits;
- a nonzero-start `indexof` at or before the earlier start's result (the
  converse reversed);
- a needle in `a ++ b` held by `a` or `b` (straddling ignored);
- `last_indexof + len(t) < len(s)` (strict).

One link was written and then dropped: `L` is at least every found
`str.indexof(s, t, i)`. It is valid. But S8v's pin asks every fact over
`s`, `t`, `i` for a negation that Z3 proves UNSAT within 1M units, and
neither Z3 does that for this one: 4.13.4 answers `unknown` even with `i =
0`. Its in-between form ("a start at or before `L` finds one in `i..L`")
was `unknown` on 5.1 too. S8v's pin was not weakened to admit them.

*3. `seq.last_indexof` takes step 1c.* A query holding one went from step
1 straight to the uncapped step 3. That was the one place the uncapped
sequence theory still ran. It now takes step 1c's uncapped half. An UNSAT
there is the query's own and is returned. Otherwise the query goes on to
step 3 as before. It does not take the capped half: that would decline a
query that is SAT only past the cap, which step 3 decides
(`tsymex_rfc0005_s8o_termination` (4), `t.len > 10` under a cap of 8, was
`sxSat` and read as a cap decline when the capped half was taken). Step 2
is still skipped for such a query, since the incremental core's
`seq.last_indexof` value is wrong. `s.len > 150 and s.endsWith(":") and
s.rfind(':') != s.len - 1` under `seqQueryRLimit = 2_000` was "the
uncapped query (it holds a seq.last_indexof) was not decided" at 58e52af.
It is now `sxUnsat` by the suffix link.

Termination, measured against 59bf62e (the channel after S8y) on the
test binary built with `-d:symexQueryStats`:

| Z3 | suite | wall (base / slice) | peak RSS | Z3 rlimit units |
|---|---|---|---|---|
| 5.1 | `r4_strip` | 153.2 s / 147.3 s | 186 / 186 MB | 20,030,283 / 20,030,293 |
| 5.1 | `q1_scanlift` | 3.0 s / 2.9 s | 64 / 66 MB | 3,114,329 / 3,114,329 |
| 5.1 | `r6_b5_chained` | 1.9 s / 2.4 s | 75 / 78 MB | 1,307,267 / 1,457,537 (+11.5%) |
| 5.1 | `rfc0005_s8r_theoryfree` | 0.1 s / 0.2 s | 50 / 50 MB | 39,267 / 39,267 |
| 5.1 | `rfc0005_s8v_termination` | 0.2 s / 0.3 s | 62 / 63 MB | 43,318 / 43,318 |
| 5.1 | `rfc0005_s8ae_remainder` | 168.7 s / 134.0 s | 156 / 162 MB | 39,511 / 39,511 |
| 5.1 | `163rev_intoffset_range` | 0.3 s / 0.5 s | 63 / 64 MB | 164,396 / 164,396 |
| 4.13.4 | `r4_strip` | 25.4 s / 29.0 s | 66 / 66 MB | 20,042,052 / 20,042,074 |
| 4.13.4 | `q1_scanlift` | 2.1 s / 2.4 s | 63 / 63 MB | 3,075,065 / 3,075,065 |
| 4.13.4 | `r6_b5_chained` | 3.0 s / 2.0 s | 73 / 74 MB | 1,262,895 / 1,271,646 (+0.7%) |
| 4.13.4 | `rfc0005_s8r_theoryfree` | 0.1 s / 0.4 s | 52 / 51 MB | 28,969 / 28,969 |
| 4.13.4 | `rfc0005_s8v_termination` | 0.3 s / 0.2 s | 64 / 65 MB | 32,453 / 32,453 |
| 4.13.4 | `rfc0005_s8ae_remainder` | 87.7 s / 92.9 s | 949 / 228 MB | 118,228 / 118,234 |
| 4.13.4 | `163rev_intoffset_range` | 0.5 s / 0.7 s | 57 / 57 MB | 127,120 / 127,120 |

Wall times were taken on a loaded host (load average 15 to 25) and move by
tens of seconds on the long suites. The rlimit totals are deterministic.
In every row the query and assert counts are identical, and so is every
check's outcome. The totals that moved:
- `r6_b5_chained` costs 11.5% more on Z3 5.1 and 0.7% more on 4.13.4, at
  the same queries and outcomes. The figure depends on the base: against
  4e76eac (before S8y dropped implied byte-domain constraints) the same
  facts cost 10.4% less on 5.1 and 5.5% more on 4.13.4, and against 58e52af
  (before S8ad) 11% and 13% less. What the facts cost on this suite is
  solver search variance across query texts, not a trend. It is reported
  here and not tuned.
- `r4_strip` moves by 10 units on 5.1 and 22 on 4.13.4, against a 20M
  total.
- `s8ae_remainder` moves by 6 units on 4.13.4.

Every other total is unchanged. The
`s8ae_remainder` wall time is its validity checks, which run outside the
walker and so outside these totals; its 4.13.4 peak RSS moved from 949 MB
to 228 MB with the same checks. No query changed outcome, and none
approaches a budget.

Pins: `tests/tsymex_rfc0005_s8ai_semantic.nim`. Every check below was RED
at 58e52af on Z3 5.1, unless stated otherwise.
- (1) Step 1c posed on its own (theory-free, facts, caps) is UNSAT for
  each of these. RED: SAT.
  - one equality;
  - a chain;
  - a haystack equality;
  - a computed needle;
  - a piece through a chain.

  Its no-equality companion stays SAT.
- (1) End to end, `t == ":" and s.find(t) > 200 and ":" notin s` is
  `sxUnsat`. RED: a `maxSeqLen` decline. Its `find > 5 and in` companion
  stays `sxSat`.
- (1) Every guarded link is valid by the two checks. There must be at
  least 17. RED: 9.
- (2) Step 1c posed on its own is UNSAT for each new fact's shape, with a
  SAT companion for each. RED: SAT.
  - `replace_all`: same-length pieces; growth both ways; no occurrence;
    and past the cap (SAT without the cap).
  - `in_re`: both loop forms; concat and union; and a 200-loop against
    the cap.
  - `from_int`: `n < 1000`, `n < 0`, `n >= 100`, the `to_int` round trip,
    and `n < 2^64`.
  - `indexof`: from a nonzero start, both directions, and a suffix.
  - Word equations: a part containing the needle; `a ++ ":" ++ b`; the
    1-character converse; prefix and suffix; and `indexof`. A
    two-character needle straddling two parts stays SAT.
- (2) Every new fact is valid by the two checks. There must be at least
  40 (RED: 14), and at least 31 word-equation facts (RED: 21).
- (2) The mutant check: each of the six broken facts is flagged.
- (3) Step 1c posed on its own decides each `seq.last_indexof` link, with
  a SAT companion. RED: SAT. Every such link is valid; there must be at
  least 19 (RED: 14).
- (3) End to end, under `seqQueryRLimit = 2_000`:
  - the `endsWith` query above. RED: step 3's "was not decided".
  - `s.rfind(':') > 200 and ':' notin s`. Already `sxUnsat` at 58e52af,
    by step 3. It is now decided by step 1c.

  The companion `rfind > 3 and in` stays `sxSat`.
- The `>= 182` floor.

Re-pinned: `phase15_CR2_cachekey` (181 -> 182; 179 -> 181 was S8ao's).

*Different mechanisms, reported and not fixed here.*
- **Step 1 itself can run out of budget.** `s.len > 10 and s[7] == ':'
  and s.rfind(':') < 7` and `s.find(':') >= 0 and s.rfind(':') <
  s.find(':')` are UNSAT on their own. Under `seqQueryRLimit = 2_000`, step
  1 (the capped one-shot solve) is canceled. On Z3 4.13.4 that happens at
  the default 20M for the second query, and at 2,000 for `':' in s and
  s.rfind(':') < 0`. Step 1c runs only after an UNSAT in step 1, so it is
  never reached. Step 3 is canceled too, and step 1b's fallback after (3)
  takes no facts. The links that would decide these are pinned at step
  1c's level. Running the facts in that fallback would decide them, but
  the fallback's context cost is what S8v measured against step 1b.
- **`L` at least every found first index is not emitted** (see Validity
  above). A query refuted only through it (`rfind < find` with both
  found) is not decided by step 1c.
- **`str.replace_all` is unreachable from the walker.**
  `Z3_mk_seq_replace_all` sits behind nim-z3's `-d:z3WithSeqReplaceAll`,
  and the walker does not lower `strutils.replace` to it. The facts
  serve parsed queries only.
- **The equality classes are syntactic over the roots.** Only a sequence
  equality the roots mention (outside quantifiers) joins two classes;
  each link it enables is guarded by it, so one under a disjunction or a
  negation stays sound. An equality the query implies without stating it
  (`len(t) = 1 and str.to_code(t) = 58`) is not seen.

**`closureForcedUnknown` needs more than a propagation fix — round 2
correction.** Round 1 argued the closure veto is redundant "once the descent's
taint joins the calling path". Verified: **most `closureCallErrors` emitters
are not descents.**

- `lowerHofCall`'s filter/map/fold declines (`runtime.nim:12505-12586`) return
  a **fresh unconstrained value** (`allocateSym(…, "__hofFilterUnsupported"` /
  `"__hofMapUnsupported"` / `"__hofFoldOpaque"`) into expression position, and
  write only `currentClosureCallErrors` + a ptr-cast `sawUnknown`. They do
  **not** set `loweringDidDegrade`, so `drainPendingLowerEffects` never taints
  the consuming path.
- `ceInlineBudgetExceeded` (`runtime.nim:11683-11691`) does `w.sawUnknown =
  true; return funcApp` — same shape, no path taint.
- The closure zero-default failure (`runtime.nim:11815-11823`) likewise.

Delete the veto without converting these, and a witness flowing through
`__hofFilterUnsupported` is reported `sxSat` on a clean path with no replay
gate — the S1 failure class, reintroduced by the slice that was supposed to be
a simplification. **Precondition:** enumerate every
`closureCallErrors`/`currentClosureCallErrors` emitter and route each
value-substituting one through `w.degrade` + path taint (or the lowering sink).
That is slice S7, and veto deletion (S9) is gated on it.

Net effect: three parallel unknown-forcing mechanisms (`sawUnknown`,
`capForcedUnknown`, `closureForcedUnknown`) collapse into **one lattice plus
one structural invariant**. This is a strict simplification of the verdict
rule, not an addition to it — but it is reached in three slices, not one.

**As landed (S8x, walker 171, no bump) — S8t2's remainder: the
compile-time VM's `let` aliasing.** S8t2 found that in Nim's compile-time
VM `let top = stack[^1]` binds the seq slot itself, so a later write to
that frame showed through `top`. The whole symex front end runs in that VM:
the parser, the type bridge, the name scopes and the macros' own helpers.
S8x audited it.

*What the VM does* (probed on Nim 2.2.10 patched, `const` against native,
pinned in the test file):

- A `let` of any non-scalar location aliases it: a seq or array element, an
  object or tuple field, a `Table` value, or a whole local seq, string,
  object or `set`. A tuple unpacked from one of these aliases it too.
  Any in-place write to that location or anything inside it shows through
  the `let`: a field write, `add`, `setLen`, `incl`, a nested `[]=`, a
  `var`-parameter callee. So the hazard is wider than seq elements.
- A non-`var` parameter aliases the caller's location the same way, while
  the callee changes that location through a ref.
- `var`, `result =`, a proc's return value, `pop`, a slice and a tuple
  constructor all copy. Replacing the whole location (`s[i] = v`,
  `obj.f = v`) detaches the `let`, which keeps the old value.
- Scalars are copied into registers. A ref (`NimNode`, `IRExpr`, `IRStmt`,
  `IRType`) is shared by design, so aliasing one changes nothing.
- `for` values match native: `items` yields `lent` there too.

*Method.* Scope: every file under `src/nelli` that declares a macro or a
`compileTime` proc, plus everything the symex macros call at expansion
time. That is `dsl_parser`, `dsl_typebridge`, `scoped_names`,
`exn_hierarchy`, `stdlib_models`, `types`, the `symex.nim` macro helpers,
and the macros in `fuzzmacro`, `derive`, `dsl`, `coverage`, `mutation`,
`concolic`, `strategy` and `parallel`. A scan listed every `let` bound to a
location (344), every `result =` of one, every call that passes a `ctx`
value field, and every `for` loop that writes to its own container. Each
hit was then classified by hand from its type and from what runs while it
is live.

| Site | Binding | Type | Written in place while live | Class | S8x |
|---|---|---|---|---|---|
| `boundEmittedDepth` (S8t2) | `let n = stack[^1].n`, `let i = stack[^1].i` | `NimNode`, `int` | `stack[^1].i`, `.h`; `add`/`pop` | safe (S8t2's fix) | pinned |
| `resolveBreak` | `let t = ctx.procScoped.jumpTargets[i]` | `JumpTarget` (object) | `breakVia(ctx, i)` mints `brkLabel` in that element | **latent**: `t` is not read after the call | a `template` over the index, as `breakVia` / `resolveContinue` |
| `ensureProcRegistered` | `let savedProcScoped = ctx.procScoped` | `ProcScopedCollectors` (object) | the callee's pre-passes and walk fill `ctx.procScoped` | **latent**: safe only because the next statement replaces the whole record, which detaches the `let`; a partial reset would make the restore a no-op | a `var` |
| `lowerShortCircuitParts.nest` | `result = parts[k].pre`, then `result.add` | `seq[IRStmt]` | `result` | safe: `result =` copies | pinned (shape) |
| `popJumpTarget` callers | `let jt = ctx.popJumpTarget()` | `JumpTarget` | later pushes, `brkLabel` mints | safe: `pop` copies | pinned (shape) |
| `enterNameScope` / `leaveNameScope` (`ensureProcRegistered`, `parseProcAsValue`) | `result = nameScope`, `let savedNames = enterNameScope()` | `NameScope` (object of tables) | field resets, then the callee's claims in place | safe: `result =` copies | pinned on the real module |
| caseNarrow push / read | `(subjectRepr: ..., tags: narrowTags)`; `for t in caseNarrow[i].tags` | tuple ctor; `int` values | nothing during the read | safe | — |
| IRType `==` (`types.nim`), `emitMVBranch` (`symex.nim`) | `let bx = b.mvAxes[i]`, `let barm = bx.arms[k]`, `let ax = ty.mvAxes[axisIdx]`, `let elseArm = ax.arms[..]` | `VariantAxis`, `VariantArm` | nothing (read-only) | safe | — |
| `ancestorsOf` (`exn_hierarchy`) | `let parent = userExnHierarchy[cur]` | `string` | nothing | safe | — |
| `emitWitnessTuple` (`symex.nim`) | `let (savedCtx, savedUsed) = (...)`, `let used = witnessRefCtxUsed` | `NimNode`, `bool` | whole reassignment | safe | — |
| scalar `ctx` saves (`savedInGuardCond`, `isIndexConv`, `cap`, `prior`) | `let x = ctx.<field>` | `bool` / `int` | — | safe | — |
| the other ~330 location `let`s | `let x = n[i]`, `impl[3]`, `cls.ty`, `parsed.bodyNimNode`, ... | `NimNode` / IR refs / scalars | — | safe | — |
| non-`var` params | the only call passing a `ctx` value field alongside `ctx` is `breakVia(ctx, ctx.procScoped.jumpTargets.high)` | `int` | — | safe | — |

No instance is live: no `let` copy is read after an in-place write to its
location. With no live instance there was no product RED. The RED is the
new source pin, which failed on the two latent lines before the fix.

*IR identity.* Neither change alters the IR. `canonicalize(prog)` and
`repr(prog)` were dumped at 5f4c2bb and again at 219f152 (after S8u),
each against this slice, and for `s8m_exits` and
`r6_r4_collector_scoping` once more at 47c70d1 (after S8w), for every SUT that
these suites pass to `symexFind`: `s8m_exits` (26, labelled breaks),
`s8l_exits` (58), `s8e_scoping` (35), `r6_nulwitness` (9),
`r6_r4_collector_scoping` (6, the collectors' save/restore) and
`r6_a3_variantconstruct_sym` (10, case narrowing). The dumps are
byte-identical. There is no walker bump.

Pins: `tests/tsymex_rfc0005_s8x_vm_alias.nim`.
- VM against native, each evaluated by `const` and at run time:
  - S8t2's frame (VM 7, native 0) and its plain-locals fix.
  - An element bound before a `var`-parameter callee writes it (latent (a)'s
    shape; VM `"brk1"`, native `""`), and the index read that fixes it.
  - A ref's value field: `let` aliases, a whole reset detaches, `var`
    copies (latent (b)'s shape and fix).
  - `result =` and `pop` copy.
  - A whole local string, a local `set` and a non-`var` parameter alias.

  A toolchain that changes any of these fails here first.
- `enterNameScope` / `leaveNameScope` on the real module: leaving a
  callee's scope drops its renames and keeps the caller's.
- Source pin: no `let` in `dsl_parser.nim` binds a `ctx.procScoped` record
  or element (`.len` / `.high` excepted). RED: `1331: let t =
  ctx.procScoped.jumpTargets[i]` and `10497: let savedProcScoped =
  ctx.procScoped`.

*Different mechanisms, reported and not fixed here.*
- **Only `ctx.procScoped` is mechanically guarded.** The VM hazard covers
  every non-scalar `let`, and a non-`var` parameter, but a general lint needs
  types. A line scan cannot tell a `NimNode` `let` (safe) from an object
  `let`. The next value-typed save/restore added to the front end is
  guarded only by review and by this note.
- **The runtime walker has the same textual shapes and is not affected.**
  Examples are `runtime.nim`'s `let savedStack = w.frame.handlerStack` before
  `setLen`/`add`, and `let byRefEntry = descentEnv` before `descentEnv[...] =`.
  They compile to native code, where `let` copies.

**As landed (S8ab, no bump) — S8x's remainder: a type-aware guard,
across the whole scope.** S8ab replaced S8x's one-file/one-pattern
source-text pin with a typed-AST walker: `getImpl()` on every top-level
routine in the same 15 files S8x's own audit table covers (`{.all.}` on
each `import`, since both of S8x's own findings were unexported procs a
plain `import` cannot see), walking every `nnkLetSection` whose RHS is
`nnkBracketExpr`/`nnkDotExpr`/`nnkSym` and whose bound name's
`getTypeInst().typeKind` is `ntyObject`/`ntyTuple`/`ntySequence`/
`ntyString`/`ntySet`/`ntyArray` (never `ntyRef`) — Option 1 of the
slice's own brief, implemented as written. A companion non-`var`-param
check flags a value-typed parameter only when a SIBLING `ref` parameter,
mutated in place in the same body, reaches the same field type
(`paramThenCallerWriteThroughRef`'s own shape) — a structural-only
version (any non-`var` value parameter, unconditionally) produced 265
hits across this scope, almost all ordinary read-only `string`/`seq`
parameters, and was rejected for exactly the false-positive explosion
the slice's brief rules out.

Run across the real scope today: four `let` hits, all already in S8x's
own table as reviewed-safe (`types.nim`'s `IRType` `==` and `symex.nim`'s
`emitMVBranch`, both reading a `VariantAxis`/`VariantArm` element with
nothing written while the binding is live) — allowlisted, one entry
each, in `tests/tsymex_rfc0005_s8ab_letaudit.nim`. Zero param hits.
RED, taken from S8x's own base (5f4c2bb): `resolveBreak`'s
`let t = ctx.procScoped.jumpTargets[i]` and `ensureProcRegistered`'s
`let savedProcScoped = ctx.procScoped`, replicated verbatim as unused
fixture procs on the real `ParseCtx`/`ProcScopedCollectors`/`JumpTarget`
types so the guard proves it still flags the exact historical shape.

*Different mechanisms, reported and not fixed here.*
- **A `[]`-style hazard reached through a proc call (Table's `[]`, a
  distinct wrapper's `[]`) types as `nnkCall`, not `nnkBracketExpr`, and
  is not covered.** Widening the RHS-shape check to "any `[]` call" was
  tried and immediately caught STRING SLICING (`s[0 .. ^2]`, which always
  copies) as a false positive — slicing lowers through the same `[]`
  call. No confirmed compile-time Table-value instance exists in this
  scope today.
- **The param check's "same type reachable" test compares `repr` text**,
  not true structural/generic identity, and walks a ref param's field
  graph only 3 levels deep.
- **A generic routine never instantiated in this scope's own compilation
  unit** yields `getImpl()`'s un-instantiated generic tree; a `let`/param
  depending on an uninstantiated generic parameter cannot be classified
  and is silently skipped, the same way an unresolvable type already is.
- **The guard is test-only reflection, not a build-time lint.** It runs
  once, in `tests/tsymex_rfc0005_s8ab_letaudit.nim`, not on every
  compile; a new hazard is caught the next time that suite runs, not at
  the point it is written.

**As landed (S8af, no bump) — S8ab's remainder: closing the four
reported gaps.** Same file (`tests/tsymex_rfc0005_s8ab_letaudit.nim`);
no walker/IR change, so no `symexWalkerVersion` bump.

1. **Table/`[]`-via-`nnkCall` aliasing.** A new `calleeReturnsVar`
   resolves the callee of an `nnkCall` RHS/LHS-receiver through
   `symKind`/`getImpl()` and reads its FIRST formal's type: `var T`
   (Table's mutable `[]`) is a real aliasing shape and is now walked the
   same as `nnkBracketExpr`; a plain-value or `lent T` return (string/seq
   slicing, Table's read-only `[]`) is not. This is the distinction-by-
   resolved-symbol S8ab's own note said was needed, not distinction-by-
   syntax — the widened-syntax version S8ab already tried and rejected
   (flagging every `[]` call) is exactly the string-slicing false positive
   this now avoids by checking the return type instead. Probed against
   real Table overloads before writing the fixture (`probe_vm_table2.nim`,
   `probe_lent2.nim`): `` `[]`(t: var Table[K,V], k: K): var V `` vs. the
   read-only/`lent` overloads differ exactly as assumed.
2. **Type identity.** `collectFieldTypes` now collects the sibling
   fields' `NimNode` types (via `getTypeInst()`), and `walkParams`
   compares them with `sameType`, not `repr` text. RED fixture: a field
   reached only through a `type X = Y` alias — repr text diverges
   (`"FxIntSeqAlias"` vs `"seq[int]"`) where `sameType` does not (probed,
   `probe_alias_mismatch.nim`). The 3-level field-walk depth bound is
   unchanged; see the residual list below.
3. **Generic procs.** Diagnosed the actual mechanism S8ab's note
   described only as "silently skipped": an uninstantiated generic's
   `getImpl()` tree binds `let`/param names as `nnkIdent`, not `nnkSym`
   (`probe_bare_generic2.nim`), so `getTypeInst()` is never reachable on
   them. `auditGenericInstantiation` forces a concrete instantiation by
   passing a CALL EXPRESSION (not a bare identifier) as a `typed` macro
   parameter — this resolves to the concrete instantiated symbol, whose
   `getImpl()` tree binds every name as `nnkSym` as usual, and hands it to
   the existing `walkLets`/`walkParams` unchanged. RED fixture
   (`fxGenericAliasShape[T]`) proves the bare walk misses the hazard and
   the forced-instantiation walk catches it. Wired to the one real-scope
   generic this audit found actually instantiated from compile-time-VM-
   reachable code: `traceOneCallBoundary[seq[NimNode]]`, called un-quoted
   from `symexFindAllWitnesses`'s own macro body (`symex.nim:2826`) —
   audited clean (zero hits). The mechanism generalizes to any other
   instantiation; it was not run against every generic-bracketed routine
   in the 16-file scope (37 by a column-0 `[` scan, mostly in
   `strategy.nim`) — see the residual list below for why most of those
   don't qualify.
4. **CI coverage.** `symex-mingw.yaml` already ran this suite (auto-
   derived `tsymex_*` corpus from `nelli.nimble`'s `test` task —
   unchanged). Neither fuzzer leg did: `tsymex_rfc0005_s8ab_letaudit`
   matches neither `fuzzer-mingw.yaml`/`fuzzer-msvc.yaml`'s glob
   (`^(tfuzz|tdb|tengine_)...`) nor their named-contract-test list. Added
   to both legs' `foreach ($named in @('tsmoke', 'trequiresinit', ...))`
   list, so the guard now runs under gcc (Linux, via `dt-bounded.sh`),
   mingw, and MSVC. There is still no CI leg that runs `nimble test`
   itself on Linux; that gap is pre-existing, out of this slice's scope,
   and is what `scripts/sweep.sh`'s manual gate stands in for.
5. **Scope.** Confirmed the existing 15-file scope by re-tracing each
   file's compile-time-VM reachability from S8x's own rationale, and
   found one omission: `smt/scan.nim`'s `scanStmt`/`scanCall`/`scanAll`
   are called directly (un-quoted) from `symexFindAllWitnesses`'s macro
   body (`symex.nim:2826-2828`) — the same "called from inside a macro's
   own un-quoted body" test that put the other 15 files in scope. Added
   as the 16th file; clean (zero new hits). `runtime.nim`/
   `runtime_strings.nim` remain correctly out of scope: every call site
   that reaches them from the audited 16 files is inside a `quote do:`
   block (code that RUNS at the property's own normal runtime, after
   macro expansion has already finished), never called directly from a
   macro's own Nim code the way `scan.nim`'s functions are. The same
   holds transitively for everything reachable only from
   `runtime.nim`/`runtime_strings.nim` (`canonicalize.nim`,
   `abstraction.nim`, `regex_parser.nim`, `concolictaxonomy.nim`,
   `engine/*`, `optbox.nim`, `db.nim`) and for `smt/dsl.nim` (the SMT-LIB
   emission DSL, invoked only from runtime solver calls).

Run across the real 16-file scope today, both gap-1 and gap-2 mechanisms
active: the same four `let` hits as S8ab's own run (already allowlisted,
unchanged), zero param hits, zero new hits from either the widened
`nnkCall` walk or the `sameType` comparison. `dt-bounded.sh c` and
`dt-bounded.sh cpp` both green, 10/10 tests.

*Different mechanisms, reported and not fixed here.*
- **The forced-generic-instantiation mechanism was demonstrated on one
  real-scope generic, not run against all 37 generic-bracketed routines
  in scope.** Most of those 37 are in `strategy.nim`; tracing
  `fuzzMacroImpl` (the one macro body that reaches toward it) shows every
  call into strategy-level generics is built inside a `quote do:` block
  (code that runs at the fuzz campaign's own runtime, not at macro
  expansion) rather than called directly from the macro's own Nim code —
  so most are not actually compile-time-VM-reachable and do not need
  forcing. This was not re-verified macro-by-macro for all 17 macros
  across the scope; a generic proc that IS compile-time-VM-reachable
  through a macro this audit didn't trace is still silently skipped by
  the bare walk until it is individually forced the same way
  `traceOneCallBoundary` was.
- **The param check's sibling-field walk is still bounded to 3 levels
  deep** (unchanged by the `sameType` fix, which corrects identity
  comparison at whatever depth is reached, not the depth bound itself).
- **A generic routine never instantiated anywhere in this scope's own
  compilation unit** still yields an un-instantiated `getImpl()` tree
  with no `typed` call expression available to force through
  `auditGenericInstantiation` — unclassifiable, same as before S8af.
- **The guard is still test-only reflection, not a build-time lint**
  (unchanged from S8ab's own note).

**As landed (S8ah, no bump) — S8af's remainder: mechanical macro-by-macro
reachability, unbounded field-graph depth, forced-generic completeness,
and a real build-time gate.** The guard's own duplicated copy moved out of
`tests/tsymex_rfc0005_s8ab_letaudit.nim` and into a reusable library,
`src/nelli/smt/vm_alias_guard.nim`, so the SAME mechanism can run both as
a test (`check`) and as an opt-in build-time gate (`doAssert`) on the real
symex compile path — see item 4 below. No walker/IR change; no
`symexWalkerVersion` bump.

1. **Macro reachability, made mechanical.** S8af traced ONE generic
   (`traceOneCallBoundary`) by hand. S8ah replaces the hand trace with
   `vmGuardWalkForGenericCalls`: for every macro in the 16-file scope,
   walk its typed `getImpl()` tree for a live `nnkCall`/`nnkCommand` whose
   resolved callee is one of the 37 registered generics —
   TRANSITIVELY through the call graph (a `file:name@line`-keyed visited
   set guards cycles), not just one level deep. The transitive hop is not
   theoretical: `traceOneCallBoundary` itself is never called directly
   from any macro — it is called from `collectStringBackedByteSeqParamsImpl`,
   an ordinary proc, which is what a macro actually calls. A one-level-only
   version of this walk (the first one built) missed the one generic S8af
   had found by hand; the transitive walk catches it and would have
   caught it without S8af's own manual trace.
   `quote do:` blocks need no special-casing: a call written inside one
   lowers to `getAst`/tree-construction code, never a live call to the
   target (probed empirically, `probe_quotedo_reach.nim`), so the walk
   naturally sees only genuine compile-time-VM execution — confirmed by a
   dedicated fixture pair (`s8ahFxDirectGenericCall`/
   `s8ahFxQuotedGenericCall` in the test file): the direct call is flagged
   reachable, the quoted one is not.

   *Macro count correction.* The fence title (and S8af's own residual
   note) say "17 macros". Counted mechanically
   (`extractTopLevelMacroNames`, pinned by a new test): the real 16-file
   scope has **22** unique macro names, across 7 of the 16 files (the
   other 9 — `dsl_parser.nim`, `dsl_typebridge.nim`, `scoped_names.nim`,
   `exn_hierarchy.nim`, `stdlib_models.nim`, `types.nim`, `scan.nim` —
   declare none). "17" matched neither the unique-name count nor the raw
   `macro` keyword count (also 22 — no macro name in scope is overloaded
   the way `coverage.nim`'s `logCmp` proc is). Per the "RFC status lines
   lag git" lesson, corrected here rather than propagated.

   *Macro-by-macro evidence table* (mechanical walk output, not a manual
   trace):

   | File | Macro | Reaches one of the 37 generics? |
   |---|---|---|
   | symex.nim | symexForAll | no |
   | symex.nim | replayWitness | **yes** -> `traceOneCallBoundary` |
   | symex.nim | symexFind | **yes** -> `traceOneCallBoundary` |
   | symex.nim | concolicCollect | **yes** -> `traceOneCallBoundary` |
   | symex.nim | concolicFlip | **yes** -> `traceOneCallBoundary` |
   | symex.nim | assertCoveredBy | **yes** -> `traceOneCallBoundary` |
   | symex.nim | symexCacheKeyForFn | **yes** -> `traceOneCallBoundary` |
   | symex.nim | saveSymexWitness | **yes** -> `traceOneCallBoundary` |
   | symex.nim | loadSymexWitnesses | **yes** -> `traceOneCallBoundary` |
   | symex.nim | saveSymexVerdict | **yes** -> `traceOneCallBoundary` |
   | symex.nim | loadSymexVerdict | **yes** -> `traceOneCallBoundary` |
   | symex.nim | symexFindAllWitnesses | **yes** -> `traceOneCallBoundary` |
   | fuzzmacro.nim | fuzz | no |
   | derive.nim | arbitrary | no |
   | dsl.nim | rejectStrategyTypedesc | no |
   | dsl.nim | property | no |
   | coverage.nim | covercmp | no |
   | coverage.nim | cover | no |
   | mutation.nim | mutantsOf | no |
   | concolic.nim | concolicAssist | no |
   | strategy.nim | map | no |
   | parallel.nim | jitterPoints | no |

   11 of the 22 macros reach `traceOneCallBoundary` transitively (all in
   `symex.nim`, all funneling through the same parse/IR pipeline); the
   other 11 reach none of the 37. Every call any of the 22 macros makes
   into `strategy.nim`'s 31 registered generics (`newStrategy`,
   `generate`, `just`, `sampledFrom`, `map`, `filter`, `recursive`, etc. —
   the bulk of the 37) is built inside a `quote do:` block in
   `fuzzMacroImpl`/`arbitraryImpl` — S8af's manual claim, now mechanically
   confirmed rather than asserted.

2. **Forced-generic completeness.** With reachability now mechanical,
   "never instantiated" classifies itself: exactly ONE of the 37 registered
   generics (`traceOneCallBoundary`) is VM-reachable from any macro in
   scope, and it is the one already forced (S8af). The other 36 are not
   left "unclassifiable" (S8af's own residual note) — the SAME walk that
   finds `traceOneCallBoundary` reachable also establishes, by finding no
   path to them from any of the 22 macros, that none of the other 36 is
   compile-time-VM-reachable at all, so none needs forcing. A completeness
   test (`vmGuardForcedGenerics`, a global `{.compileTime.}` list every
   `vmGuardAuditInstantiation` call appends to, shared across modules) now
   fails closed if the mechanical walk ever finds a NEW reachable generic
   with no matching forced-instantiation audit.

3. **Field-graph depth.** `collectFieldTypes`'s 3-level bound is replaced
   with a full walk guarded by a `sameType`-keyed visited list — the depth
   bound's only real job was stopping an infinite loop on a
   self-referential type, which a visited set does at any depth. RED,
   observed against the OLD code (`probe_fielddepth_red.nim`, deleted
   after confirming): a hazard 5 field-hops deep
   (`FxHolderDeep.nxt.nxt.nxt.nxt.xs`) produced `siblingFieldTypes.len=0,
   matched=false` — a real false negative. GREEN: the same shape, plus a
   second fixture reachable only through a self-referential type
   (`FxCyclicInner.self: FxCyclicInner`) proving the visited set both
   catches the hazard AND terminates (this fixture compiling at all is
   part of the termination proof).

4. **Build-time check.** The exact same mechanism (now living in
   `src/nelli/smt/vm_alias_guard.nim`) is wired into `symex.nim`'s and
   `concolic.nim`'s own trailing `when defined(nelliVmAliasAudit): ...
   static: doAssert ...` blocks — a genuine build-time gate on the real
   symex/concolic compile path, not only the test file's own
   unconditional `check`s. Opt-in via `-d:nelliVmAliasAudit`: an ordinary
   `import nelli/symex` compile evaluates none of this (the `when
   defined` guard means the block is not even semantically checked when
   the define is off), so it costs library users nothing.
   *Measured cost* (podman/gcc, this worktree): compiling
   `tests/tsymex_phase15_F8_smoke.nim` (imports `symex.nim`) went from
   29.7s to 44.7s with the define on (+15.0s); compiling
   `tests/tfuzzconcolicassist.nim` (imports `concolic.nim`) went from
   34.5s to 49.7s (+15.2s) — both from the 16-file self-audit's `getImpl`
   reflection plus the new transitive reach-walk, paid once per compile
   unit that imports the audited module with the define on.
   *CI wiring, deliberately narrow*: because the cost is per-COMPILE
   (not a one-time cost across a whole CI run), the define is turned on
   for exactly ONE suite per leg — `tsymex_rfc0005_s8ab_letaudit` itself,
   which already imports both `nelli/symex {.all.}` and `nelli/concolic
   {.all.}` — rather than the whole corpus/glob in any of the three legs.
   `symex-mingw.yaml` singles it out by name inside its derived-corpus
   shard loop (`run-ci-suite.ps1 -ExtraNimArgs @('-d:nelliVmAliasAudit')`,
   reusing that script's existing `-ExtraNimArgs` parameter — precedent
   `-d:symexCiLeanB5`); `fuzzer-mingw.yaml`/`fuzzer-msvc.yaml` single it
   out inside their existing named-contract-test loop. Applying the
   define to every suite in any of the three legs would have multiplied
   the measured ~15s per compile across ~200+ suites (symex-mingw's
   derived corpus) for zero additional coverage — no suite besides this
   one self-audits `symex.nim`/`concolic.nim`'s own routines at build
   time. Verified locally (podman) before pushing: both
   `tests/tsymex_phase15_F8_smoke.nim` and `tests/tfuzzconcolicassist.nim`
   compile clean with `-d:nelliVmAliasAudit` (no cycle error — the
   concolic.nim -> symex.nim -> vm_alias_guard.nim -> concolic.nim import
   cycle this design deliberately avoids by having `vm_alias_guard.nim`
   self-audit only 14 of the 16 files, with `symex.nim` and `concolic.nim`
   each self-auditing their OWN routines independently, with no `{.all.}}`
   import of themselves).

Run across the real 16-file scope today: the same four `let` hits as
S8af's own run (already allowlisted, unchanged), zero param hits (the
unbounded field walk finds no NEW real-scope hazard), one reachable
generic (`traceOneCallBoundary`, already forced). `dt-bounded.sh c` and
`dt-bounded.sh cpp` both green, 15/15 tests (5 new: two field-graph
fixtures, two reachability-mechanism fixtures, the macro-count and
single-reachable-generic pins).

*Different mechanisms, reported and not fixed here.*
- **A zero-required-argument macro passed bare as a `typed` macro
  parameter is auto-invoked by Nim, not resolved to its own symbol** —
  discovered while building the reachability-mechanism fixtures (a
  zero-arg fixture macro's bare name resolved to `nnkIntLit`, the RESULT
  of calling it, never `nnkSym`; probed, confirmed with a required dummy
  parameter added). Checked against the real 16-file scope: none of the
  22 real macros has zero required parameters (`command grep -nE '^macro
  [a-zA-Z_][a-zA-Z0-9_]*\*?\(\)'` and the bare `macro name:` form both
  return no matches), so this does not hide a real-scope reachability
  false negative today — but the mechanism itself would miss one if a
  future zero-arg macro were added to scope. Not fixed here: doing so
  would mean detecting and special-casing the auto-invoke shape inside
  `vmGuardAuditRoutine`/`vmGuardAuditMacroReachWithSpecs`, which is a
  change to the audit macros themselves, not to this slice's four items.
- **The build-time gate runs on one suite per CI leg, not the whole
  corpus.** A real regression in `symex.nim`'s or `concolic.nim`'s own
  routines would still be caught (the gate's `doAssert`s fire on ANY
  compile of that module with the define on, and this one suite's compile
  happens on every leg run), but the define is not exercised against
  every OTHER test file's own compile of those modules — deliberate, per
  item 4's cost measurement above, not an oversight.
- **The guard's own walker (`extractTopLevelNames`/`extractTopLevelMacroNames`)
  is still a column-0 source scan**, with the same backtick-operator and
  unusual-multi-line-signature caveats S8ab's own note first listed —
  unchanged by this slice.

**As landed (S8ad, walker 175) — S8ac's remainder.**

*A local distinct value allocates its own sort.* `D(x)` is the parser's
identity (S8p), so `var m = Meters(0)` binds the bare base. The first
borrowed arithmetic on it (`m + Meters(1)`) re-boxes the result as an
`svDistinct`, and `reboxDistinct` assumed the distinct sort existed because
"the operands were already allocated as this distinct type". With no
`Meters` parameter, field or call result, nothing had allocated it:
`weInternalWalkerFault` ("reboxDistinct: distinct sort `Meters` not
allocated"). The borrow node now carries the distinct TYPE
(`IRExpr.borrowDistinctTy`, which replaces `borrowDistinctName`), and the
re-box takes the sort from `ensureDistinctSort`. That is the sort half of
`allocDistinctSym`, factored out, and it is created at most once per run as
before.

With the sort in place, a probe found a second fault on the same values. A
boxed result met its bare base in the element fold of a symbolic array read
(`var a = [Meters(1), Meters(2), Meters(3)]; a[0] = a[0] + Meters(2); a[i]`):
`iteSV: kind mismatch svBV64 vs svDistinct`. The base is the whole
observable value, since every read ejects and `retBindEq` binds through it.
So `iteSV` now merges the two bases when exactly one side is boxed.

*The Int quotient's linear bounds sit beside every query.* A scan offset
(`start`, a width-stamped Int) divided by a bitvector parameter (`y`, read
through `bv2int`) is Z3's Euclidean `div` inside `truncDivInt`'s
adjustment. Z3 relates `start div y` to `start` only through the product
`y * q`, which is its nonlinear core. Under the sequence theory that core did
not refute the UNSAT shapes within `seqQueryRLimit`. Its theory-free
re-check (step 1b) did not either, so each ran to 40M steps and
`sxUnknown`. Without a scan, `start` stays a bitvector (`bvsdiv`), and the
same shape was UNSAT in 2.9M.

`checkCapped` now decides every query (plain and capped, every step) with
`divRangeFacts` asserted beside it. For each Int `a div b` and `a mod b` in
the query, these are the linear bounds that hold for a divisor of known sign:
- `0 <= r <= |b| - 1`, and `r <= a` for `a >= 0`.
- `e` between `a` and 0, and within `a / 2` once `|b| >= 2`. The bounds are
  given per sign of `a` and `b` in the doc comment.
- When `|a| < |b|`, the pair itself: `e` is 0 or `+-1`, and `r` is `a`,
  `a + b` or `a - b`.

The last group came from symex-mingw. On Z3 4.13.4 the bounds alone refuted
`start > 0` but not `start < 0`: `truncDivInt`'s quotient equals `start`
only when `e == start == -1` with `r == 0`, and 4.13.4 did not see that
`r == y - 1` there within 40M steps. Stating the pair for `|a| < |b|` makes
that case linear on both versions.

The remainder's twin, `start mod y <= -y`, also needed the Int value of the
negated bitvector. `-y` lowers to `0 - y`, and Z3 did not connect
`bv2int(0 - y)` to `bv2int(y)` beside the remainder. So `bv2int(-y)` (both
the `bvneg` and the `0 - y` form, unsigned and signed) is asserted equal to
`2^W - bv2int(y)` (0 at 0), or to `-sbv2int(y)` (`y` itself at `low`).

Each fact is a theorem of the Euclidean pair or of two's complement, not a
constraint on the input, so the query's models are unchanged. The pin checks
every one against Z3's own operators on a grid of numerals. Decl kinds are
read off the linked Z3, as `seqCapKinds` does, so the facts find the same
terms on 4.13.4 and 5.1.

With a scan, default settings (`isOptimised`), steps for the whole walk
(`rlimitDelta`). The base column is the probe on Z3 5.1 with
`queryRLimit = 20M`. The S8ad columns are the pinned suite, on the
container's Z3 5.1 and on Z3 4.13.4 (symex-mingw's version, run locally with
its Linux build):

| Shape (UNSAT unless noted) | Base (5.1) | S8ad (5.1) | S8ad (4.13.4) |
|---|---|---|---|
| `start < 0 and y > 1 and start div y == start` | 40.4M, `sxUnknown` (260 s) | 0.88M | 1.19M |
| `start > 0 and y > 1 and start div y == start` | 80.5M, `sxUnknown` (490 s) | 0.85M | 1.08M |
| `start < -1 and y < -1 and start div y <= start` | -- | 1.13M | 1.14M |
| `start < 0 and y > 1 and start mod y <= -y` | 40.4M, `sxUnknown` (150 s) | 1.19M | 1.02M |
| `start < 0 and y > 1 and start mod y > 0` | 0.20M | 0.51M | 0.64M |
| `start > 0 and y > 1 and start mod y >= y` | 0.82M | 0.84M | 1.09M |
| `start mod y <= 1 - y` (SAT) | -- | 0.20M | 0.27M |
| `start div y == start + 1` (SAT) | -- | 0.48M | 0.50M |
| exact unchecked `start div y == start`, `start < 0` / `> 0` | past the 1500 s probe bound | 0.69M / 0.93M | 0.87M / 0.98M |

Without the `|a| < |b|` group, 4.13.4 ran `start < 0` (both settings) to
40M and `sxUnknown`, and `start mod y <= -y` to 7.2M.

S8ac's `lowerArith` change (the linear `low(T) div -1` wrap) is not on this
slice's base. The exact-unchecked rows decide here without it.

Pins: `tests/tsymex_rfc0005_s8ad_remainder.nim`, with a `.nim.cfg` that sets
`-d:symexQueryStats`.
- (1) A local distinct value: borrowed sums on a straight line, on one
  branch, in a loop, and in a short-circuit operand, plus a boxed element
  beside bare ones read at a symbolic index. Each target is SAT with its
  witness checked, and each dead twin is UNSAT. RED: `weInternalWalkerFault`
  on every one; the array read then hit `iteSV: kind mismatch`.
- (2) The div and mod shapes above. Each dead shape is `sxUnsat` within 3M
  steps with no `beSolverUndef`. RED: `sxUnknown` at 40M and 80M. The SAT
  neighbours (`start mod y <= 1 - y`, `start div y == start + 1`) keep a
  witness that compiled code agrees with.
- (3) Every fact (19 per `(a, b)` pair) is valid for `a` in -13..13 and `b`
  in -6..6 (not 0), and
  for every 8-bit `y`, both negation forms, both signednesses.
- The `>= 175` floor.

*Different mechanisms, reported and not fixed here.*
- **An uninitialized local array with an element write is a walker fault.**
  `var a: array[3, int]; a[0] = a[0] + 2` (or `a[1] = x`), then `a[i]`, is
  `weInternalWalkerFault` (`iekIndex on non-array kind=svBV64`), and the same
  happens at the base. The parser declines the zero-init (`zeroValueForType`
  has no array arm: `feUnsupportedStmtKind`, "zero-init not modeled this
  cycle"). The element write then binds the unbound name to a scalar, and the
  read asserts. It is independent of `distinct`, since `array[3, Meters]`
  faults the same way.
- **The facts cover `div`/`mod` and negation only.** A quotient read
  through other bitvector arithmetic (`bv2int(y + 1)`, `bv2int(2 * y)`) gets
  no bridge. No failing shape was found. The general `bv2int` of `bvadd` /
  `bvmul` identities would touch every stamped-offset query, which is why
  they are not asserted.

**As landed (S8ak, no bump) — S8ah's remainder: zero-arg macro resolution
by symbol, and a real-parse name scan.** Pure compile-time reflection, no
walker/IR change; no `symexWalkerVersion` bump.

1. **Zero-required-argument macros, resolved by symbol.** `vmGuardAuditNames`
   (the audit entry point every real call site uses — the test file and
   `symex.nim`'s/`concolic.nim`'s own build-time self-audits alike) now
   resolves each name with `bindSym(nm, brForceOpen)` rather than generating
   `vmGuardAuditRoutine(ident(nm), fileTag)` for the compiler to re-semcheck
   as a fresh `typed` argument expression — the exact shape S8ah's own note
   above identified as the auto-invoke trap (a bare zero-arg macro reference
   in an expression-value context has no reading other than "call it", so
   the audit macro would have received the target's own RESULT, never its
   symbol). RED (`s8akFxZeroArgDirectGenericCall`, a genuinely zero-arg
   macro whose body calls `just`, a registered generic in `strategy.nim`):
   missed under the old `ident`-based path; GREEN under `bindSym`, flagged
   reachable like any other direct call.

   *A second, unanticipated scoping problem, found building this against
   the real scope (not just the fixture).* `bindSym` resolves a name
   against the scope of wherever the `bindSym` CALL ITSELF is lexically
   written, not the call site of whatever macro contains it — probed and
   confirmed with a 3-file minimal reproduction (`s8ak_probe_{a,b,c}.nim`,
   deleted after confirming), not shipped. A straightforward port (calling
   `bindSym` directly in `vmGuardAuditNames`'s own body, written in
   `vm_alias_guard.nim`) compiled fine against the 14 files that module
   already self-imports with `{.all.}}`, but failed — "undeclared
   identifier" — auditing `symex.nim`'s own private, generic
   `sortedKeysOf` from the TEST FILE's call site, which imports `nelli/symex
   {.all.}}` but `vm_alias_guard.nim` deliberately does not (that would
   reintroduce the `concolic.nim -> symex.nim -> vm_alias_guard.nim ->
   concolic.nim` cycle S8ah's own build-time-gate design avoids). Fix,
   confirmed by the same probe: `vmGuardAuditNames` now generates, per
   name, a NESTED macro definition (`quote do: block: macro
   vmGuardAuditNameLocal(): untyped = ... ; vmGuardAuditNameLocal()`)
   spliced into the CALLER's own code, so when the compiler processes that
   spliced block it compiles as part of the calling module — the nested
   macro's own `bindSym` call then resolves using THAT module's scope,
   `{.all.}}` imports included. `vmGuardAuditOneSym` itself (the shared
   per-symbol audit body, extracted from S8ah's `vmGuardAuditRoutine`) is
   resolved once, by a same-module `bindSym` call outside the per-name
   loop, and spliced in as an already-resolved symbol, so the generated
   code never re-resolves it by bare name. `vmGuardAuditRoutine` (the old
   `typed`-argument entry point) is retired, not kept dormant: once
   `vmGuardAuditNames` no longer generates calls into it, nothing calls it.

2. **`extractTopLevelNames`/`extractTopLevelMacroNames`, from a real parse.**
   Both now `parseStmt(staticRead(path))` the module and walk the resulting
   typed-AST shape (`{nnkProcDef, nnkFuncDef, nnkMacroDef, nnkTemplateDef,
   nnkIteratorDef, nnkConverterDef}`, unwrapping an `nnkPostfix` export
   marker and joining `nnkAccQuoted` parts for a backtick name) rather than
   scanning source lines for a `startsWith("proc ")`-style column-0 match.
   Checked across the real 16-file scope before changing anything: the OLD
   scan already handles a single-line backtick operator and a multi-line
   parameter list correctly (`command grep` found no real-scope routine of
   either shape that it missed) — the brief's two named cases were not
   where the real gap was. RED (`s8akSplitKeywordOp`/`s8akSplitKeywordMacro`,
   a fixture scan file never compiled, only `parseStmt`'d): a routine whose
   keyword and name sit on different physical lines (valid Nim, confirmed
   by a parse probe) is invisible to the old scan outright — a line
   containing only `"proc"` fails `line.startsWith("proc ")`, so the name
   on the NEXT line is never even searched for. GREEN under the real parse;
   the already-correct single-line-backtick and multi-line-parameter-list
   fixtures are pinned alongside it to prove no regression.

   *Real-scope counts, re-derived mechanically against the new scan* (not
   assumed to carry over from S8ah's count, which used the old scan): still
   **22** unique macro names, still **37** registered generics, still
   exactly **1** VM-reachable (`traceOneCallBoundary`) — no change. The
   split-keyword gap the new scan closes does not exist anywhere in the
   real 16-file scope today (every real routine's keyword and name already
   share a physical line); item 2 is therefore a hardening of the
   mechanism, not a correction of today's counts.

Run across the real 16-file scope today: the same four `let` hits as S8af's
own run (already allowlisted, unchanged), zero param hits, one reachable
generic (`traceOneCallBoundary`, already forced) — identical to S8ah's own
run, confirming neither fix changed what the real scope reports. Both
`symex.nim`'s and `concolic.nim`'s own build-time self-audits
(`-d:nelliVmAliasAudit`) recompiled clean (podman) against the new
mechanism: `tests/tsymex_phase15_F8_smoke.nim` and
`tests/tfuzzconcolicassist.nim` both still pass with the define on. `dt-bounded.sh
c` and `dt-bounded.sh cpp` both green, 24/24 tests (7 new: two
zero-arg-macro-reachability tests, five real-parse-scan tests).

**The full-suite sweep gate was skipped for this slice.** `vm_alias_guard.nim`
is reachable from only two places outside the test file itself:
`concolic.nim:542` and `symex.nim`'s own trailing block, both inside a
`when defined(nelliVmAliasAudit):` guard the sweep never turns on (the
block is not even semantically checked with the define off) — the same
footing S8af's own note already recorded ("the guard is still test-only
reflection, not a build-time lint"), unchanged by S8ah's later build-time
wiring, which only widened what the OPT-IN define covers, not what an
ordinary `nimble test`/`sweep.sh` compile exercises. No normal compile
path changed, so no suite in the sweep could be affected; the two compiles
that DO take the define (verified individually above) are the entire
blast radius, and they're green. A full sweep would have re-certified the
~536 suites S8ah's own gate already covers at the parent sha, for zero
additional coverage of this slice's actual change.

*Different mechanisms, reported and not fixed here.*
- **The build-time gate still runs on one suite per CI leg, not the whole
  corpus** — unchanged from S8ah's own note; still deliberate, same cost
  reasoning.
- **The forced-generic-instantiation mechanism is still only exercised
  against one real generic** (`traceOneCallBoundary`, the only one
  VM-reachable today) — `vmGuardForcedGenerics`'s completeness check would
  still fail closed on a genuinely new reachable generic with no matching
  forced audit, but the mechanism's "force and audit an instantiation"
  half has only ever run against this one case.
- **`vmGuardAuditMacroReachWithSpecs`'s own test fixtures still need a
  required dummy parameter** (`s8ahFxDirectGenericCall`/
  `s8ahFxQuotedGenericCall`) to avoid the auto-invoke trap item 1 above
  fixes in the REAL audit path — the TEST HOOK itself takes a `typed`
  argument (by design, so it can run against a caller-supplied `specs`
  list instead of the real registry) and so still needs its fixtures
  shaped to avoid auto-invoke; not a gap in the real `vmGuardAuditNames`
  path, which item 1 fixes directly.

**As landed (S8ak, second round, no bump) — the line-keyed registry fix
and Linux build-time-audit coverage.** All three Windows legs went red at
the channel tip (`94b8303`, S8ad) immediately after the round above
landed: `symex.nim(3141)`'s and `vm_alias_guard.nim`'s own self-audits
both `doAssert unforced.len == 0`, naming `dsl_parser.nim:
traceOneCallBoundary@7269` as unforced even though it is, in fact,
already forced. Root cause, confirmed by reading the code rather than
assuming: `genericRoutineSpecs*: seq[GenericRoutineSpec]` (the 37-entry
registry) hand-types each generic's declaration LINE as a literal;
`calleeMatchesGeneric` (the eligibility check) never reads `spec.line` —
only `spec.name`/`spec.file` — so that field was already dead for
MATCHING, but `vmGuardWalkForGenericCallsAux` still baked it into the
REACHABLE-generic hit key, while `vmGuardAuditInstantiation`'s own
forced-instantiation key for the very same generic has always derived its
line LIVE from `impl.lineInfoObj.line`. S8ad edited `dsl_parser.nim`
*above* `traceOneCallBoundary`, shifting it from line 7269 to 7270;
`genericRoutineSpecs` still said 7269; the two independently-built keys
silently desynced. Linux never saw it: the sweep never turns on
`-d:nelliVmAliasAudit`, so neither self-audit block is even semantically
checked in any Linux-gated compile, and S8ak's own first round only ran
`letaudit` by hand, pre-S8ad.

1. **Fix: the reachable-generic hit key is now derived from the MATCHED
   CALLEE's own live `getImpl()`**, exactly mirroring what
   `vmGuardAuditInstantiation`'s forced key already did
   (`vmGuardWalkForGenericCallsAux`, `vm_alias_guard.nim`; see that
   procedure's own doc and the module header's item 6 for the full
   mechanism). `calleeMatchesGeneric` (eligibility) is unchanged — it
   never used `spec.line` either. `genericRoutineSpecs`' `line` field is
   left as-is in the tuple (it still tells apart `logCmp`'s two same-file
   overloads, `coverage.nim:540`/`:561`, and `map`'s,
   `strategy.nim:236`/`:303`, for a human reading the table) but is now
   NEVER consulted when building either key — an edit anywhere in the
   file, not just the one line S8ad happened to shift, can no longer
   desync the two sides. `checkUnsatOverTaintOnly` (`types.nim`, the
   coordinator's second named check) carries the same kind of stale
   registry line (hardcoded 3434; real declaration now at 3438, also
   moved by S8ad) but was never actually reachable in the real scope (only
   `traceOneCallBoundary` is), so it never manifested as a CI failure —
   it is fixed by the same change, since the fix touches the KEY
   derivation for every registered generic, not `traceOneCallBoundary`
   specially.
2. **RED test added, reusing existing scaffolding rather than new
   fixtures.** `fixtureGenericSpecs` (the test file's own small
   reachability-mechanism fixture list) already registered
   `fxGenericAliasShape` with a deliberately wrong `line: 0` — pre-existing
   S8ah scaffolding, never actually exercised at the `@line` suffix, since
   the existing checks only `.contains()`-matched a prefix. A new test
   (suite "S8ak: a reachable generic's hit key tracks the live
   declaration, never the registry's hand-typed line") cross-checks
   `s8ahFxDirectGenericCall`'s reach-hit key against a new
   `fixtureForcedGenerics` snapshot (`vmGuardForcedGenerics`, taken AFTER
   this file's own `fxGenericAliasShape[seq[int]]` forcing call, unlike
   the earlier `globallyForcedGenerics` snapshot which runs before it).
   Confirmed RED against the pre-fix key derivation — failure text:
   `reach[0] was ...fxGenericAliasShape@0`, `fixtureForcedGenerics was
   @[..., ...fxGenericAliasShape@394]`, i.e. the exact mismatch class,
   reproduced on demand rather than only at the real scope's one
   instance — then GREEN with the fix applied. The real-scope
   completeness/converse/exact-match checks (`realScopeForcedGenerics`
   and the "exactly 1 of 37" assertion) are also made line-independent
   (a `genericKeyPrefix` helper strips the `@<line>` suffix before
   comparing), so the TEST's own assertions cannot re-introduce the same
   staleness trap by hardcoding a line number either — confirmed by the
   same RED/GREEN run surfacing `traceOneCallBoundary@7270` (today's real,
   live line) where the old hardcoded assertion said `@7269`. A second,
   pre-existing hardcoded-line assertion in the S8ak-item-1 suite
   (`-> strategy.nim:just@130`) was hardened the same way on sight, before
   it could become a second copy of this exact bug.
3. **Linux now exercises the build-time audit.** New
   `tests/tsymex_rfc0005_s8ab_letaudit.nim.cfg` adds `-d:nelliVmAliasAudit`
   — Nim auto-reads a `<file>.nim.cfg` sibling, so `scripts/sweep.sh`
   (which compiles `tests/t*.nim` directly, each via `dt-bounded.sh`,
   with no per-file special-casing) now compiles `symex.nim`'s and
   `concolic.nim`'s own `when defined(nelliVmAliasAudit):` self-audit
   blocks for this ONE suite on Linux too — a future line-shift like
   S8ad's now goes red in the Linux gate, not only on the three Windows
   legs. Scoped to this file alone (Nim's `.nim.cfg` lookup is per main
   module filename): no other suite's compile changes, so the "tell me
   first" condition does not apply and the full-suite sweep is still
   correctly skipped for this slice (below). **Per-compile cost** (podman,
   cpp backend, wall clock via `time scripts/dt-bounded.sh`): 52.9s
   without the define, 70.7s with it — **+17.8s (~+34%)** for this one
   suite's compile; zero cost everywhere else, since no other `.nim.cfg`
   sets the define and it is `when`-gated out of every other compile unit.
4. **Re-verified real-scope counts: unchanged.** Still 22 unique macro
   names, still 37 registered generics, still exactly 1 VM-reachable
   (`traceOneCallBoundary`) — the fix changes how a hit's KEY is built,
   not which generics are found reachable or forced. `dt-bounded.sh c` and
   `dt-bounded.sh cpp` both green at the rebased sha, 26/26 tests (one new:
   the line-keying RED/GREEN mechanism test above).

**The full-suite sweep gate stays skipped for this round too**, per the
same reasoning as the first round above: the `src/` change is entirely
inside the `when defined(nelliVmAliasAudit):`-reachable surface
(`vmGuardWalkForGenericCallsAux`, called only from the opt-in audit path),
and the one compile-affecting addition (`letaudit`'s new `.nim.cfg`) is
scoped to that single suite, verified individually above. No ordinary
`sweep.sh`/`nimble test` compile path changed.

**As landed (S8al, no bump) — S8ak's remainder: the force-and-audit half
of the guard exercised against a fixture generic, and
`vmGuardAuditMacroReachWithSpecs` resolved by symbol.** Pure compile-time
reflection and test-only fixtures; no walker/IR change, no
`symexWalkerVersion` bump.

1. **The force-and-audit half, exercised end-to-end against a fixture
   generic.** In the real 16-file scope, the "a VM-reachable generic with
   no forced-instantiation audit fails the completeness check closed"
   comparison (`vmGuardForcedGenerics`'s own doc; each self-audit's
   `doAssert unforced.len == 0`; the test file's own "every generic the
   real scope finds VM-reachable has a forced-instantiation audit" test)
   has only ever had ONE row to evaluate — `traceOneCallBoundary`, which is
   always forced — so the comparison's FAILING branch had never actually
   run; a regression that broke the comparison itself (the wrong key, the
   wrong list) could not have been caught by the real scope alone. Two new
   fixture generics close this: `s8alFxForcedHazardGeneric` (reachable from
   its own zero-arg macro, `s8alFxDirectForcedGenericCall`, and forced via
   `vmGuardAuditInstantiation`) and `s8alFxUnforcedHazardGeneric`
   (reachable from `s8alFxDirectUnforcedGenericCall`, deliberately never
   forced). RED (podman, reverted after confirming): commenting out the
   forced generic's `vmGuardAuditInstantiation` call turns both of its own
   tests red — `fixtureLetHits` loses the `s8alFxForcedHazardGeneric[instantiated]`
   hit, and the completeness comparison's `unforced.len` goes from 0 to 1.
   GREEN with the call restored: the forced generic's hazard is reported
   (`fixtureLetHits.anyIt(... "s8alFxForcedHazardGeneric[instantiated]" ...)`),
   the forced generic's own completeness comparison reports zero unforced,
   and the SAME comparison run against the deliberately-unforced sibling
   reports exactly one unforced entry — the mechanism fails closed, proven
   by a fixture built to fail it, not only by the one real row that has
   never failed.
2. **`vmGuardAuditMacroReachWithSpecs`, resolved by symbol.** This
   test-only reachability hook took the macro SYMBOL directly as a `typed`
   argument — the exact auto-invoke trap S8ak's item 1 already fixed for
   `vmGuardAuditNames`: a genuinely zero-required-argument macro referenced
   bare in a `typed`-argument position is auto-invoked by Nim (its own
   RESULT arrives in place of its symbol), never resolved to its symbol.
   RED (podman, reverted after confirming): a genuinely zero-arg macro
   passed to the pre-fix hook was silently auto-invoked and its body never
   walked — the reachability check found nothing. Fix, same technique
   `vmGuardAuditNames` already uses (S8ak): the hook now takes the macro's
   NAME (`static string`) and resolves it via `bindSym(name, brForceOpen)`
   inside a nested macro definition spliced into the caller's own code
   (`vmGuardAuditOneSymReachOnly`, the extracted per-symbol body). This also
   let `s8ahFxDirectGenericCall`/`s8ahFxQuotedGenericCall` drop the dummy
   required parameter they carried purely to dodge the trap — both are now
   genuinely zero-arg and still correctly flagged (the direct call
   reachable, the quoted one not).

Run across the real 16-file scope today: unchanged — still 22 unique macro
names, still 37 registered generics, still exactly 1 VM-reachable
(`traceOneCallBoundary`); neither change touches the real registry or
walk, only the test-only fixture-spec hook and two new test-only fixture
generics. `dt-bounded.sh c` and `dt-bounded.sh cpp` both green, 28/28 tests
(3 new: the fixture's hazard-reported test and the two force/unforced
completeness-comparison tests).

**The full-suite sweep gate is skipped for this slice too**, same
reasoning as S8ah/S8ak: the `src/` change
(`vmGuardAuditOneSymReachOnly`/`vmGuardAuditMacroReachWithSpecs` in
`vm_alias_guard.nim`) is reachable only from this one test file, never from
`symex.nim`'s or `concolic.nim`'s own `when defined(nelliVmAliasAudit):`
self-audit blocks (those call `vmGuardAuditNames`, not
`vmGuardAuditMacroReachWithSpecs`), and no other suite's `.nim.cfg` turns
the define on. No ordinary `sweep.sh`/`nimble test` compile path changed.

*Different mechanisms, reported and not fixed here.*
- **The build-time gate still runs on one suite per CI leg, not the whole
  corpus** — unchanged from S8ah's/S8ak's own note; still deliberate, same
  cost reasoning.
- **A generic routine never instantiated anywhere in this scope's own
  compilation unit still yields an un-instantiated `getImpl()` tree, same
  as before S8af** — unrelated to this slice's fixtures, which are forced
  (or deliberately left unforced) by hand, not discovered as
  never-instantiated.
- **The guard's own walker (`extractTopLevelNames`/`extractTopLevelMacroNames`)
  is unchanged by this slice** — S8ak's real-parse scan already covers it.
- **The param check's sibling-field walk and the let/param hazard shapes
  themselves are unchanged** — this slice is scoped entirely to the
  force-and-audit completeness mechanism and one test hook's symbol
  resolution, not to the hazard-detection shapes.
**As landed (S8aj, walker 179) — S8ad's remainder.**

*Rebased a second time, onto S8ac (walker 178).* This slice's branch point
also predates S8ac, which bumped the walker 177->178 for an unrelated
var-parameter write-back and short-circuit-join fix untouched by this
slice's mechanism. No conflict beyond the walker-version doc block and the
two brittle pins (CR2's `==` and this slice's own `>=` floor); S8ac did not
touch `zeroValueForType`, `iteSV` or `divRangeFacts`. 178 -> 179.

*A local aggregate takes Nim's zero, and S8z's parallel fix merges into
one mechanism.* `zeroValueForType` had no arm for an array, an object
(`itTuple`), a seq or a variant, so `var a: array[3, int]` was declined
("zero-init not modeled this cycle") and `a` was left unbound. The first
`a[0] = a[0] + 2` then bound it to a scalar, and the next `a[i]` asserted:
`weInternalWalkerFault`, "iekIndex on non-array kind=svBV64". S8aj's branch
point predates S8z, which found and fixed the same decline independently,
but scoped to ONE call site (the uninitialised-`var` statement parser),
for `itArray`/`itTuple`/`itVariant`/`itMultiVariant` only — not `itSeq`,
and not the omitted-constructor-field path below. `zeroValueForType`
itself now carries the fix for all five kinds (`mkZeroValue(ty)`, which the
walker lowers through `defaultZero`: every element and field gets its own
zero, and a seq is empty; a shape it cannot zero — a variant whose
ordinal-0 tag is not legal — is allocated and degraded there, as any
`iekZeroValue` is; only `itUninterp` still has no zero, and its caller
declines it as before), and S8z's call-site special-case now collapses to
a plain call to `zeroValueForType` — it was identical to this for the four
kinds it covered, and gains `itSeq` for free. No caller of
`zeroValueForType` relied on its old `nil` for these kinds for anything
beyond "decline, and use a never-read placeholder" (checked against every
call site: the CR-2a and P2a degrade paths already taint the path before
their dummy is ever read), so widening it is a pure extension, not a
behaviour change at the sites S8z left alone.

With the zero in place, the loop shape hit a second fault. That shape is
`a[0] = a[0] + x` and `a[2] = a[2] + k` in a loop, under `symexAssume` on
`x`. The element fold met a width-stamped Int on one path and a bitvector
on the other: `iteSV: kind mismatch svBV64 vs svInt`. An initialised
`var a = [0, 0, 0]` faults the same way at the base, so this was not
introduced by the zero. Both sides are the same Nim integer, so `iteSV` now
merges them through `reconcileInt`, as every mixed operator does.

Two existing suites pinned the decline, and both now get Nim's answer. The
first Windows run of this slice caught them, so they are repinned here:
- `tsymex_r6_itesv_mergedegrade`'s two-sibling probes. Each declares
  `var arr: array[3, string]` and reads `arr[i]` before any guard on `i`.
  With the zero modelled, an out-of-range `i` is a genuine `IndexDefect`.
  The verdict moved from `sxUnknown` (the decline) to `sxRaised`, with
  witness `i = low(int)`. The suite's guard is that the string merge never
  yields a fabricated `sxSat`. That guard is now checked on the raise:
  never `sxSat`, and the witness index out of range. S8z re-pinned this
  same shape independently (same mechanism, same verdict), so the merge
  keeps S8z's re-pin — it adds a real-Nim replay of the raised witness —
  and S8aj's own addition is two new in-range twins
  (`symexAssume(i in 0..2)`), which stay `sxUnknown` through the merge's
  classified havoc; replay refutes their spurious candidates.
- `tsymex_r8_omitted_field_degrade`. `Bag(tag: x)` omits a `seq` field,
  and that field is now Nim's empty seq. So `b.tag == 5 and b.xs.len == 0`
  is a real `sxSat` (`x == 5`), where it was an `sxUnknown` decline. The
  `xs.len != 0` twin is `sxUnsat`. R8 warned against a "guessed zero" for a
  non-scalar field. This is not a guess: it is the zero compiled Nim gives.

*An unchecked sum that wraps decides.* The slice asked for `bv2int` links
for `+`, `-`, `*` and shifts, beside S8ad's negation link, once a failing
shape had been found. The search ran in two batches. Both used quotients,
remainders, sums, differences, products and shifts of `y + 1`, `2 * y`,
`y shl k` and `y shr k`, beside a scan.
- A first batch of 12 shapes ran on 5.1. Every one decided. Seven came back
  `sxRaised` because the probe left an overflow reachable, so the second
  batch bounds its operands.
- A second batch of 24 shapes ran on both versions, 18 of them checked and
  6 unchecked. All but one decided. On 5.1 the dearest took 6.6M steps
  (`(start + y) div (y + 1) > start`). On 4.13.4 the dearest took 19.0M
  (unchecked `start mod (y + 1) <= -(y + 1)`).

One did not decide: `start >= 0 and y > 1 and start + (y + 1) == start`
under unchecked arithmetic beside a scan. It is UNSAT, and it was
`sxUnknown` (`beSolverUndef`) at 40.6M steps on 5.1 and 40.9M on 4.13.4.

The links are not what it lacks. The query was dumped and replayed offline
on 4.13.4. With the `bv2int(y + 1) == wrap(bv2int(y) + 1)` link, with sign
links for `y` and `y + 1`, and with all of those together, it was still
unknown at 20M. Rewritten with a plain Int for `bv2int(y + 1)` it was UNSAT
in 917 steps, so the hard part is the wrap, not the bitvector.

`wrapIntToWidth` wraps an Int sum as `lo + (r - lo) mod 2^W`. A sum of two
in-range operands that overflows puts `r - lo` in `[2^W, 2^(W+1))`. That is
one window past S8ad's `|a| < |b|` pair. An underflow lands inside the
pair's `negSmall` arm, which is why the difference twin already decided. So
`divRangeFacts` now states that next window as well:
- `b >= 1` and `b <= a <= 2b - 1`: `e == 1`, `r == a - b`.
- `b <= -1` and `-b <= a <= -2b - 1`: `e == -1`, `r == a + b`.

Offline, either of those facts alone made the dumped query UNSAT in 0.45M
steps.

The `bv2int` links were built and measured before this was found, then
removed. They decided nothing, and they made other queries dearer. On 5.1,
`(start + y) div (y + 1) > start` went from 6.6M to 31.6M. On 4.13.4,
unchecked `start mod (y + 1) <= -(y + 1)` went from 19.0M to 29.8M.

The same no-unused-facts rule applies to the window. Each fact is a
theorem of the Euclidean pair. The pin checks both against Z3's own `div`
and `mod`, first on S8ad's numeral grid (now 23 facts per pair), then at the
wrap's own divisor, `+-2^64`, on both sides of every window edge. A
deliberately broken variant, with the window one too wide (`a <= 2b`), is
rejected at exactly `a == 2b` for each `b` in 1..6.

Steps for the whole walk (`rlimitDelta`), unchecked (`isExact`,
`{acDivByZero, acRange}`), with a scan:

| Shape | Base (5.1) | S8aj (5.1) | Base (4.13.4) | S8aj (4.13.4) |
|---|---|---|---|---|
| `start >= 0 and y > 1 and start + (y + 1) == start` (UNSAT) | 40.6M, `sxUnknown` | 0.61M | 40.9M, `sxUnknown` | 1.19M |
| `... start - (y + 1) == start` (UNSAT) | 0.88M | 0.78M | 1.31M | 1.60M |
| `... start + (y + 1) < start` (SAT, witness overflows) | 6.1K | 111K | 6.3K | 246K |

The SAT neighbour still decides in well under 1M steps. It is dearer
because the window facts sit beside its model search.

*Termination cost against the base.* Each suite was run whole at 94b8303 and
at the slice, on both Z3 versions, with every query's `rlimitDelta` summed.
Most were identical to the step, with the same number of queries and
unknowns: `r4_strip`, `q1_scanlift`, `r6_b5_chained`,
`r6_n36_raise_degrade`, `s8ae_remainder`, `s8v_termination` and
`163rev_intoffset_range`. Their queries hold no Int `div` or `mod`, so the
facts add nothing to them. `s8ad_remainder`, whose queries do, went from
6.08M to 6.35M on 5.1 (+4.3%) and from 7.04M to 7.13M on 4.13.4 (+1.2%). It
kept the same 125 queries and no unknowns. No query changed its answer.

*symex-mingw has 8 corpus shards, and each one checks its own headroom.*
At 3 shards, the slowest shard's run step took 44-60 min against the corpus
job's 60-minute limit. Three runs (36807797996, 36808365118, 36785819850)
reached 56.8, 59.4 and 56.6 min. A shard that the limit cancels reports
nothing for the suites it has not reached yet, so a failure there is
hidden.

A suite's cost is its compile plus its run, and the compile dominates: run
36808365118 spent 157.8 min in all on 394 suites. So the round-robin's
shards stay even. Replayed on that run's per-suite times, 8 shards come to
18.0-20.9 min each.

`derive-ci-suites.ps1` now owns the count (`$shardCount`). It emits the
matrix as `shard_ids`, so the workflow no longer repeats it by hand, and it
throws on an empty shard.

The corpus job's `Run shard` step times every suite. It prints the 10
slowest, and writes them to the job summary whether the shard is green or
red. It fails loudly in two cases:
- **SHARD OVER BUDGET**: past 40 min, even when every suite passed.
- **NOT RUN**: past 48 min it stops starting suites, which leaves time for
  the examples step and the log upload, and names the suites it skipped.

Either message says to raise `$shardCount`. Each of the step's three exits
(green, over budget, not run) was exercised locally in the pwsh container
with mock suites.

At the channel tip before this slice (59bf62e, still 3 shards, run
36817942850), the limit cancelled shard 0 at 60 min. Shards 1 and 2 took
44.7 and 58.2 min. With 8 shards, the first real run (36821741052) took
11.8-22.2 min per shard: 20.7, 22.2, 16.1, 17.5, 21.1, 21.9, 21.4 and 11.8
min for shards 0-7. Every shard ran every suite, and each one printed its
timing summary.

The landed sha (0cd890e, run 36824933867) took 13.2-22.4 min per shard:
21.1, 21.0, 15.8, 22.4, 20.8, 22.4, 20.9 and 13.2 min. That leaves at
least 17 min below the 40-minute budget and 37 below the limit. On all
three Windows legs (symex-mingw 36824933867, fuzzer-mingw 36824933826,
fuzzer-msvc 36824933818), the one failure was the known
`tsymex_rfc0005_s8ab_letaudit` guard-keying defect, which S8ak is fixing.
It fails on the tip too.

The reshard went onto the channel ahead of the rest of the slice, as
e3cd0c7, because every slice was losing shards to the limit. Its own run
(36833623417, green, S8ak's letaudit fix included) took 18.2-22.6 min per
shard: 21.1, 22.1, 22.3, 22.6, 20.2, 18.2, 20.3 and 20.6 min for shards
0-7. No shard came near the 40-minute budget, so the count stays at 8.

Pins: `tests/tsymex_rfc0005_s8aj_remainder.nim`, with a `.nim.cfg` that sets
`-d:symexQueryStats`.
- (1) The array cases: an element write then a symbolic read (S8ad's
  exhibit), untouched elements read as zero, reads at symbolic indices, and
  writes in a loop, on one branch, and in a short-circuit operand.
- (1) The nested aggregates: an array of objects, an object holding an array
  (and an array of objects), a seq field, a local seq, an array of a
  distinct type, an array of arrays, and a variant object.
- (1) For each of those, the target is SAT with its witness checked, the
  dead twin is `sxUnsat`, and there is no `weInternalWalkerFault`. RED at
  the base: every one is `sxUnknown` with `weInternalWalkerFault`.
- (2) The table above. Each UNSAT shape is decided within 3M steps with no
  `beSolverUndef`, and the SAT witness is checked to overflow. RED at the
  base: `start + (y + 1) == start` is `sxUnknown` at 40.57M.
- (2) The facts hold at `+-2^64`, and the check rejects the broken window.
- The `>= 179` floor.

*Different mechanisms, reported and not fixed here.* (A symbolic-index
array write, `a[i] = 7`, was declined — `feUnsupportedStmtKind`,
"unsupported nnkAsgn shape" — at this slice's branch point; S8z modelled
it independently, landed first on the channel, and this slice rebases onto
that fix, so it is no longer true post-rebase and is dropped from this
list.)
- **`add` on a dotted seq field is declined.** `o.s.add v` is N49
  `feUnsupportedOp`. `s.add v` on a local seq and `o.s = @[v]` are both
  modelled (and pinned).
- **An uninterpreted type has no zero.** `zeroValueForType` still returns
  nil for `itUninterp`, and the caller declines as before.
**As landed (S8ao, walker 181) — S8aj's remainder.**

*`add` on a dotted seq field is modelled through the field path.*
`o.s.add v` was N49 `feUnsupportedOp` — the dotted-field lvalue receiver
never matches the bare-symbol `#145 mutations` arm (`recvName` there is a
genuine env-slot the rebind machinery can reassign; `obj.seqField` has no
such slot), so it fell to the blanket dotted-field decline. `.add` is not a
new mutation primitive: it is Nim/stdlib sugar for "read the field, append,
write the field back," and the field-WRITE half of that already has a
primitive for every lvalue shape `<fieldPath> = v` supports — S8p's
value-field rebuild (`valueFieldWrite`) for a value tuple/object step, the
R6 ref-object field-deref-write (`mkFieldDeref`/`mkFieldDerefWrite`) for a
`ref`/`ptr` step. Two new procs, `dottedSeqAddShape` (pure eligibility,
mirroring `valueFieldTy`'s own "parses nothing" contract) and
`dottedFieldAdd` (the lowering), sit beside `valueFieldWrite` in
`dsl_parser.nim` and do exactly that: read the field (which, for a value
step, also forks any variant-arm discriminant check for free — the same
reason `valueFieldChecked` exists for plain assignment), `mkSeqAdd` the new
element on, and write the result back through the SAME primitive assignment
uses. The N49 dispatch site now gates `calleeName == "add"` and
`classifyType(fieldNode).ty.kind == itSeq` and `dottedSeqAddShape(fieldNode)`
before routing there; everything else (`del`/`insert`/`incl`/`excl`/`[]=` on
a dotted field, and `add` on a dotted STRING field) keeps the original
blanket decline unchanged — this slice named `add` on a seq field only.

A base `o.s.add v` and a nested `a.b.s.add v` both take the value-field arm
(the recursion is `valueFieldWrite`'s own, one level per step, unchanged by
this slice). RED at the base: both were N49 `feUnsupportedOp`. GREEN: both
are `sxSat` with the appended value in the witness, and the untouched-field
twin is `sxUnsat`; two `.add` calls in sequence read the freshly-rebuilt
field (not the proc-entry value), proving the rebuild is live, not cached.
`del`/`insert`/… on a dotted field, and `add` on a dotted string field, are
pinned unchanged (still N49).

*A ref/ptr object's field add reuses the real primitive — and inherits its
real gap.* `p.s.add v` for a `ref object` field now routes through
`mkFieldDeref`/`mkFieldDerefWrite`, the SAME primitive `p.s = v` already
uses. Probing surfaced that a ref-object field of a COMPOUND sort (`seq`)
has no field-split heap representation yet at all — `p.s = @[...]` alone,
with NO `.add` involved, already raises `seUnsupportedCompoundSortLeaf`
("no single-leaf Z3 sort representation") from the heap-sort derivation
itself, independent of this slice (the engine's own message names it R3+
territory: "composite pointees — ref object / seq[ref T] — land R3+").
Before S8ao, `p.s.add v` hit N49's narrower, EARLIER `feUnsupportedOp`
first, which happened to hide this deeper, pre-existing gap. This slice's
own pin proves the routing is real without claiming to have closed that
gap: `p.s.add v` now fails the SAME way `p.s = @[...]` already does (shares
the real primitive, not a parallel one), rather than being blocked by its
own N49-specific catch-all.

*`zeroValueForType` keeps declining for `itUninterp` — proven, not widened.*
`classifyType` (`dsl_typebridge.nim`) builds `itUninterp` for exactly three
placeholder prefixes, and none has a zero `zeroValueForType` can fabricate
soundly:
- `__ownership:*` (`owned T` / `Atomic[T]`, ADR-0010 Breadth-LOW-L4):
  deliberately out of scope for the ref cluster — no Z3 sort was ever
  allocated for these, so there is no sort to build a zero constant of.
- `__closure` (a proc-typed local with no initializer, e.g.
  `var f: proc(x: int): int`): Nim's real zero is a nil closure, but
  `svClosure` carries a SITE KEY into real lambda-body IR
  (`runtime_closures.nim`) — there is no "nil closure" sentinel today that a
  later `f(...)` call could degrade through soundly; minting one is a new
  `SymVal` shape (plus every call/compare site that would need to recognise
  it), out of proportion for one caller's zero-init.
- `__unsupported:<X>` (`classifyType`'s catch-all for a type name no
  structural arm recognises): `X` names some real Nim type the classifier
  never identified, so its actual shape — and therefore its actual zero —
  is unknown at this call site. Fabricating a zero for an unidentified shape
  is exactly the "launder a gap into a sound-looking value" move §3.1 rules
  out.
`allocateSym`'s own `itUninterp` arm already classifies these three
precisely the instant a value of one is ALLOCATED
(`heUnsupportedOwnership`/`feUnsupportedParamType`/`ceUnsupportedHof`).
`zeroValueForType` declining first, at the uninitialized-`var` statement
(its one caller whose decline is directly observable — every other caller
already SND-1-taints before its dummy is ever read, per S8aj's own audit),
is a classified halt one step earlier for the same reason, never a crash,
never a guess. Pinned for all three prefixes, reached through an
uninitialized local var of each shape: `sxUnknown`, `feUnsupportedStmtKind`,
"zero-init not modeled this cycle," never `weInternalWalkerFault`.

Pins: `tests/tsymex_rfc0005_s8ao_remainder.nim`.
- (1) A base and a nested dotted seq-field `.add`: `sxSat` with the appended
  value witnessed, the untouched-field twin `sxUnsat`, no
  `weInternalWalkerFault`. Two sequential `.add`s read the live field.
  `del`/`insert`/… and a dotted STRING field's `add` are unchanged (N49).
  A ref object's seq field: `.add` no longer hits N49 specifically (shares
  fate with plain assignment's own pre-existing `seUnsupportedCompoundSortLeaf`).
- (2) All three `itUninterp` prefixes, reached via an uninitialized local:
  `sxUnknown`/`feUnsupportedStmtKind`, never `weInternalWalkerFault`.
- The `>= 181` floor.

*Different mechanisms, reported and not fixed here.*
- **A ref-object field of a compound sort (`seq`) has no field-split heap
  representation.** `p.s = @[...]` alone (no `.add`) already raises
  `seUnsupportedCompoundSortLeaf` — pre-existing, independent of this
  slice, and explicitly out of scope per the engine's own message (R3+
  territory, composite pointees). `.add` through such a field now shares
  that fate instead of being blocked earlier by its own N49 catch-all, but
  building real compound-sort field-split heap storage is not done here.
- **`del`/`insert`/`incl`/`excl`/`[]=` on a dotted field are still N49
  `feUnsupportedOp`.** This slice named `add` only; a genuine value-typed
  field-write rebind for the others is the same "out of proportion for
  this fix" argument N49's original comment made for the whole group.
- **`add` on a dotted STRING field is still N49 `feUnsupportedOp`.** The
  scope was the seq case; a dotted string field's `.add` would need the
  SAME field-path routing applied to `iekStrConcat` instead of
  `mkSeqAdd`, not attempted here.
- **`itUninterp`'s three placeholder prefixes stay undifferentiated at the
  uninitialized-`var` decline site.** `zeroValueForType`'s `nil` return
  collapses all three into one generic `feUnsupportedStmtKind` "unmodeled
  type itUninterp" message at that ONE call site, where `allocateSym`'s own
  `itUninterp` arm already gives each prefix its own precise kind
  (`heUnsupportedOwnership`/`feUnsupportedParamType`/`ceUnsupportedHof`).
  Sharpening the uninitialized-`var` site's diagnostic to match was not
  requested and is not done here — it is a diagnostics-precision
  improvement, not a verdict change.

**As landed (S8am, walker 183) — S8z's remainder.** The six mechanisms
S8z's own "Different mechanisms, reported and not fixed here" footer
listed above (items 1–6 there) closed, plus one witness-extraction
characteristic found on the way and reported, not fixed (out of scope).

1. **Seq element `op=`.** `s[i] += x` and every other augmented assignment
   on a `seq` element is modelled, mirroring the array path S8z already
   fixed: the parser's `nnkInfix` augmented-assign handler gained an
   `itSeq` branch beside its existing array one. Was
   `feUnsupportedStmtKind`.
2. **Seq element write order.** Nim's own evaluation order for
   `s[i] = f()` was empirically determined with a compiled probe (Nim
   2.2.10, debug build; an index expression with a visible side effect
   beside an RHS call that also has one): the index is evaluated and
   bounds-checked **before** the RHS. The walker's seq-assignment path
   previously evaluated the RHS first (the array path, fixed earlier,
   already had this right); `parseAsgn`'s `itSeq` branch now forces a
   discarded bounds-check read before parsing the RHS, matching
   `valueFieldWrite`'s existing array/tuple/object idiom. `s[9] = raiser()`
   now raises `IndexDefect`, never the value's own exception, confirmed by
   an oracle test that calls the real Nim code and asserts the side-effect
   log stays empty.
3. **`char` witness rendering.** A `char` scalar or `seq[char]` witness
   renders as Nim's own `char`, not `uint8`. `IRType` gained a
   provenance-only `isChar` field (parallel to the existing `enumName`
   idiom: it affects rendering and `canonicalize()`'s cache key, not
   structural `==`), set by `classifyType`'s `"char"` arm. `emitTyAndReader`
   picks a new `readChar` runtime reader (`char(w.uintVals[name])`,
   reusing the same 64-bit cell `char` / `byte` / `uint8` already shared) when
   `isChar` is set. This is a render-only change: the underlying solve was
   already sound, so it bumps `renderAsChoicesVersion` (11 → 12), not
   `symexWalkerVersion`.
4. **`low(a)` / `high(a)` on an array value.** Both fold to the array
   type's own `lo` / `lo + size - 1` at parse time, mirroring the existing
   `isStringLow` / `isStringHigh` carve-out. Was `feUnsupportedExprKind`.
5. **Array witness index type.** An `array[1..3, int]` witness now renders
   as `array[1..3, int]`, not `array[0..2, int]`: `IRType` gained a
   provenance-only `lo` field (`itArray`, same idiom as `isChar` above),
   threaded from `classifyArrayBracket` through `canonicalize` to
   `emitTyAndReader`'s `itArray` arm, which builds `array[lo..hi, T]` via
   an `infix` node when `lo != 0`. Render-only (the values were already
   positional and exact); bumps `renderAsChoicesVersion` only.
6. **Container shapes, closed further.**
   - **`array[bool, T]`.** A `bool`-indexed array reads and writes at a
     symbolic index: `arrayIndexBounds` gained an `itBool` case
     (`lo = 0, hi = 1`), and a new `coerceArrayBoolIndex` helper
     (`ite(idx.bo, 1, 0)`) is applied at the two walker call sites that
     read an array index — not inside the shared `arrayIndexConds` /
     `arraySelect` / `arrayStore` helpers, which the seq-index path also
     uses, where a bool index can never arrive. Was declined as an
     unsupported type.
   - **`char` / `byte` / `uint8` container witness parameters.** With
     `isChar` giving the renderer the provenance it was missing (item 3),
     the `isCharAmbiguous` exclusion in `isRenderableTableTy` /
     `isRenderableSetElemTy` is no longer needed and is removed: a
     `Table[string, char]` value or `HashSet[char]` / `HashSet[byte]`
     element is now a reachable witness parameter, using the same
     `readTableStrIntAs[T]` / `readSetIntAs[T]` readers unmodified. Was
     `feUnsupportedWitnessType` ("unsupported witness shape ... the
     supported fragment is {...}") at the parser's parameter-level gate —
     distinct from `seUnsupportedTableKeyType` /
     `seUnsupportedTableValType` / `seUnsupportedSetCharInterop`, the
     allocation-time kinds that apply only to a Table/HashSet
     constructed *inside* the SUT (pinned independently by
     `tsymex_r6_n39` / `n40` / `n43`).
   - **Non-`string` Table keys and non-integer values / elements.**
     Confirmed, by code reading and by three new pin tests, still
     correctly declined (no sound 64-bit cell model exists for them) —
     see "Different mechanisms" below.

Found on the way:

- **A raise-irrelevant parameter's witness is not a reliable bound.** For
  `s[i] = raiser()`, finding the path that reaches `raiser`'s own
  `ValueError` reports a sentinel-looking value for `i` (`low(int64)`)
  rather than a value respecting the already-accumulated `0 <= i < s.len`
  path condition, even though `i` plays no role in `ValueError`'s own
  raise condition. Reproduced identically against the pre-existing,
  already-S8z-fixed array write path (`a[i] = raiser()`), so this is a
  general witness-extraction characteristic of the engine — a don't-care
  symbol's reported value need not respect an accumulated-but-irrelevant
  path constraint — not an S8am regression. The `tRaisedExn("IndexDefect")`
  direction, where `i` *is* part of the raise condition, correctly reports
  `i` outside the valid range.
- **Four pre-existing suites assumed the old `char`-as-`uint8` rendering**
  and one assumed the old `HashSet[char]`-parameter decline:
  `tsymex_rfc0005_s8z_remainder.nim` (`setCharLocal`'s witness comparison,
  and `setCharParam`'s own "scoped decline" test, repinned to the new
  `sxSat`), `tsymex_phase15_S11_mutation.nim`, `tsymex_phase15_z3c_classify.nim`
  (comment-only) and `tsymex_rfc0005_s8p_precision.nim`. All four are
  updated here to assert `char`, not `uint8(ord(...))`.
- **Consumer-visible (for S11's migration note).**
  - **`sxUnknown` programs that now get verdicts:** items 1, 2, 4, 6a and
    6b above (verdict-affecting; `symexWalkerVersion` 182 → 183).
  - **Witness type changes with no verdict change:** items 3 and 5
    (`renderAsChoicesVersion` 11 → 12).
  - **Cache.** Both version bumps invalidate every symex cache entry that
    touches a `char`, a non-zero-based array, a seq `op=`/assignment, a
    `bool`-indexed array, or a `char`/`byte`/`uint8` Table value or
    HashSet element.
- **Different mechanisms, reported and not fixed here.**
  - **Non-`string` Table keys.** Still `seUnsupportedTableKeyType`
    (allocation-time) or `feUnsupportedWitnessType` (parameter-level): the
    model and the S8f registry/extractor are keyed by string.
  - **Non-integer Table values or HashSet elements** (`string`, `float`,
    tuple, object, `seq`, ...). Still `seUnsupportedTableValType` /
    `seUnsupportedSetCharInterop` (allocation-time) or
    `feUnsupportedWitnessType` (parameter-level): every such shape would
    need a different cell sort than the 64-bit integer one the container
    model has.
  - **The raise-irrelevant-parameter witness sentinel**, above: a true
    engine characteristic, not scoped to this slice's mechanisms, and
    outside what S8am was asked to fix.

**As landed (S8an, walker 183) — S8ac's remainder.**

*A routine declared inside the code under test is walked.* A statement-
position `proc`/`func` (and `iterator`, `converter`, `template`, `macro`)
declaration was `feUnsupportedStmtKind`, which tainted every path past it.
A declaration has no run-time effect, so it is now an empty statement
(`parseStmtInner`); what is walked is each use. A CALL reaches the body
through `ensureProcRegistered`, as any callee. Its captures are the
enclosing variables and parameters the body names without declaring them,
transitively through the nested routines it names (`b` calling `a`, which
writes `c`, reaches `c`); they are computed by symbol identity
(`nestedCaptureSyms`) and stored as IR names on `ProcSig.captures`. The
callee's own locals and parameters keep clear of those names
(`reserveScopedNames`, before `claimRoutine`), so the walker copies each
capture into the callee's env at the call and back into the caller's on
every exit, a raise included (`threadOuterBindings`/`carryOuterBindings`):
Nim captures by reference, and a direct call reads and writes the
enclosing variable as it stands. Used as a VALUE (`let f = addk`), a nested
routine is a closure over its captures (`parseProcAsValue` no longer forces
a unit env for it); a lambda that names a nested routine inherits that
routine's captures (`collectFreeVarRefs`), so a write through it is the
by-reference capture write the closure machinery already declines
(`ceCaptureByRefUnmodelled`) -- before, the write landed in the closure's
own env and was dropped (`sxUnsat`, `errors` empty).

A nested routine is keyed by its declaration (`nestedSiteKey`: body hash
and position), and an overload by its symbol. A non-generic callee was
keyed by its bare name, so two nested `h` (one in `a1`, one in `b1`) and two
top-level overloads `ov(int)`/`ov(string)` each shared one registration and
every call ran the first body: `nc`/`ov` `sxUnsat`, `nc_dead` `sxSat`,
`errors` empty. `ensureProcRegistered` now records the symbol each bare key
was registered for (`ParseCtx.keySyms`); a different symbol of the same
spelling gets `name#<bodyHash>#ovl`. A program without overloads is keyed
exactly as before.

Recursion is bounded by `maxCallDepth`. The explore-mode walk forks an
`if` without a feasibility check, so `fact(1)`'s `k > 1` arm reached the
next level and the depth bail even when the argument decided the depth:
every recursive target was `beBudgetExhaustedUnmodelled`. A path that
reaches the bail is now dropped when its query is UNSAT (`pathInfeasible`,
bounded like `loopArmInfeasible`; an undecided query keeps the path), so a
recursion whose depth the arguments decide is walked exactly within the
budget. On a symbolic argument the deepest feasible path still bails and
declines, scoped, with the budget named; with room it decides.

*`addr lv` passed as a `ptr T` is a heap cell for the call.* An `addr`
actual was `feUnsupportedExprKind` (`nnkAddr`), and `let p = addr x` was
`heUnsafeCast`. `userCallStmt` now stores `lv` into a fresh `ptr` cell
(`mkNewT` + `mkDerefWrite`), passes the cell, and reads it back into `lv`
in the call's `finally`, so the write lands on every exit as Nim's does.
Every `addr` of one lvalue in one call (`scopedRepr`) is ONE cell:
`two(addr x, addr x, 8)` leaves `x == 3` and `same(addr x, addr x)` is true,
`same(addr x, addr y)` false -- aliasing is exact, not declined. The
cell's store and read-back are marked `dwCell`/`dCell` and do not count
against `heapDepth` (a per-path count of heap operations, 8 by default:
two `incP(addr x)` calls exhausted it on the synthetic copies alone). The
model needs two facts, each checked, each a scoped decline when it fails:
- the pointer cannot outlive the call (`ptrFormalStaysLocal`): every use of
  the formal is `p[]` not under `addr`, a comparison, or an argument to a
  `ptr` formal that itself stays local (recursively). Otherwise
  `heUnsafeCast`, "may let the pointer escape";
- the callee cannot reach `lv` another way (`addrActualMayAlias`; a `var`
  actual on the same root, `mixP(addr x, x)`, is `feUnsupportedOp`), and
  every variable `lv` names is a guard root (below).
`let p = addr x` (or `var`) whose every later use in its statement list is
`p[]` or such an argument IS `x`: the rest of the list is parsed with `p[]`
spelled `x` and `p` spelled `addr x` (`addrAliasDecl`/`substAddrAlias`);
`x` must name one location for `p`'s whole life (a variable, or a field
chain of value objects over one). `p[] += v` on an unranged int or float
pointee is modelled (`p[] = p[] + v`).

*Module-level globals are threaded through every walked call.* A global
was a bare name in the caller's env and absent from the callee's: the
callee's write was dropped (`g` `sxUnsat`, `g_dead` `sxSat`), its read was
`feGlobalReadUnmodelled`, and `setAlG(gCount, 8)` (whose callee also writes
`gCount = 5` directly) was written back over the direct write (`ga_dead`
`sxSat`), all with `errors` empty. A module-level `var`/`let` is now named
`__gl:<module>.<x>` (`scoped_names.strVal`, so every site agrees), copied
into each callee's env and carried back out on every exit, and a call that
reaches a global or a capture is never cached (the cache replays only
`pcDelta`). A global read before any write in the walk is still
`feGlobalReadUnmodelled`: its value is whatever the program left there. A
`var`/`addr` actual names its variables as `IRStmt.cGuardRoots`; one that
is a global or a capture of the callee is WITHHELD from the callee's env
(the copy-in/copy-out argument is its only route), a direct read of it
anywhere under the call declines (`callGuardedNames`, `feUnsupportedOp`),
and a direct write is caught on exit (`touchedGuard`) and declines. A
closure body that writes a global declines (`ceCaptureByRefUnmodelled`,
naming it), as one that writes a capture already did.

The same audit found the copy-in/copy-out write-back unsound on its own
lvalue. `varActualMayAlias` checked only the lvalue's root:
`setIJ(s[i], i)` (whose callee writes `j = 1` then `x = 7`) writes `s[0]` in
Nim, and the write-back after the call wrote `s[1]`; `setIJ(i, i)` leaves
`i == 7` in Nim, and two by-name write-backs left 1 (both directions,
`errors` empty). Every variable an lvalue names now counts
(`lvalueVarSyms`), and a plain-variable `var` actual is checked too; both
shapes decline, scoped, `feUnsupportedOp`.

An unbound non-global name now reads "is read where the symbolic walker
has not bound it" instead of calling itself a module-level global (same
kind, `feGlobalReadUnmodelled`).

Routine-kind tests go through the Cluster N vocabulary, as
`tsymex_phase15_N2_kindgate_audit` requires: a nested routine is
recognised by its impl's node kind (`routineShapedForClosureDetect`, via
`namesRoutineDef`), not by a symbol-kind gate, and the statement arm and
the pointer-use scan name `routineShapedForClosureDetect` /
`RoutineNodes` rather than inline lists. `tsymex_rfc0005_s8_scope`'s
`isUnsafeCast` exhibit was `let p = addr y` read through `p[]`, which this
slice models; it is now `cast[ptr int](addr y)`, with the same contract
(one parse record, `heUnsafeCast`, site-anchored, reached twice under its
marker).

Pins: `tests/tsymex_rfc0005_s8an_remainder.nim`, every expectation probed
against Nim 2.2.10.
- (1) A nested proc and func with no captures; captures of a parameter and
  of a local, read as they stand at the call; written (`c += x` twice),
  through a chain (`b` -> `a` -> `c`), shadowed inside the callee, and
  written before a raise the caller catches; a nested routine as a closure
  value (read as it stands at the call; a write declines, scoped); a `var`
  actual that is also a capture declines (`feUnsupportedOp`); a lambda
  writing a capture through a nested routine declines; a nested template
  and iterator; same-named nested routines and top-level overloads;
  recursion within the budget (concrete argument, and a capturing
  recursion) and past it (declines with `maxCallDepth=3`, decides with 8).
- (2) `setP`/`getP`/`incP`/`fwdP` through `addr x`; one cell for
  `two(addr x, addr x)`, two for `addr x, addr y`, `same` both ways;
  `let p = addr x`; `addr o.a`; a raising callee; an escaping callee
  (`heUnsafeCast`); `mixP(addr x, x)` (`feUnsupportedOp`).
- (3) A callee's write and read of a global, nested and across a raise; the
  call cache across a write; a global first read in a callee declines; a
  `var`/`addr` actual that is a global the callee writes or reads declines;
  one that is a local while the callee writes a global is modelled; a
  closure value or lambda writing a global declines; a lambda reading a
  global reads it as it stands; `setIJ(s[i], i)` and `setIJ(i, i)` decline.
- The `>= 183` floor.

*Different mechanisms, reported and not fixed here.*
- **The explore-mode walk forks an `if` without a feasibility check.**
  S8an drops an infeasible path only at the call-depth bail; elsewhere an
  infeasible arm is still walked to its end (a precision and cost matter,
  not a verdict one: its query is UNSAT at every target). Recursion on a
  symbolic argument therefore still reaches `maxCallDepth` on its deepest
  feasible path and declines, scoped.
- **An opaque or foreign call does not havoc globals.** A
  `{.symexOpaque.}`/`importc` call that writes module state leaves the
  walk's binding of every global unchanged across it -- true before S8an
  for globals the entry proc itself wrote, and now for globals threaded
  through callees too. Modelling it needs an effect summary (which globals
  a foreign routine may write) the engine does not have.
- **A global read before any write in the walk stays a decline.** Its
  value at entry is the program's state at the time of the call, which the
  walk does not know; making globals free inputs (or `default(T)` at
  program start) is a separate modelling choice.
- **A closure value's write to a capture or a global still declines**
  (`ceCaptureByRefUnmodelled`), as does a closure called outside the frame
  that built it reading a by-reference capture. Direct calls of a nested
  routine are exact; closure values keep S9's scoped declines.
- **A pointer that may escape, and `addr` outside a call argument or the
  `let p = addr x` form, still decline** (`heUnsafeCast` /
  `feUnsupportedExprKind`): storing `addr x` in an object, returning it,
  comparing two `addr` expressions directly, or pointer arithmetic. The
  slice title's "`var ptr` parameter passed `addr x`" cannot occur (Nim
  rejects an `addr` rvalue for a `var` formal); the modelled shape is a
  `ptr T` formal.
- **Two `addr` of different parts of one root in one call decline**
  (`two(addr o.a, addr o.b)`), conservatively: the alias check is by root
  variable, not by disjoint path.
- **An `int` heap cell costs Z3 tens of seconds on wide-range arithmetic.**
  The `int` heap is `(Array Ref (_ BitVec 64))`, and an Int-sorted local
  stored into it and read back goes through `int_to_bv`/`ubv_to_int`. With
  `v` in `(-1000, 1000)`, the UNSAT query for "two `incP(addr x)` leave `x
  != v + 2`" took 6.5M rlimit steps (37-41 s on Linux, past the Windows
  corpus watchdog's 240 s for the suite). A plain `let r = new int; r[] =
  v; r[] += 1` with the same range takes 58 s, so this predates S8an; with
  `v` in `[0, 16)` it takes 0.56 s. The pins use the narrow range. An
  Int-sorted heap for unranged `int` pointees (or a bridging lemma) is the
  fix, in the heap model.

**As landed (S8ap, walker 183) — S8ao's remainder.**

*Compound-sort fields of a ref object are leaf-split heap cells.* A field
(or a bare pointee, `ref seq[int]`) whose type is a backed seq, a
`Table[string, V]` or a backed `HashSet` was `seUnsupportedCompoundSortLeaf`
plus `heUnsupportedPointeeRead` on every access, and
`heNewFieldZeroUnsupported` on every constructor: the logical heap is one Z3
array per key, `Z3Array[Ref_T, V]`, and a compound value has no single term
`V` (a seq is a data array and a length, a table a data array, a presence
array and a size, a set a membership array and a size). S8ap keeps one heap
array per LEAF instead. The leaf heaps of a cell share the cell's key: leaf 0
keeps the key itself (so `heapKeyShapes[key]` still records the whole value
type, which the witness reads), the others add `__@len`/`__@present`
(`heapLeafSuffixes`). `@` cannot start a Nim identifier, so no field key
collides with a leaf key, and `renderCell`'s field scan already skips any
suffix holding `__`. Every array is indexed by the object's `Ref_T` address,
so a read is a ground `select` per leaf, and a write is a `store` per leaf.
The procs (`runtime_heap.nim`) are `heapCellArrays` (the current or input
array of each leaf), `heapCellSelect`, `heapCellStore` and `heapCellIte`. A
scalar cell is the one-leaf case and behaves exactly as before. Every
`walkHeapArm` site that read or wrote a field heap goes through them: the
main deref read and write, the variant arm-field read and write, the
discriminator write's same-branch carry, and `new`/the constructor's
zero-write. A constructor zero-writes such a field with `defaultZero`.

- **Aliasing** is the scalar heap's own: two equal addresses select the same
  cell of every leaf, so a write through `p` is read through `q` when
  `p == q`, and only then.
- **Nil** is unchanged. The deref still forks `NilAccessDefect` before any
  leaf is touched.
- **Merges** need nothing new. Path joins, the return merge and
  `heapMetaExtends` work key by key, and each leaf is a key. A read that
  selects among several arms' cells (an arm field shared by several tags,
  the discriminator carry) uses `heapCellIte`, which builds one `ite` per
  leaf. `iteSV` would havoc a compound or string merge.
- **Well-formedness.** A free input cell must hold a value Nim can hold:
  - a length or size in `[0, 1024]`;
  - a string of bytes;
  - a table's or set's size tied to the keys present, via
    `ContainerCardRegistry`.

  `heapCellWfConds` asserts these of the INPUT cell
  `select(heap_<leaf>, p)` at every read of a compound or string cell.
  The input heap holds the program's inputs, so a fact about every input
  cell is a fact of the program for any address.
- **Strings.** A `string` field keeps its single heap, and was already
  writable. `liftHeapValue` now has an `itString` arm, so a read is the
  select itself instead of a havoc.
- **Witness.** `renderCellField`/`renderCell` render a string and a compound
  cell from the model's INPUT heap (`renderHeapCompound`). The leaves are
  written under the same names a by-value param of the type uses:
  - `strVals`;
  - `seqLens` plus `.<i>` elements;
  - `tabKeys`;
  - `setMembers`.

  A `seq[ref T]` element becomes the position `<cell>.<field>[<i>]`, added
  as a ref field is. `readCellField` reads them back through
  `readCellSeq`/`readCellTable`/`readCellSet`, plus a string arm.
  `refCellFidelity` counts such fields faithful: a string; a seq of
  int/bool/float/ref; a `Table[string, int|bool]`; a backed `HashSet`.
  A cell no path read is unconstrained in the model. A length outside
  `[0, 1024]` therefore renders empty, and a non-byte string renders `""`
  (`evalStrBytesOrEmpty`). Any well-formed value is a faithful rendering of a
  cell nothing observed.

*Dotted-field mutations take the field-write primitive.* S8ao's
`dottedSeqAddShape`/`dottedFieldAdd` are generalised to
`dottedFieldShape`/`dottedFieldMutate` (`dsl_parser.nim`):
- **Mutations covered:** `del` (seq or Table), `insert`, `incl`, `excl`,
  `[]=`, and `add` on a string field. A string or char argument becomes
  `iekStrConcat`; any other argument becomes the bare arm's
  `iekStrUnsupported`.
- **How each lowers:** read the field, apply the bare-symbol arm's own IR to
  the old value (`dottedOpExpr`), and write the field back through the same
  primitive `<fieldPath> = v` uses. That is the R6 field-deref-write for a
  ref/ptr step, or S8p's `valueFieldWrite` for a value step. So `del`'s
  `IndexDefect` fork and `insert`'s lowering decline are the bare
  variable's.
- **Element assignment** `o.s[i] = v` / `p.s[i] = v` was the "unsupported
  nnkAsgn shape" decline. It now reads the field into a fresh slot, runs
  N14's `isIndexAssign` there (its IndexDefect fork included), and writes
  the slot back (`dottedFieldIndexAssign`). A Table field takes
  `mkTableSet`, and a string field S11's `iekStrUnsupported`.

*An uninitialised `var` of an `itUninterp` placeholder declines with the
placeholder's own kind* (`uninterpVarDecline`). These are the kinds
`allocateSym` already uses for the same placeholder:

| Placeholder | Kind |
|---|---|
| `__ownership:*` | `heUnsupportedOwnership` |
| `__closure` | `ceUnsupportedHof` |
| `__unsupported:*` | `feUnsupportedParamType` |
| `__unsupported_witness:*` | `feUnsupportedWitnessType` |

Before, all of them were one generic `feUnsupportedStmtKind`.
`zeroValueForType` itself is unchanged: it still declines, for the reasons
S8ao proved.

Pins: `tests/tsymex_rfc0005_s8ap_remainder.nim`, 36 tests.
- (1) Heap cells. Each case pairs a reachable target with an unreachable
  twin, and witnesses replay through the SUT:
  - write-then-read;
  - an input seq read and rendered;
  - the witness is the input cell, not the end-of-path value;
  - aliasing and its no-alias twin;
  - nil read and nil write raise;
  - constructor and `new` zero-writes;
  - string, Table and HashSet fields, including size tied to content;
  - a float seq;
  - a `seq[CNode]` whose elements render as heap positions;
  - a path join;
  - a bare `ref seq[int]`.
- (2) Dotted mutations, value path and ref path:
  - `del`, and `del` out of bounds;
  - `[i] =`, and `[i] =` out of bounds;
  - Table `[]=`/`del`;
  - `incl`/`excl`;
  - dotted `insert` matching the bare `insert`'s status and kinds.
- (3) Dotted string `add`: a char argument and a string argument, value
  path and ref path.
- (4) All three `itUninterp` prefixes with their own kinds.
- The `>= 183` floor.

Moved forward because the old pins exercised exactly the gaps S8ap closes.
For the ones that pinned a still-unmodelled site, the poison source was
swapped for a field kind that still reaches the same site:
- `s8ao_remainder`: dotted `del` and dotted string `add` are now `sxSat`;
  `p.s.add v` is `sxSat`; the itUninterp kinds are as above.
- `r6_n49_dottedfield_mutation`: `del` is `sxSat`; `insert` stays
  `sxUnknown` through the bare decline.
- `s0_exhibit`, `s3_monotonicity` F1 and `r6_heap_raise_totality`: string
  field replaced by a `distinct int` field.
- `s4_alloc`: string field replaced by a `distinct string` field; its IR
  case uses `tDistinct`.
- `r6_lows_declines` N41-2/3: Table field replaced by a tuple field.
- `s6b_ops`: seq field replaced by a `distinct int` field (still
  `heNewFieldZeroUnsupported`).
- `rfc0005_s2_replay`: the lossy-witness fixture's string field replaced
  by a `distinct int` field (a string field now renders faithfully).
- `r6_n27_placeholder_read_audit`: runtime.nim's marker count goes from 81
  to 85. `renderHeapCompound`'s svSeq arm adds the placeholder guard and
  three reads behind it.

Caught on symex-mingw, not locally: `readCellSet` converted every member
with `E(v)`, which does not compile for a `HashSet[string]` field
(`r6_n43_parity`). Members are integers, and only an integer-like element
is backed (`isBackedSetElemTy`). Any other element type keeps the empty
set, and its pointee classifies as lossy. `readCellTable` is guarded the
same way.

*Different mechanisms, reported and not fixed here.*
- **`insert` is unmodelled even on a bare seq.** Lowering declines
  `iekSeqInsert` (`feUnsupportedOp`, "#143 follow-up"). A dotted `insert`
  now takes the same IR and so the same decline. Making it modelled is an
  `insert` lowering, not a field-path change.
- **A `seq[string]`'s element operations fault the walker on a bare local
  too.** `var s: seq[string]; s.add v; s[0] == "q"` reports
  `weInternalWalkerFault`: the `a.kind == b.kind` assertion at
  `runtime.nim` and "iekSeqAdd: unsupported elem string". A `seq[string]`
  field holds a well-formed cell, but the same operations fault through it.
  This is the seq-of-string element model, independent of the heap.
- **A field of a value field of a ref (`p.inner.s`) is outside
  `dottedFieldShape`.** It accepts one ref/ptr step directly before the
  field, or a value chain from a local or param. `p.inner.s.add v` stays
  N49. Reading `p.inner` itself is a tuple-valued heap cell, which is
  still `seUnsupportedCompoundSortLeaf`.
- **Some field kinds still have no heap leaf representation**
  (`seUnsupportedCompoundSortLeaf` + `heUnsupportedPointeeRead`):
  - by-value object, tuple and array fields;
  - `Table` with a non-string key;
  - `Table[string, V]` whose `V` is not backed.

  A `distinct` field is still havocked (`heUnsupportedPointeeRead`). None of
  these, nor a seq field with an unbacked element type, get a
  construction-time zero (`heNewFieldZeroUnsupported`). They are the
  remaining shapes of the same storage problem, but each needs its own leaf
  layout (a tuple's fields, an array's elements).
- **An unrenderable container inside a ref pointee demotes the whole
  param.** Examples are `seq[bool]` and `seq[string]` fields, or a
  `Table[int, int]`; the check is `isRenderableWitnessTy` /
  `demoteUnrenderableWitnessTy`. The param demotes to
  `__unsupported_witness:*` (`feUnsupportedWitnessType`) before the walk,
  so such a field is reachable through a locally constructed object but
  never through an input ref.
- **A seq field of the object's own ref type crashes compilation.** A field
  like `kids: seq[Node]` inside `Node` hits "VM call depth exceeded" in
  type classification (`dsl_typebridge.nim`). A seq of a DIFFERENT ref type
  works and is pinned.
- **The heap-depth budget counts field reads.** Each `p.f` is a deref
  against `maxHeapDepth` (8). A path that reads nine fields of one object
  reports `heDepthExhausted`. The budget bounds derefs per path, not cells,
  and was met here by a test that read four compound fields twice on one
  path.
- **Only part of a table's content renders.** `extractTableEntries` renders
  `int`/`bool` values only, so a `Table[string, float]` field renders its
  keys without values. Witness fidelity calls such a field lossy.
- **The input cell's well-formedness is asserted only where it is read.** A
  cell no path reads is unconstrained in the model, so the renderer clamps
  it (above). This is sound, because nothing observed it. But
  `renderedSize` and the `[0, 1024]` length window are the only guard, and
  a future reader of unread cells would have to assert the facts itself.

### §2.6 The raise-routing recovery — *corrected*

`routeRaise` (`runtime.nim:11380-11384`) kills any tainted path
unconditionally and sets `sawUnknown`, **including for handler-caught
raises**, with the comment "bailed-call retSyms are unconstrained".

Round 1 described the recovered case as an `scIncomplete`-only path. **That set
is empty by construction.** The `pathTaint` function of §2.2 only ever yields
`{}`, `{scSpurious}` or `⊤`, and the set is closed under the union join
(`runtime.nim:11083`) — a path whose taint is `{scIncomplete}` alone cannot
exist. Round 1's DoD pin for this case was therefore unsatisfiable.

The real recovery is the **`scSpurious`-tainted raise**, and it is the same
shape as everything else in §2.3: `routeRaise` must stop killing tainted paths,
route the raise, and let a resulting `sxRaised` enter the candidate pool to be
replay-gated. A `dcOmitted`-only path (path taint `{}`) is already clean and
needs no rule. This aligns §2.6 with §2.3 and makes the DoD pin writable
(§6.2).

## §3 — Classification

### §3.1 The rule

Classify by **what the site substitutes**, never by the mechanism's name:

| substitution | class | examples |
|---|---|---|
| fresh unconstrained symbol | `dcFreshSymbol` | `allocDegrade` arms, R1 placeholder funnel, `degradeStrArm`, `mkUnsupported` in a position that yields a free symbol, the HOF declines of §2.5 |
| forced concrete value / stale env | `dcSubstituted` | `defaultZero`, typed-zero dummy, dropped-statement stale `env`, `maxCallDepth` bail, `feOpaqueCallUnmodelled` |
| fabricated continuation | `dcFabricated` | k-unroll exhausted survivor |
| pure path drop / halt / prune | `dcOmitted` | heap-depth halt, `maxFrontierSize` prune, unsafe-cast halt |
| no answer exists | `dcNoAnswer` | Z3 `unknown` result *and* `ekZ3*` exceptions, `weInternalWalkerFault`, parse-time whole-run declines, signature-scoped declines |

Round-2 corrections to round 1's table:

- **"break-budget bails" is struck from the drop row.** It was a three-way
  conflation (see §3.2).
- **`feOpaqueCallUnmodelled` moves from `dcFreshSymbol` to `dcSubstituted`.**
  `runtime.nim:10682-10698` havocs the return **and drops the callee's
  mutations** — a stale env, not a free symbol. §8.2 previously asserted the
  `dcFreshSymbol` classification; the two give different `sxUnsat` outcomes for
  any SUT that calls `echo`.
- **A solver-undef row is required.** `trySolve`'s `zsUnknown` result
  (§2.2's table) is reachable via timeout and via the deterministic
  `queryRLimit` truncation (`:7458`, `:14354`), and mints no kind today. Mint
  one (`beSolverUndef`, tail-appended), class `dcNoAnswer`. It is also the
  natural carrier for the rlimit provenance §8.2 owes 0011/0008.
- **`eeUnknownExnType` is a behaviour substitution recorded at `sevWarning`**
  (`runtime.nim:11385-11396`): an unknown raised type is matched only against a
  bare `except:`, never a named handler, so where reality's subtype match would
  catch, the walker fabricates an escaped raise *and* drops the handler
  continuation. That is `dcSubstituted` by this table's own rule. Either it
  taints (and the §2.2 severity rule carves an exception for it) or the
  reachability argument for leaving it inert is written down. §6 requires one
  of the two.

`dcNoAnswer` deserves a note: a Z3 resource-out or a walker bug is not an
approximation in either direction — no enlarged or shrunk program exists. It is
nonetheless *represented* as `⊤` on both coordinates, because that forces
`sxUnknown` in both directions by construction, which is exactly the required
behaviour. A separate "fatal" lattice element would be a distinct encoding of
an identical observable; it is rejected in §9.4. What must **not** happen is
laundering a walker fault into a sound verdict by giving it a single channel.

### §3.2 Kind-splitting policy

`classOf` is well-defined only if every site sharing a kind shares a
substitution class. Where the §5 audit finds a kind whose sites diverge,
**split the enum member**, tail-appended for ordinal stability (the enum's own
established convention, `types.nim:1287-1298`). Do **not** add a per-site class
parameter: that re-smears classification across call sites and forfeits the
single-table property. Splitting also improves diagnostics.

**Mandatory splits identified in round 2** (round 1 named only
`feUnsupportedOp`, as "the known candidate"):

- **`beBudgetExhausted` — a ≥3-way split, and the most dangerous row in the
  RFC.** One kind, three classes, merged deliberately
  (`runtime.nim:10759-10769`: "this call-inlining depth cap is a sibling of the
  SAME budget family, so it reuses the kind"): the `maxLoopUnwind` exhaustion
  (`:9550`) is `dcFabricated`; the `maxCallDepth` bail (`:10771-10786`)
  continues with a **fresh havoc `retSym` and the callee's var-param/heap
  effects dropped** — `dcSubstituted`; the `maxFrontierSize` prune (`:9317`) is
  a genuine `dcOmitted`. Six emission sites total (`:9277`, `:9317`, `:9551`,
  `:10246`, `:10284`, `:10771`). Classifying the merged kind `dcOmitted` — which
  is what round 1's §3.1 row implied — gives it `pathTaint = {}` and therefore
  **removes** the taint the `maxCallDepth` site sets today, turning a witness
  through the havoc retSym into an unreplayed `sxSat`.
- **`feUnsupportedOp` — 12 emission sites in `runtime.nim` alone**, spanning at
  least three classes (free retSym, stale-env statement drop, no-zero-default
  fallthrough). Budget for several tail-appended kinds, not one.

**Split discipline.** A split appends **one sibling for the minority funnel**
and keeps the original member for the majority funnel — never retire-and-append-two.
The enum already carries six "retained for ordinal stability, never emitted"
tombstones (`feConvDomainExcluded`, `seByteIndexUnsupported`, `seParseIntPreE`,
`geUnresolvedGeneric`, `ceUnsupportedCapture`, `geVtableDispatch`); each
undisciplined split adds another at permanent cost to every consumer `case`.

**Standing rule, uncheckable by any mechanism:** *reusing an existing kind at a
new site asserts that your site shares that kind's substitution class.* Say it
in the enum's doc comment, because `classOf`'s exhaustiveness cannot catch it.

### §3.3 The residual boundary-abort class

The whole-walk aborts of §1.2 (`runtime.nim:64-213`) can carry no path-scoped
channel until they are migrated in-band, and the §1.5 toolchain constraint
forbids catching them lower. They classify `dcNoAnswer` — always `sxUnknown`,
both channels — and their in-band migration is explicitly **out of scope**
(§11). **Producer: S1** — under the conservative-`⊤` default (§5) these kinds
need no special handling, because the default already gives them `⊤`; the
obligation is only that S6's totality sweep must not "promote" them out of it.
Round 1 stated the classification in the passive voice with no producer at all.

### §3.4 Deliverable

The classification table is a **deliverable of this RFC, not an open
question** — one row per live `SymexErrorKind` (41 members at HEAD, ~6 retired
or never-emitted, plus the kinds minted in S1b), each row naming its class and
citing its emitting funnel. The table **is** `classOf`; there is no separate
document to go stale.

The funnels that concentrate the work: `allocDegrade` (`runtime.nim:1295`),
`degradeStrArm` (`:4904`), the R1 placeholder funnel, the closure/HOF funnel
(§2.5), and the Class-A/Class-B split across the `mkUnsupported` sites in
`dsl_parser.nim`. **The audit checklist is not "the 52 `sawUnknown` write
sites"** — round 1's checklist would structurally miss every
behaviour-substituting site that records no taint at all (§2.2's table,
`eeUnknownExnType`). The checklist is: the 52 write sites, **plus** the
enumerated kindless sites of §2.2, **plus** the `sevWarning`
behaviour-substituting sites of §3.1.

## §4 — Verification strategy

### §4.1 Taint monotonicity — scoped

The draft's property was: *adding an unreachable tainted branch to a green SUT
must never change its verdict*, mechanically generable by grafting a poisoned
disjoint arm onto any existing passing test.

**As stated it contradicts §0.1 and would go red against this RFC's own
design.** The walker forks both arms with no feasibility check
(`runtime.nim:9472-9474`), so a grafted arm *is* walked and *does* taint;
graft a `dcOmitted` arm onto a green `sxUnsat` test and the verdict correctly
becomes `sxUnknown`. It is also weaker than advertised where it does hold: it
exercises taint *scoping* only — swap every channel label and it still passes.

The property this RFC can actually carry, in two families:

1. **Witness monotonicity.** Grafting a disjoint tainted arm onto a SUT with a
   clean witness path must not change an `sxSat`/`sxRaised` verdict. This is
   the honest form of the draft's property and it does encode the path-scoping
   half. **It is also the pin that catches the `shouldStop` regression of
   §2.3** when the tainted arm is discovered *before* the clean witness path —
   make that ordering explicit in the battery.
2. **Classification pins.** A `dcSubstituted` site on the witness path must
   never yield `sxSat` without replay; an over-taint-only run that proves the
   target unreachable must yield `sxUnsat`. These are what test the *labels*,
   which family 1 cannot.

"Graft onto any existing passing test" is not mechanizable — SUTs are procs
defined inside 496 individual test files, not an importable registry. The
buildable form is a test-support macro (`withPoisonedArm`) over a curated SUT
battery in one new file (slice S3, §5).

### §4.2 Witness replay — the execution contract

Any `sxSat`/`sxRaised` this RFC newly permits on a `scSpurious`-tainted path
must have its witness replayed against the real function. Round 1 established
the substrate; round 2 establishes the contract, because replay is the one
mechanism here that **executes user code inside the verdict**.

**Substrate (round 1, verified).** "B7's differential oracle" is not in this
repository — it is chapulin's `t_symex_decode.nim`, and per the standing
consumers-report-don't-drive rule it cannot be this RFC's oracle or its
definition of done. The in-repo substrate exists: `symexTarget` records hits
into a threadvar capture (`markers.nim:63-74`) and `assertCoveredBy`
(`symex.nim:1418`, codegen at `:1560-1643`) already proves a concrete call
reaches a label.

**Interface.** A `bool` conflates *refuted* with *could not run*, which are
different facts with different downstream reporting, and a `label` parameter
cannot serve the raise-flavoured targets §2.3 puts in scope (`SymexTarget` has
six kinds, `types.nim:1203-1216`):

```nim
type ReplayOutcome* = enum
  roConfirmed     ## the real fn reached the target on this witness
  roRefuted       ## the real fn ran to completion; target not reached —
                  ## the witness is proven spurious (a confirmed model gap:
                  ## surface it as its own classified diagnostic kind)
  roInconclusive  ## not faithfully executable, or replay declined —
                  ## the candidate stays sxUnknown

replayWitness(fn, witness, target: SymexTarget): ReplayOutcome
```

**Eligibility gate.** Replay is attempted only for candidates whose path taint
derives entirely from `dcFreshSymbol` sites. A `dcFabricated` candidate is
`roInconclusive` by construction — and that costs nothing, because §0.3 already
argues the k-unroll SAT payoff is empty. This is the gate that bounds the
non-termination hazard below, and `DegradeClass` makes it one line rather than
a site list.

**Hazards, each of which must be addressed in the slice, not discovered in it:**

- **Non-termination.** A fabricated-continuation witness is by §0.3's own
  analysis an input on which the real program may still be looping. The
  eligibility gate excludes exactly that class; what remains is the ordinary
  risk any PBT library takes when it calls a user proc — which nelli already
  takes in `forAll`/`fuzz`. State it; do not build a watchdog (Invariant 3 is
  preserved by the gate, and an in-process watchdog is not safely buildable
  under §1.5's constraint).
- **Side effects.** A path is `scSpurious`-tainted precisely when it ran
  through an unmodelled call — often an *effectful* one (the #137
  `echo`/`writeFile` shape). Replay performs those effects for real, at verdict
  time, in the user's process.
- **Contract change.** `symexFind` (`symex.nim:1220ff`) has never executed
  `fn`. After this RFC it does, on solver-chosen inputs. This is
  consumer-visible and belongs in §8.1 and the migration note — it is arguably
  the most surprising thing in the whole RFC.
- **Defect-flavoured targets.** `stkNilAccess` and friends expect a Defect; a
  raw-pointer nil deref is a SIGSEGV, not catchable. State replay scope per
  target kind, and default to `roInconclusive` outside it.
- **Un-replayable witnesses.** Witness rendering has a restricted fragment
  (`emitTyAndReader`, `symex.nim:575-649`: closures → nil placeholder,
  `__unsupported:` → dummy `int`), and a spurious path's model includes havoc
  symbols the witness does not pin. Both are `roInconclusive` → `sxUnknown`,
  permanently. Say so.
- **Capture reentrancy.** `symexCaptureBegin` *clears* the hit-set
  (`markers.nim:50-54`), so engine-internal replay during a user's active
  `assertCoveredBy` capture clobbers it. The capture context must become
  stackable — that is part of the substrate slice.
- **Naming collision.** `sfReplayMiss` already exists on `SymexFindingStatus`
  (`engine/types.nim:29-35`) as replay vocabulary from Phase 14 B5. Reuse it or
  distinguish it explicitly.
- **Tainted-solve cost (found in S1c).** Rule 3 needs a model, so S1c solves
  every target-hit path, tainted or not -- queries no engine before it ever
  issued. A tainted path's pc carries whatever a degraded lowering left behind,
  and the N36 `iekStrInOptionRegion` BV-bound decline's residue spins Z3's
  `check` without end under the default `queryRLimit = 0`: an unbounded solve
  there would be a NEW non-termination, not a pre-existing one. S1c bounds it
  (`taintedSolveRLimit`: the caller's explicit `queryRLimit`, else
  `defaultConcreteBranchRLimit` = 20M) and the bound's `zsUnknown` is the
  honest `beSolverUndef`. The bound is finite but not cheap: on
  `tsymex_rfc0005_s1c_verdict`'s N36 shape six tainted queries each run to the
  full 20M, which is ~230 s of wall time under default settings (measured at
  S10 with `-d:symexQueryStats`), well past `dt-bounded.sh`'s 180 s default
  (the sweep's 900 s covers it). A caller's explicit `queryRLimit` shrinks it
  (1M: ~12 s, same verdict). Replay adds nothing here -- the candidates it
  receives are already solved -- but a tighter default tainted budget is a
  live tuning question, not a closed one.

**Plumbing — replay cannot live in `runSymex`.** Invoking the SUT requires
splatting a typed witness into its parameter list with `var`-param wrapping;
that is macro codegen (the existing template is `assertCoveredBy`'s splat
block, `symex.nim:1481-1490`, `:1555-1643`). `runSymex` is runtime code and has
no `fn`. Therefore **replay runs in macro-generated code after `runSymex`
returns**, and `RawResult` must carry candidacy across that boundary in a form
that cannot be mistaken for a plain `sxSat` — a distinct raw status
(`sxSatCandidate`) or a field every `SymexResult` construction must explicitly
discharge, so an entry macro that forgets to replay **fails to compile** rather
than mis-reporting. There are exactly two `runSymex` callers — `symexFind`
(`symex.nim:1272`) and the `symexFindAllWitnesses` codegen (`:2061-2063`, also
reached by `symexForAll` via `toFindingStatus`, `:408`) — and **both** must
discharge it. A `symexFind`-only implementation leaves `symexForAll` either
unsound or dark, and round 1's DoD wording ("replay confirmed in the reporting
path", singular) did not force the second.

**As landed (S10).** Candidacy crosses the boundary as `SatCandidate`
(`smt/runtime.nim`), a type with no `witness`/`raisedWitness` branch whose
model is a PRIVATE field. It is readable only by `symex.nim`'s private
`candidateInput`, and a verdict can be made from it only by the private
`settleCandidate`, and only on `roConfirmed`. Both are reached solely through
`bindSym` in `emitRunSymexReplayed`, which is the ONE `runSymex` call site
behind both entry macros. An entry macro that skipped the settle could not
mis-report: it would see `sxUnknown` and a pool it cannot render. The
compile-time and structural pins live in `tsymex_rfc0005_s10_replay_verdict`.
Each hazard above is contained as follows:

- **Non-termination.** The eligibility gate (`replayEligible`: path taint
  `<=` `{scSpurious}`) is unchanged, and there is no watchdog.
- **Side effects.** These are run for real, once per replayed candidate, in
  discovery order, stopping at the first confirmation. An ineligible or clean
  result runs nothing, and the tests pin that with an effect counter.
- **Defects.** Under `--panics:on` every target is declined, not just Defect
  targets, because a candidate's real run may hit a Defect the model never
  forked. `tNilAccess` is always declined.
- **Un-replayable witnesses.** A `feExtractionFailed` model is lossy: it
  confirms on a hit and never refutes.
- **Naming.** A refutation is the new `feReplayRefuted` hint on a `sxUnknown`
  result, not `sfReplayMiss`, which stays Phase 14 B5's per-seed diagnostic.
- **Raises (§2.6).** `routeRaise`'s spurious raises reach the same pool, and
  an `sxRaised` claim replays against `tRaisedExn(<its type>)`.
- **parseInt.** The raise predicate is split so that Nim's `+`/`_` syntax
  (which `str.to_int` rejects) raises only on a `seParseIntLaxSyntax`
  (`dcFreshSymbol`) candidate. Before this, it was a clean `sxRaised` that
  could be false (`"+5"`).
- **Cache.** Replay precedes persist, structurally: the cache writers run on
  the settled result.
- **Link/load contract (found by S10's sweep; decided: stated contract with
  an opt-out).** Replay needs a real call to `fn` in the generated code. So
  with replay on, `fn` and everything it calls are compiled, LINKED and LOADED
  into the calling binary, whether or not any candidate is ever replayed.
  Before S10, `fn` was only read at macro time.
  - An `importc` with no definition now fails the link. This was
    `tsymex_phase15_g5_distinct_borrow`'s deliberately unlinkable stub.
  - A `dynlib` the host lacks now fails at start-up. `std/re` loads PCRE1:
    `libpcre.so.1` on Linux, `pcre64.dll` on x64 Windows.

  No runtime gate can contain either failure, because both happen before any
  replay decision runs.

  The opt-out is `SymexSettings.replay = false`. It is static at every entry
  macro, so no reference to `fn` is emitted and every candidate stays
  `sxUnknown` as before S10. It enters the cache key as `;rp=off`, and only
  when off, so default keys are unchanged. g5 opts out. The regex suites keep
  full coverage instead:
  - the dev image builds PCRE 8.45 from hash-pinned source, since Tumbleweed
    ships only PCRE2;
  - `symex-mingw`'s corpus job puts the hash-pinned `pcre64.dll` from Nim's
    official `dlls.zip` on PATH.

  The S11 migration note leads with both contract changes: `fn` is EXECUTED,
  and `fn` must LINK and LOAD.

Replay is therefore a **verdict mechanism**, not a test oracle, and it is the
single largest piece of genuinely new machinery in the RFC.

### §4.3 The `sxUnknown` pin audit

272 `== sxUnknown` assertions across 110 test files pin today's conflated
verdict. Every over-taint-only run among them that proves UNSAT flips to
`sxUnsat` under §2.3. Candidates include the honest-decline pins at
`tests/tsymex_r6_n21_pairloop_member.nim:171,213,242` and the SND-3 family at
`tests/tsymex_snd3_loopdegrade.nim:109-127`. **Each flip must be individually
re-justified** in the slice that causes it — some of those pins exist
specifically to assert that the engine declines honestly, and a flip there is
either the payoff or a soundness bug, with no way to tell them apart in
aggregate.

**Round 2 made this tractable in two ways.** Round 1 scheduled the whole audit
as one slice (S6) positioned *before* any verdict-changing slice — where
**zero pins can flip**, making the audit an empirical no-op and the
"individually justified" requirement unsatisfiable in the same breath.

1. **The audit attaches to each verdict-changing slice**, covering only the
   pins that slice flips. Under §5's per-funnel sequencing, that is a handful
   of pins per slice, and a misclassification is caught by its own slice's
   flipped pins instead of by one big-bang landing.
2. **Justification is a checked line, not prose.** Export a helper
   (`SymexResult.errors` is already public, `types.nim:1906`):

   ```nim
   checkUnsatOverTaintOnly(r)
     ## asserts r.status == sxUnsat AND every drained error maps through
     ## classOf() to a class with scIncomplete notin runTaint(class)
   ```

   The flip list itself is generated by `sweep-diff` against the sha-pinned
   baseline, so the audit is *find the diff, rewrite each line through the
   helper, justify anything the helper cannot express*.

The converse risk raised at round-1 kick-off does **not** exist: no k-unrolled
run reports `sxUnsat` today (any degrade sets `sawUnknown`, which already voids
it), so the 283 `== sxUnsat` assertions across 130 files are taint-free runs by
construction and cannot regress. The change is a relaxation on both sides.

### §4.4 Process gates

- Every slice lands on an **`rfc-0005-*` branch** — `rfc-*` naming is what
  triggers the three Windows legs (`fuzzer-msvc.yaml:66`,
  `fuzzer-mingw.yaml:43`, `symex-mingw.yaml:118`).
- `tests/tsymex_r6_b7r2_pathscope.nim` — the opOack-faithful path-scoped-taint
  composite, i.e. the single most relevant pin suite for this work — is one of
  the six Linux/podman hangers skipped by name (`scripts/sweep.sh:91-96`).
  **The exact area under change is verifiable only on Windows CI**, and the SAT
  slice (S10) has *no local gate at all*. Local gating elsewhere is
  `sweep-diff` against a sha-pinned baseline over the remaining suites.
- **Price the Windows gate.** `symex-mingw` runs the derived corpus (parsed
  from `nelli.nimble`'s test task) in 60-min-capped shards plus 90-min-capped
  per-suite scan-tail jobs: roughly **1–1.5h wall per push**, and the plan has
  13 slices. Windows CI is a required gate on every **semantics-bearing** slice;
  batch the non-semantic ones (S1's carrier pieces; the classification slices
  under their shared bump) into one gated push each.
- New test files must be registered in `nelli.nimble`'s `test` task or they
  land in `.drift` and run in **no** CI leg. That applies to every new file this
  RFC creates.
- Existing suites to extend rather than duplicate:
  `tests/tsymex_163rev_degrade_classification.nim`,
  `tests/tsymex_r6_degrade_pairing_audit.nim`,
  `tests/tsymex_r6_n40_alloc_totality.nim`.

## §5 — Slice plan

Each slice is a vertical RED-GREEN-REFACTOR unit with a named failing test.
Blast radius is listed because a single implementing agent inherits it as
context; anything spanning more than ~2–3 modules is a round, not a slice.
Remember the path convention: the five `runtime_*.nim` files are **`include`d
into `runtime.nim`** — "the runtime unit" below means all six, ~17.6k lines.

**The two sequencing decisions round 2 changed, and why.**

1. **`classOf` is total from S1 with a conservative `⊤` default.** Every kind
   is mapped on day one; unaudited kinds map to `dcNoAnswer`. All-`⊤`
   reproduces today's behaviour bit-for-bit (any taint blocks both verdicts),
   so the verdict rule can land *early* as a behaviour-preserving refactor and
   each classification slice then flips only its own funnel's pins. Round 1
   built a lattice, a replay engine and a harness across eight slices during
   which **no observable verdict changed**, then turned everything on at once
   at S7 — which is how an RFC ships green-but-inert, and which made its own
   top risk (a single under-as-over misclassification) undetectable until the
   big bang.
2. **The `isTargetLabel` tainted-path solve moves into the UNSAT slice.** Round
   1 put the verdict rule in S7 and the solve in S8. That boundary mints a
   false `sxUnsat` (§0.1, §2.3): a tainted path that reaches the target and is
   never solved is an omission, so rule 5 cannot be shipped without it.

| # | slice | blast radius | RED |
|---|---|---|---|
| **S0** | **Exhibit the discarded capability.** A SUT run through `symexFind` — the real entry point — that is over-taint-only and proves its target unreachable, pinned **green** today as `sxUnknown` **plus its expected drained error-kind set** (`SymexResult.errors` is already public, so the over-taint-only status is *asserted*, not assumed). Add the §2.5 veto companion: a clean-path witness plus a `sevError` decline behind an unreachable branch, pinned `sxUnknown` today. Flipping these is S6's and S9's RED. | 1 new test file + `nelli.nimble` | characterization pin (green) |
| **S0b** | **Measure the payoff before building it.** Throwaway `-d:`-gated dump of drained error-kind sets at the verdict site (~5-line diff, reverted), one podman sweep over the 110 pin files, classify observed kind-sets against §3.1. Output: the count of over-taint-only `sxUnknown` runs. **Gate: if the count is near zero, §13.1 re-opens scope before any product code is written.** | throwaway instrumentation; no product code | n/a (spike) |
| S1 | **Lattice + carrier.** `SoundnessChannel`/`Taint`/`DegradeClass`; `classOf` **total with `dcNoAnswer` default**; `pathTaint`/`runTaint`/`channels`; `Path.uncertain` → `Path.taint` (79 refs); `w.runTaint` **derived at drain** from the error seqs; the `degrade()` funnel + `Degrade` token + `taintInPlace`; `forkPathTainted` takes a `Degrade`; `loweringDidDegrade` → `loweringPendingTaint` + its leak pin; `RawResult.pathTaint`; the `.taint`/`.runTaint` writer grep-pin. No verdict change. | runtime unit + `types.nim` | the H1-style compile-time hook (`runtime.nim:686-699` — `Path` is private, tests cannot name it directly) |
| S1b | **Mint the missing kinds** (§2.2's table): `mkUnsupported(kind, reason)` across ~40 `dsl_parser.nim`/`canonicalize.nim` sites; new kinds for cycle-break, handler re-raise, diverged body, break/continue, `beSolverUndef`; over-cap missing-callee carries its kind at the site. Land the **correspondence pin**: `runTaint` equals the union over drained errors, mismatch → `weInternalWalkerFault`. Still all-`⊤`, so still no verdict change. | `dsl_parser.nim`, `canonicalize.nim`, runtime unit, `types.nim` | correspondence pin on a SUT whose degrade records no error today |
| S1c | **The verdict rule** (§2.3): ordered procedure, `w.candidates` pool, `shouldStop` excludes candidates, `isTargetLabel` solves `scSpurious`-tainted paths, unsolved-skip contributes `scIncomplete`, `routeRaise` stops killing tainted paths. Behaviour-preserving under all-`⊤`. **The consumer now exists — the RFC runs end-to-end from slice 5.** | runtime unit | S0's exhibit still `sxUnknown`, *and* a witness-monotonicity pin with the tainted arm discovered first |
| S2 | **Replay substrate** (§4.2): `ReplayOutcome`, target-shaped `replayWitness` macro, eligibility gate, stackable capture context. Not yet wired to the verdict. | `markers.nim`, `symex.nim`, 1 test file | direct replay test: confirmed / refuted / inconclusive |
| S3 | **Taint-monotonicity harness**: `withPoisonedArm` + curated battery (§4.1). | 1 new test file + support macro | the battery |
| **S4** | **Classify the `allocDegrade` funnel** (`runtime.nim:1295`) — **and this is where S0's exhibit flips**, because S0's SUT is chosen to route through this funnel. First observable payoff: slice 6 of 13. Carries its own flip audit (§4.3). | runtime unit | S0 exhibit flips `sxUnknown` → `sxUnsat` |
| S5 | Classify `degradeStrArm` + the R1 placeholder funnel; own flip audit. | runtime unit | that funnel's flipped pins |
| S6 | Classify heap/halt sites + the `beBudgetExhausted` and `feUnsupportedOp` splits (§3.2); own flip audit. | runtime unit, `types.nim` | that funnel's flipped pins |
| S7 | **Cross-path sinks + closure taint** (§2.4, §2.5): admission rules on all seven sinks pinned against the live drain list; closure-descent taint joins the calling path; **every value-substituting closure/HOF decline routed through `w.degrade` + path taint** (the precondition for S9). | runtime unit | a witness through `__hofFilterUnsupported` must not report clean `sxSat` |
| S8 | **Decline-scope representation**: `DeclineScope` on `SymexErrorInfo`; Class-A/Class-B unification so every site-anchored decline mints a marker; callee-key anchoring; the structural totality pin + the bucket-4 count. **Vetoes retained — no verdict change.** | `dsl_parser.nim` (39 `parseErrors.add` sites), `types.nim`, runtime unit, 1 test file | the totality pin, initially red with an enumerated bucket-4 list |
| S9 | **Delete both blanket vetoes.** Verdict-changing; own bump; own flip audit. | runtime unit | S0's veto companion flips to `sxSat` |
| S10 | **SAT relaxation**: replay wired into the verdict across **both** `runSymex` consumers, candidacy made unspellable-as-sat, `routeRaise`'s spurious raises replay-gated (§2.6). Windows-only verifiable. | runtime unit, `types.nim`, `symex.nim` (both entry macros + cache helpers) | DoD §6.2's trio |
| S11 | **Public surface** (§8.1): the `Soundness` object, `gaps()`, `SymexFinding` + render layer, cache value schema, docs. | `types.nim`, `symex.nim`, `engine/types.nim`, `engine/render.nim`, examples | a `forcedBy`-shape assertion through `symexFind` |

**Totality of the totality claim.** The audit sweep round 1 scheduled as "S6"
is gone as a separate slice: under the conservative default, every kind is
already classified, so there is no sweep to do — only per-funnel
reclassification with per-funnel flip audits. What remains of S6's other half
(the Invariant-7 extension) lands in S1b's correspondence pin.

## §6 — Definition of done

Not "the suite passes". The RFC is done when:

1. The **S0 exhibit** — a named in-repo SUT, run through `symexFind`, the real
   entry point — flips from a recorded `sxUnknown` to `sxUnsat` at S4, with
   its over-taint-only status asserted from the public `errors` seq, not
   assumed.
2. **The SAT half's live payoff is pinned, both halves of it** (§0.3):
   - S0's **veto companion** — a clean-path witness plus a `sevError` decline
     behind an unreachable branch — flips `sxUnknown` → `sxSat` at S9, through
     `symexFind`; plus a closure-veto companion.
   - A named SUT whose witness lies on a `dcFreshSymbol`-tainted path is
     reported `sxSat` **with `replay == rsConfirmed` in the reporting path**,
     a companion whose witness is refuted stays `sxUnknown`, and a third pins
     §2.6: a **`scSpurious`-tainted** raise is routed and replay-gated rather
     than killed. *(Round 1's third pin named an `scIncomplete`-only path,
     which §2.6 shows is unconstructible.)*
   - Both pins run through **`symexFind` and `symexForAll`/`symexFindAllWitnesses`** —
     the two `runSymex` consumers (§4.2).
3. Every pin the plan flips is individually justified **in the slice that
   flipped it**, via `checkUnsatOverTaintOnly` where the helper can express it
   (§4.3).
4. The must-NOT-flip guards hold: `tests/tsymex_r6_n20_boundedloop.nim:126,144`
   stay `sxUnknown` (no witness + under-taint voids unsat);
   `tests/tsymex_r6_b7r2_pathscope.nim:381` stays `sxUnknown` (over-decline on
   the witness path).
5. `classOf` is total over `SymexErrorKind`, pinned by a totality test; the
   §2.1 **introduction invariant** ("a `dcFreshSymbol` site's symbol carries no
   constraints at introduction") is pinned for every `dcFreshSymbol` kind; the
   §2.2 **correspondence pin** (`runTaint` = union over drained errors) is
   green; the `.taint`/`.runTaint` writer grep-pin is green; and
   `eeUnknownExnType` is either classified-and-tainting or has its
   leave-inert argument written down (§3.1).
6. Both blanket vetoes deleted, the `DeclineScope` totality pin green, and the
   count of `dskUnplaced` declines (§2.5 bucket 4) **recorded in the slice's
   own test** — the target is zero, and a non-zero count must be an
   enumerated, named list rather than a tolerance. *(S8: the pin covers every
   `sevError` construction, walker records included — see §2.5 "As landed";
   the two `feTransparent*` kinds are not in it because §13.3 moved them off
   the decline lattice, not because they were demoted or companion-scoped.
   Recorded count: 0, in `tests/tsymex_rfc0005_s8_scope.nim`; the Invariant-7
   backstop is the one construction `dskUnplaced` by design, named there.)*
7. §7's version and cache discipline discharged **including the cache value
   schema**; the `docs/migration/<version>.md` entry written (§8.2); Windows CI
   green on all three legs; `sweep-diff` against a sha-pinned baseline shows
   `regressed=0`.

## §7 — Version-pin, cache and process discipline

Walker semantics change here, so per the standing rule each semantics-bearing
slice bumps `symexWalkerVersion` (`canonicalize.nim:187`, `"140"` at HEAD),
updates the **brittle `==` pin** in `tests/tsymex_phase15_CR2_cachekey.nim`
(which has shipped red before for exactly this omission), and adds a `>=` floor
pin in the round's own test file (pattern:
`tests/tsymex_163rev_concolic_diagnostics.nim:517`).

**The semantics-bearing slices are S4, S5, S6, S7, S9 and S10 — six bumps, not
two.** Round 1 scheduled bumps for "S7, S8 and any classification slice", with
one shared bump across S3–S6; under the new sequencing each classification
slice changes observable verdicts, so each needs its own bump and its own CR2
pin update. S9 in particular was previously unscheduled entirely and is
verdict-changing.

**Cache key.** The cross-run verdict cache (`symex.nim:259-331`) persists
`sfUnsat`/`sfUnknown` sentinels keyed on the walker version, so a bump
invalidates it and the taint need not enter the cache key. Pre-bump entries
orphan unread rather than being evicted — harmless, worth one sentence in the
migration note.

**Cache value schema — round 2 addition.** The key is handled; the *value* is
not. The stored verdict sentinel is an **empty `seq[ChoiceNode]`**
(`saveSymexVerdictImpl`, `symex.nim:259-297`), and `loadSymexRaisedImpl`
(`:389-410`) reconstructs `RawResult(status: sxRaised, raisedTypeId)` and
nothing else. So on every cache hit:

- an `sxUnknown` cannot carry `forcedBy != {}`, breaking §8.1's Invariant-7
  extension, and the actionability payoff never reaches the consumer that
  needed it most (the repeat run);
- an `sxSat`/`sxRaised` cannot carry `pathTaint`/`replay`, so a served result
  cannot state whether it was replay-confirmed.

**Decision: widen the sentinel to carry `Soundness`** (§8.1). The walker-version
key already invalidates the format for free, so the schema change costs
nothing, and it keeps cross-run reuse rather than trading it away. Two ordering
rules ride with it: **replay precedes persist** — a tainted `sxSat`/`sxRaised`
is never written to the cache before `roConfirmed` — and a served result carries
its stored `Soundness` unchanged. (The alternative, restricting what may be
cached, is recorded in §9.9.)

Any new `SymexErrorKind` member is tail-appended (`types.nim:1287`). The in-run
summary cache is handled at §2.4.

**Batch 1 (2026-10-01) — one walker number for six slices.** S8ag, S8am, S8an,
S8ap, S8aq and S11 were built in parallel on the channel tip, each with a
provisional walker number (S8ag, S8am, S8an and S8ap 183; S8aq 187; S11 188).
They land stacked, in that order, on one integration branch under ONE number:
`symexWalkerVersion` 182 -> **190**, the CR2 `==` pin 190. Each slice's own
`>=` floor stays at its provisional number (all at or below 190); the "walker
183/187/188" in each "As landed" heading is that provisional number. S8am's
`renderAsChoicesVersion` 11 -> 12 is unchanged. S11 adds no separate cache
schema version: its widened cache value rides the walker key.

## §8 — Consumer surface and migration

### §8.1 What consumers see

Do **not** grow `SymexStatusKind` — `sxUnknownOver`/`sxUnknownUnder` would
conflate two axes in one enum and break every `case` for no gain.

**One common field, not three variant-branch fields.** Round 1 proposed
`forcedBy` on the `sxUnknown` branch and `satPathTaint`/`replayVerified` on the
`sxSat` branch. That is internally inconsistent — §2.3 makes `sxRaised` obey
the SAT rules verbatim, and §6.2 pins a replay-gated raise, but round 1 gave
`sxRaised` no taint fields at all, making the pinned case unauditable on the
public surface. It also forces every generic consumer (the verdict cache,
`toFindingStatus` wrappers, logging) to `case`-split merely to *read* the taint.
`SymexResult` (`types.nim:1888-1933`) already keeps cross-status facts in its
**common** section — `errors`, and `heapSnapshot`, which is documented as
"EMPTY for a SUT with no ref/ptr params". Follow that precedent:

```nim
type
  ReplayStatus* = enum
    rsNotNeeded    ## clean path — replay was not required
    rsConfirmed    ## roConfirmed (refuted/inconclusive never ship on a winner)

  Soundness* = object
    pathTaint*: Taint  ## winning path's taint (sxSat/sxRaised); {} otherwise
    runTaint*:  Taint  ## run-global taint; on sxUnknown this is round 1's
                       ## `forcedBy`, with the Invariant-7 extension != {}
    replay*:    ReplayStatus

  # RawResult / SymexResult common section gains:  soundness*: Soundness
```

and the single predicate the whole RFC exists to license:

```nim
func trusted*[T](r: SymexResult[T]): bool =
  case r.status
  of sxSat, sxRaised: scSpurious notin r.soundness.pathTaint or
                      r.soundness.replay == rsConfirmed
  of sxUnsat:         scIncomplete notin r.soundness.runTaint
  of sxUnknown:       false
```

**Actionability is per-cause, not the aggregate.** Round 1 claimed `forcedBy`
tells the caller which lever to pull. It does not, and the reason is structural:
`runTaint` is the **join** over every degrade in the run, so a SUT with one
`echo` and one deep loop reads `⊤` — "model gap" *and* "budget problem" at once
— when the right moves (mark the `echo` transparent, raise `maxLoopUnwind`) are
both recoverable from the classified error list. With 52 degrade sites, `⊤` will
be the *common* value on real SUTs. `soundness.runTaint` is the O(1) **verdict**
input; the actionable surface is the per-cause view, and `DegradeClass` is
exactly the lever taxonomy:

```nim
func gaps*[T](r: SymexResult[T]): seq[tuple[class: DegradeClass, e: SymexErrorInfo]]
  ## dcOmitted      → raise the named budget (maxLoopUnwind / maxCallDepth /
  ##                  heap depth / maxClosureInlineCount) — the caller can fix it
  ## dcFreshSymbol,
  ## dcSubstituted  → a model gap: engine work, or mark the call transparent
  ## dcFabricated   → the bound was hit and the continuation is fiction
  ## dcNoAnswer     → solver resource-out or a walker defect
```

**Known consumers to update** — round 1's list was short by four:
`toFindingStatus` (`symex.nim:408-412`), the `SymexResult` codegen arms
(`symex.nim:1288-1319`, `:1559-1610`), `symexFindAllWitnesses`' verdict arms and
cache path (`:2038-2089`), the seed filter (`:537`), the verdict cache (§7),
**`SymexFinding` (`engine/types.nim:37-70`) and the render layer
(`engine/render.nim:21`, `:135`)** — the Z3-free record that reaches the
terminal report and the ofJson/ofJunit/ofGithubAnnotation renderers, which
round 1 never mentioned and without which the payoff never reaches anyone
reading a report — plus `examples/symex_loops.nim` and
`examples/symex_stdlib_model.nim`, and the `symexOpaque` doc comments
(`symex.nim:1096-1134`) which promise "costs precision (an extra sxUnknown)".

**One caveat on the example.** `examples/symex_loops.nim` records in its own
header (lines 60-63) that it **stopped compiling for a full release cycle with
nobody noticing, because `examples/` is built by neither CI nor `nimble test`**.
Putting the worked "read `gaps()`, pull the right lever" walkthrough there and
nowhere else deposits this RFC's user-facing payoff in dead code. S11 puts the
walkthrough in a **registered test file** and lets the example mirror it.

**As landed (S11, walker 188).** Pins: `tests/tsymex_rfc0005_s11_surface.nim`
(public imports only — `nelli`, `nelli/symex`), registered in `nelli.nimble`.
Migration note: `docs/migration/0.9.0.md`, with a CHANGELOG `[Unreleased] —
0.9.0` entry.

- **Placement (a deviation from §8.2's sentence, not from its constraint).**
  `SoundnessChannel`/`Taint`/`DegradeClass`, the new `ReplayStatus`/`Soundness`
  and the annotation vocabulary (`SymexAnnotation`, `AnnotationViolationKind`,
  `AnnotationViolation`) moved out of `smt/types.nim` into a new leaf module,
  `smt/soundness.nim`, which has no imports at all. `smt/types.nim`,
  `engine/types.nim` and `symex.nim` re-export it. The reason is
  `SymexFinding`: `engine/types.nim` is the Z3-free record and must not import
  `smt/types.nim`, but it now carries `Soundness` and `AnnotationViolation`.
  §8.2's real requirement — the lattice is Z3-free so RFC-0007 can share it —
  holds more strongly than before.
- **One carrier.** `RawResult.pathTaint` became `RawResult.soundness`
  (`pathTaint`, `runTaint`, `replay`), and `SymexResult` gained the same field
  in its common section, exactly as §8.1 sketched.
  - `runTaint` is derived once, at `runSymex`'s public exit, from the final
    error list (`runTaintOf`, after the boundary overrides). The S1 writer pin
    now names `runtime.nim:runSymex` beside `runSymexImpl`, with that
    justification.
  - `settleCandidate` re-derives `runTaint` for a confirmed claim, because the
    candidate's own extraction errors join the result's list, and it is the
    single writer of `rsConfirmed`.
- **`trusted()`** is §8.1's predicate verbatim (`trustedSat` / `trustedUnsat`
  on `Soundness`). `SymexFinding` has its own overload; `sfNotApplicable` and
  `sfReplayMiss` are never trusted.
- **`gaps()`** returns the `taintsRun` entries paired with `classOf` (via
  `gapsOf`, shared with the finding). It therefore omits hints and warnings,
  and its class join equals `soundness.runTaint`, which a test pins. The lever
  table is its doc comment. `SymexFinding.gaps` is the Z3-free projection
  (`FindingGap`: `class`, `kind` as a string, `msg`). It is empty on a cache
  hit, because the cache stores the soundness, not the error list.
- **Bound echo:** `bounds: ResourceBudget` on `RawResult` and `SymexResult`, set
  from `settings.budget` on every status (§8.2's decision).
- **Invariant-7 backstop strengthened.** The `sxUnknown` backstop used to fire
  only on an EMPTY error list. An `sxUnknown` whose errors were all hints or
  warnings (no run-tainting entry) shipped `runTaint == {}`, which breaks
  §8.1's "`forcedBy != {}`" and leaves `gaps()` empty. It now fires when
  `runTaintOf(errors) == {}`, which is the same `weInternalWalkerFault`, at
  the same single site.
- **Cache value schema (§7).** Each entry's `Soundness` rides the
  `ExampleDatabase` per-entry metadata (F6's `save(..., meta)` /
  `loadPrimaryWithMeta`), under the key `soundness` with a versioned encoding
  (`"1:<pathBits>:<runBits>:<replayOrd>"`). This applies to the `:sat`
  witness entries, the `:unsat`/`:unk` sentinels and each `:raised:<type>`
  sentinel.
  - A served result carries the stored `Soundness` unchanged.
  - An entry without the metadata is a **miss**, with a note in the errors,
    never a clean verdict.
  - Replay already preceded persist (S10). `symexFindAllWitnesses` now saves
    the settled `f.soundness` with the verdict.
  - The public helpers changed shape. `saveSymexVerdict(Impl)` takes a
    `Soundness`; `loadSymexVerdict(Impl)` returns `Option[CachedVerdict]`;
    `loadSymexWitnesses(Impl)` returns `seq[CachedWitness]`.
  - A backend that leaves the metadata closures nil (a hand-built
    `ExampleDatabase`) is reported and skipped, never called. Calling a nil
    closure is a SIGSEGV, which the cache's best-effort `try` cannot absorb,
    and the S11 suite's first RED was exactly that crash.
- **`SymexFinding` and the render layer.**
  - Every finding built in `assertCoveredBy` and `symexFindAllWitnesses`
    carries `soundness`, `gaps` and `annotationViolations`. The violations are
    parse-time facts, so they are present on a cache hit too.
  - `engine/render.nim` adds:
    - `ofText`: a `[symex]` section;
    - `ofJson`: a `symexFindings` array;
    - `ofJunit`: `<system-out>`;
    - `ofGithubAnnotation`: an `::error` per annotation violation, and a
      `::warning` per untrusted finding other than not-applicable and
      replay-miss.
  - All of it is additive: a report with no findings renders byte-for-byte as
    before, which is pinned.
- **The seed filter** (`symexForAll`, `status == sfSat`) needed no change.
  Since S10 every shipped `sfSat` is trusted by construction. A comment there
  records why.
- **Docs.**
  - The `symexOpaque`/`symexTransparent` doc comments (and the parser's twin)
    now describe the `dcSubstituted` gap, replay, and the
    annotation-violation channel in place of "an extra `sxUnknown`".
  - `examples/symex_loops.nim` mirrors the registered walkthrough (suite (c)).
  - `examples/symex_stdlib_model.nim` reads its gap.
- Walker 182 → 188 (S11 widened the cache value and strengthened the
  backstop). The CR2 `==` pin was updated; the S11 file carries the `>= 188`
  floor.

*Different mechanisms, reported and not fixed here.*
- **The public cache macros drop their DB errors.** `saveSymexWitness`,
  `loadSymexWitnesses`, `saveSymexVerdict` and `loadSymexVerdict` collect
  `dbErrors` into a block-local `{.used.}` variable and discard it. The comment
  at the site has deferred the wiring since Phase 13 cycle 7. A caller of those
  macros therefore never sees an S11 miss reason, or any other save or load
  failure. `symexFindAllWitnesses` is unaffected: it routes its errors. This is
  pre-existing, and a different mechanism from S11's schema: it is the
  macros' error plumbing.
- **`ExampleDatabase`'s optional closures are unchecked everywhere else.**
  S11 guards the symex cache against nil `saveWithMetaImpl` /
  `loadPrimaryWithMetaImpl`. `db.nim`'s public wrappers (`save(..., meta)`,
  `loadPrimaryWithMeta`, and the corpus/secondary/scheduler wrappers) still
  call whatever closure is set, and the fuzzer's F6 paths reach them, so a
  partial hand-built backend crashes there with a SIGSEGV rather than an
  error. This is pre-existing and belongs to `db.nim`'s record contract, not
  to the symex surface.
- **A cache hit's `gaps` is empty.** The schema stores the run's `Soundness`,
  not its error list. A served `sfUnknown` is therefore untrusted, with its
  `runTaint` intact, but it cannot name its levers until it is re-run cold.
  Storing the classified errors as well would be a schema widening that §7 did
  not ask for. It is recorded here so that a consumer who needs per-cause data
  from a warm run knows the current shape.

### §8.2 Downstream RFCs

**RFC-0011 (effect-annotations) is blocked on this RFC, and round 1's
provenance answer does not work.** 0011's `checkRaises` rests entirely on
`sxUnsat` claims — the half §0.3 identifies as the real payoff, which makes
0011 the motivating application the original draft lacked. 0011 §3 asks *which
bound* an `sxUnsat` held under ("a proof under `maxLoopUnwind = 8` is not a
proof"), and RFC-0008 (assurance-record) wants the same.

Round 1 answered: ship the bit, carry provenance in the `errors` seq. **That is
structurally impossible for the case 0011 needs.** An `sxUnsat` under §2.3 has
`scIncomplete notin runTaint` — so **no under-channel error entries exist on
precisely the runs whose bounds 0011 wants to record**. "Which bound did this
proof hold under" is a property of the *settings*, not of an error that by
construction was never minted. (`SymexErrorInfo` is also `kind + severity +
msg` — free text, no structured budget field.)

**Decision: bound provenance is a settings echo on the result**, not an error —
one additive field carrying the budget values the run actually used, shipped in
S11. It is small, it is correct for the `sxUnsat` case, and it gives 0011 and
0008 a single carrier. The claim that `errors` carries it is struck.

**RFC-0007 (trace-properties)** is a third downstream: it states at
`docs/rfc/0007-trace-properties.md:123` that "the same over/under-approximation
discipline RFC-0005 is building for symex applies here, in a different engine",
while declaring `Depends on: none` at `:38`. Per `docs/rfc/README.md` that soft
edge belongs in 0007's own Depends-on block. It also pins a type-placement
constraint worth stating: `SoundnessChannel`/`Taint`/`DegradeClass` go in
`smt/types.nim`, which imports no z3 — that is what lets 0007's trace engine
share the lattice.

**Coverage interplay — round 1's paragraph is factually wrong at HEAD.** It
claimed `{.cover.}`'s injected `recordEdge` calls are opaque and force whole-run
`sxUnknown`, and advised marking them `{.symexTransparent.}`. Issue #163 already
did exactly that (`src/nelli/coverage.nim:100-140`, which documents the change
as the G3fix follow-up): the parser **drops** the calls, so a `{.cover.}`'d SUT
taints nothing and the advice instructs users to add a pragma the procs already
carry. The live interaction is **user `{.symexOpaque.}` procs and the #137
opaque-call arm** (`canonicalize.nim:568`, `:586`) — now a named `dcSubstituted`
row in §3.1, because it havocs the return *and* drops the callee's mutations.

**Migration note.** Verdict changes are consumer-visible, so the release
carrying the first flipping slice needs a `docs/migration/<version>.md` entry
per `docs/rfc/README.md`. **It must lead with the contract change, not the
verdicts**: after this RFC, `symexFind` may *execute the SUT* at verdict time on
solver-chosen inputs (§4.2). No per-RFC downstream-audit document — that format
is retired.

## §9 — Alternatives considered

1. **May/must framing.** This is the standard abstract-interpretation
   vocabulary for the same duality (over ≈ may-analysis, under ≈
   must-analysis), and incorrectness logic's under-approximate triples are the
   same idea on the proof side. *Adopted as the conceptual grounding, rejected
   as the naming* (§2.1).
2. **A single `Taint` return from `channels()`** rather than a `(path, run)`
   pair. Rejected: it cannot express the `dcFabricated` class, whose survivor
   path and run-wide omission differ (§2.2).
3. **Value-level taint** — a channel on `SymVal`, joined through every
   arithmetic/comparison combinator. Rejected: it requires negation-swap join
   rules (§2.1), there is no way to make "forgot the join" unspellable in a new
   combinator, and the codebase already solved the one case that needed
   per-value precision with the deferred placeholder pattern (§2.2). It would
   also be XL on its own, touching every `lower()` arm.
4. **A distinct "fatal/no-answer" lattice element** for Z3 errors and walker
   faults. Rejected as a distinct encoding of an observable identical to `⊤`
   (§3.1) — `dcNoAnswer` names the class without adding a lattice point.
5. **Reason-set carrying** — thread `seq[SymexErrorKind]` per path and classify
   at verdict time. Partly adopted: the run coordinate **is** derived this way
   (§2.2). The path coordinate cannot be, because `errors` carries no path
   association.
6. **Keeping the blanket vetoes, or folding them in blind.** Round 1 posed
   these as a fork (keep / fold / fold-plus-audit). All three are rejected as
   policy knobs on a representational gap — §2.5 removes the gap instead.
7. **Discharge instead of taint.** `beBudgetExhaustedAssumedBound`
   (`types.nim:1539`) and `ObligationDisposition`
   (`odDischargedStatic`/`odLive`, `types.nim:1245-1255`) show the codebase
   already has a pattern where a bound is proven rather than labelled. Some
   under-sites could be *eliminated* rather than classified — genuinely better
   where it applies, and out of scope here (§11).
8. **A side table for decline scope** (`prog.declineSites: Table[errorIndex,
   markerId]`) instead of a `DeclineScope` field. Rejected: index-coupled
   parallel structure, and the invariant stops being a total function of the
   record (§2.5).
9. **Restricting what may be cached** instead of widening the sentinel — cache
   only clean `sxUnsat`, stop caching `sxUnknown` and tainted `sxRaised`.
   Rejected: it trades away cross-run reuse on exactly the slow runs, to avoid a
   schema change the walker-version key already makes free (§7).
10. **A watchdog around replay** rather than the `dcFabricated` eligibility
    gate. Rejected: an in-process watchdog is not safely buildable under §1.5's
    no-non-top-level-catch constraint, and the gate excludes precisely the class
    §0.3 already argues is worthless (§4.2).
11. **Bare `notin` at consumption sites** versus named predicates
    (`blocksSat`/`blocksUnsat`/`clean`) over `Taint`. Kept bare in §2.3 because
    the verdict rule reads self-evidently, and `trusted()` (§8.1) gives
    consumers the one predicate they need; revisit if a third channel appears.

## §10 — Risks

| risk | mitigation |
|---|---|
| One site misclassified under-as-over mints a false `sxUnsat` — the S1 failure class | Per-funnel flips (§5): each classification slice flips only its own pins, so a misclassification surfaces in that slice's audit instead of in one big-bang landing; `classOf` starts conservative-`⊤` so an unaudited kind is never wrong in the unsound direction |
| Shipping the UNSAT rule without the `isTargetLabel` solve mints a false `sxUnsat` | They are one slice (S1c), and §0.1/§2.3 state why they cannot be separated |
| Deleting the closure veto before the HOF/budget declines carry path taint reintroduces the S1 class | S9 is gated on S7 (§2.5) |
| A tainted candidate halts the walk and loses a verdict the engine earns today | Candidates live in `w.candidates`, never `w.found`; `shouldStop` untouched; pinned by §4.1 family 1 with the tainted arm discovered first |
| Replay executes user code at verdict time — effects, divergence, Defects | `dcFabricated` eligibility gate + per-target-kind scope + `roInconclusive` default; contract change leads the migration note (§4.2, §8.2) |
| The measured payoff turns out to be ~0 after the build | S0b measures it **before** S1; §13.1 is the scheduled fork |
| The classification table goes stale as kinds are added | `classOf` is an exhaustive `case`; a new kind is a compile error |
| `soundness.runTaint` becomes a second source of truth beside `errors` | The **run** coordinate is derived from `errors` via `classOf()`, never written, and the correspondence is pinned (§2.2). **The path coordinate is genuinely independent data** — `errors` carries no path association, so nothing can re-derive it. Round 1's blanket "derived, never set independently" was half false and would have blessed a refactor that silently destroyed the path coordinate |
| A cache hit serves a result that cannot state its own soundness | Sentinel widened to carry `Soundness`; replay precedes persist (§7) |

## §11 — Non-goals

- Widening the modelled fragment. This changes how gaps are *reported*, not
  how many there are.
- In-band migration of the residual boundary-abort class (§3.3).
- Channel-aware call-summary caching (§2.4) — soundness first, reuse later.
- Eliminating under-sites by discharging their bounds (§9.7).
- Unifying `hoistCaseExpr` with M5's `nnkIfExpr` arm — same idiom, worth
  sharing, but it is a refactor-under-green and belongs in its own slice.

## §12 — Round-1 forks — **resolved 2026-09-20**

### §12.1 Does the RFC keep the SAT side? — **YES, full scope (Corey)**

The question was whether to drop the SAT half now that §0.3 shows its payoff
is near-empty and that what remains of it (the k-unroll exhausted survivor) is
a fabricated continuation, unsound to trust without in-engine witness replay —
against a UNSAT-only scope of roughly M that delivers the entire *measured*
payoff.

**Resolved: full scope.** Both halves ship. The replay substrate and the SAT
relaxation stay in the plan, the SAT rule is symmetric with the UNSAT one, and
§2.6's raise-routing recovery is in scope. The consequence to hold onto: replay
is a *verdict mechanism* (§4.2), so the engine gains a new execution step.

*Round 2 note: this resolution is re-opened by §13.1, not because the decision
was wrong, but because round 2 changed the facts it was made on.*

### §12.2 The two blanket vetoes — **resolved by redesign, not by choosing**

The fork as posed offered fold / keep / fold-plus-pin. Corey rejected the
framing and asked for the best-in-class design instead. All three options
argue about *how much to trust a backstop*; §2.5 records the answer, which is
that the backstop is standing in for a representational gap.

**Resolved:** delete both vetoes; unify Class-A and Class-B so every
site-anchored decline mints a marker node and is scoped by reach-taint;
classify signature-scoped declines through the ordinary class table; and make
an unplaceable `sevError` a loud walker-completeness defect under a structural
totality pin. Three parallel unknown-forcing mechanisms collapse to one lattice
plus one invariant.

*Round 2 amended the **implementation**, not the decision: a third anchor class
is required for totality, the scope needs a carrier on `SymexErrorInfo`, the
closure veto has a hard precondition, and the whole thing is three slices
(S7/S8/S9), not one.*

## §13 — Round-2 forks — **open**

### §13.1 Does §12.1 still stand, given round 2's cost? — **for Corey**

§12.1 chose full scope on the understanding that the SAT half cost a replay
substrate. Round 2 changed three facts underneath that decision:

- the SAT half's **entire live payoff** is the veto deletion and the
  raise-routing recovery (§0.3) — the replay-gated cases are the near-empty
  half;
- replay **executes the SUT at verdict time**, a contract change to `symexFind`
  with effects, divergence and Defect hazards (§4.2), and it must be discharged
  by both `runSymex` consumers;
- the plan is now **13 slices with six walker bumps** and six Windows CI gates
  at ~1–1.5h each.

The RFC as written keeps full scope. The question is whether to keep carrying
it as one RFC, or to land S0–S9 (the UNSAT channel plus veto deletion — which
delivers *both* measured payoffs) and spin S2/S10's replay machinery into a
successor RFC. **My read: keep it as one RFC.** The SAT and UNSAT rules are one
design and splitting them leaves `isTargetLabel` half-migrated across a release
boundary; and the replay slices are genuinely separable *within* the plan, so a
mid-flight decision to defer them costs nothing. But the size is now honestly
**L+ bordering XL**, and whether that fits a single RFC in your release cadence
is your call, not a design question.

**This fork is also conditional on S0b.** If the measured over-taint-only
population comes back near zero, the UNSAT half's value becomes purely
prospective (RFC-0011's), and the scope question should be re-answered with the
number in hand. S0b runs before any product code for exactly that reason.

### §13.2 Should `blocked_by = ["0001"]` become a soft edge? — **for Corey**

§1 documents every 0001 dependency as **landed** (B7-2 at `cac15e6`, the SND-1
machinery, the N36–N40 migration), and the Depends-on prose calls 0001 prior
art rather than pending work. The tracker derives readiness from this edge, and
RFC-0011 inherits the delay transitively through 0005. Either the edge should
drop to a soft "builds on", or the specific still-pending 0001 item that blocks
S0 should be named. I have **not** changed the frontmatter — 0001 round 6 is
live, and the tracker graph is yours to move.

### §13.3 `feTransparentResultUsed` / `feTransparentArgNotInert` — warning or companion-anchored? — **resolved 2026-09-26 (Corey): neither — a separate channel; landed in S8**

**Resolution.** Both options assumed the two are declines that need a place in
the decline lattice. They are not: nothing is approximated *because of* them —
the call's opaque fallback, whose walk-time `feOpaqueCallUnmodelled` taints
every path through it, is the whole soundness story. What they report is that
the *user's* annotation makes a promise the code does not keep. So they left
`SymexErrorKind`'s live set: the two members are tombstoned ("retained for
ordinal stability, never emitted"), and the report rides a separate
`AnnotationViolation` channel (`pragma`, `kind` = `avResultUsed` /
`avArgNotInert`, `callee`, `site` = `file:line:col`, `msg`) on
`SymexProgram` → `RawResult` → `SymexResult` (and `ConcolicCollectResult`),
populated on every verdict branch. It is error-severity in spirit and stays
loud, but it is **verdict-neutral by construction**: no `classOf`, no
`DeclineScope`, no taint, and it cannot trip the cap veto. Why this beats both
options: `sevWarning` would have made a wrong promise *quieter* than a real
decline; `dskCompanionAnchored` would have added a scope kind for two members
and still left a non-decline in the decline lattice, where it vetoed runs the
annotation did not affect.

**The verdict consequence (S8).** Before S8 the parse-time `sevError` tripped
`capForcedUnknown` for the whole run. Now a hit on a path that never passes
the over-claimed call is a clean `sxSat` (rule 1; pinned in
`tests/tsymex_rfc0005_s8_scope.nim` (d)); a hit *through* it stays a
`dcSubstituted` candidate (replay-ineligible), and a dead target behind it
stays `sxUnknown` (the walk record's run coordinate carries `scIncomplete`).

The original framing, kept for the record:


These two are `sevError` diagnostics *companion* to a walk-time mechanism that
already taints reaching paths via `feOpaqueCallUnmodelled` (§2.5). Under the
`DeclineScope` invariant they have no anchor of their own, so they land in
bucket 4 — a "walker-completeness defect" they are not. Demoting them to
`sevWarning` makes the invariant total and costs a little loudness on
over-claimed `{.symexTransparent.}` pragmas; adding a fourth
`dskCompanionAnchored` scope keeps them loud at the cost of a scope kind that
exists for two members. The trade is *how loudly you want an over-claimed
pragma surfaced*, which is a product judgment rather than a design one — I have
no basis to prefer either.

**As landed (S8aq, walker 187) — S8ai's remainder.** All four items are in
`checkCapped` and `seqRangeFacts`; none changes an existing verdict.

*1. Step 1c no longer needs step 1 to reach `zsUnsat`.* `checkCapped`'s step
1 (the capped one-shot solve) has exactly two non-SAT outcomes once the
early `zsSat` return is taken out of the domain: `zsUnsat` and `zsUnknown`
(cancelled, out of budget). Step 1b (the theory-free check) and step 1c
(the facts-based check) were both gated `if r1 == zsUnsat`, so a query
whose step 1 itself ran out of budget skipped both and fell straight to
step 3 with whatever budget remained — the facts were never tried, even
though both checks are sound independent of *why* step 1 did not return
SAT. Both gates are now `if r1 != zsSat`. Step 2 (which needs an actual
UNSAT to pull an unsat core from) is unchanged, still gated on
`r1 == zsUnsat` alone. `s[7] == ':' and rfind < 7`, and `':' in s and rfind
== -1` (on Z3 4.13.4), were the two cases S8ai flagged by name as not
pinned end to end for this reason; both are now `sxUnsat` under a budget
that cancels step 1.

*2. The dropped link — attempted, declined.* S8ai's link ("`L`
(`seq.last_indexof`) is at least every found `str.indexof(s, t, i)`") was
valid but neither Z3 could refute its negation within S8v's 1M-unit pin,
even at `i = 0`. S8aq tried two reformulations as a ground fact
`seqRangeFacts` could emit: first, a synthetic `str.indexof(s, t, L)` term
per `seq.last_indexof` occurrence (searching from `L` finds `L` exactly
when `L` is a real occurrence) folded into the existing `indexOfs`
collection so S8ai's own pairwise-ordering facts would apply to it
automatically; when `tsymex_rfc0005_s8v_termination.nim`'s own per-fact
validity pin caught that as `zsUnknown` (not just slow — symex-mingw's
Windows CI leg surfaced this on Z3 4.13.4, and it reproduces on Z3 5.1
too), a second, simpler form stating the same bound directly against an
existing `str.indexof(s, t, i)` term with no nested term at all. Raising
the validity pin's own check budget 50x (1M → 50M units) made the second
form hang past a 240s wall-clock bound on Z3 5.1 rather than return
either answer. Both forms are genuine theorems — a small-domain exhaustive
check over strings up to length 3 and integers -2..6 found no
counterexample to either, and Z3 never returned `zsSat` (a disproof) for
either, only `zsUnknown` (unable to decide) — so this is a tractability
limit of Z3's combined `str.indexof`/`seq.last_indexof` reasoning, not an
unsound fact. **Declined**: `seqRangeFacts` emits no fact linking the two
functions. See "different mechanisms" below for what this costs.

*3. `str.replace_all` is reachable, opt-in.* The walker's own call
(`iekStrReplaceAll`, `runtime_strings.nim`) was unconditionally gated off
(`when defined(z3WithSeqReplaceAll): ... else: raise
SymexZ3VersionMissingError`), and nelli's build never set the define — so
even on a Z3 new enough to support it, the real op was never tried.
nim-z3 already ships the FFI binding (`Z3_mk_seq_replace_all`, `{.optional,
prototype.}`) and its own `replaceAll` wrapper with an `Available()`
runtime guard; no nim-z3 change was needed, only turning the flag on. The
define is scoped to this slice's own test file
(`tests/tsymex_rfc0005_s8aq_remainder.nim.cfg`, the same per-test-file
mechanism `symexQueryStats`/`nelliVmAliasAudit` already use), so every
other suite is unaffected — the default public surface is unchanged. The
chokepoint (`runtime.nim`'s `lowerStrArm` catch) now also catches nim-z3's
own `Z3FeatureUnavailableError`, classified the same as the compile-time
gate being off (`seZ3VersionMissing`, `dcFreshSymbol`): a Z3 build with the
define on but the C symbol absent (below 4.16, e.g. 4.13.4) still degrades
honestly to a fresh stand-in instead of raising uncaught. A claim the real
op would refute is then replay-refuted against that stand-in
(`feReplayRefuted`, `sxUnknown`), never a false `sxSat`.

*4. A missed implied equality costs completeness, never soundness —
shown, not closed.* `seqRangeFacts`' union-find joins a term to another
when a `(= a b)` sits somewhere in the query (at any nesting) or when
`Z3_simplify` folds one to the other; it does not derive an equality the
query only IMPLIES through unrelated reasoning. `y ++ "x" == z ++ "x"`
implies `y == z` (concatenation is injective — ordinary word-equation
reasoning, decided fast by both Z3 5.1 and 4.13.4's own theory), but the
union-find only joins the two CONCATENATION terms (the asserted
equality's own two sides), never descending through `str.++` to join `y`
and `z` themselves. A query reaching `str.indexof(s, y, 0) > 200` and `not
str.contains(s, z)` this way is not decided by step 1c (`stepOneC` returns
`zsSat`/`zsUnknown`, never `zsUnsat`) — but the full, uncapped sequence
theory (steps 2/3, exactly where `checkCapped` falls through) still
decides it correctly. The miss costs step 1c a decision; it never costs
the walker a wrong one. Closing the union-find under arbitrary implied
equalities is not attempted here — it is an open-ended theorem-proving
problem, not a bounded one.

Pins: `tests/tsymex_rfc0005_s8aq_remainder.nim`.
- (1) End to end, both of S8ai's named cases are `sxUnsat` under a budget
  that cancels step 1 (`tight()`, `seqQueryRLimit = 2_000`), with no
  `"was not decided"` error.
- (2) The decline itself: step 1c never claims `zsUnsat` from the dropped
  link (no false positive), a found index at or before `L` stays `zsSat`,
  and a hand-built strict mutant of the (abandoned) fact still fails the
  general validity-check machinery (pinning that machinery, independent of
  `seqRangeFacts`'s own output). End to end, the query the dropped link
  would have shortcut lands a sound `sxUnknown` (never a false `sxSat`),
  with its companion still reachable.
- (3) End to end, under this suite's own `-d:z3WithSeqReplaceAll`: every
  occurrence is really replaced (`sxSat`, confirmed by replay, never
  `seZ3VersionMissing`) on a Z3 that has the symbol; the first-occurrence-
  only and no-occurrence-unchanged claims the real op forbids are
  `sxUnsat` there. On a Z3 without the symbol (4.13.4), all three degrade
  to the fresh-stand-in behaviour, with a content-specific claim the real
  op would refute landing `sxUnknown` + `feReplayRefuted`, never a wrong
  `sxSat`.
- (4) Step 1c misses the `y`/`z` word-equation case (never `zsUnsat`); the
  uncapped theory still decides it `zsUnsat`, at 1M units, on both Z3
  versions.
- The `>= 187` floor.

*Different mechanisms, reported and not fixed here.*
- **Item 2's gap is now permanent, not an anchor-availability question.**
  A query that reaches "`L` is at least every found `str.indexof(s, t,
  i)`" purely through `seqRangeFacts` falls through to steps 2/3 (still
  correctly decided, just not by step 1c's shortcut) regardless of what
  else is in the query — there is no anchor fact, stated or
  walker-produced, that would make step 1c decide it, because
  `seqRangeFacts` emits no fact joining the two functions at all (see item
  2 above). This is the same *class* of gap as item 4 above (step 1c needs
  a syntactic foothold it does not have), but here the foothold is
  provably unreachable by Z3 in this combination, not merely unbuilt.
- **Regex replace-all sits behind the same kind of gate, for a different
  reason.** nim-z3 declares `Z3_mk_seq_replace_re`/`Z3_mk_seq_replace_reAll`
  the same optional/prototype way as `Z3_mk_seq_replace_all`, gated behind
  `z3WithSeqReplaceRe`/`z3WithSeqReplaceReAll` in `regex.nim` — but per
  nim-z3's own comment there, Z3's solver returns `unknown` on
  `str.replace_re{,_all}` even for fully concrete inputs (unlike
  `str.replace_all`, which it decides). Enabling that define was not
  attempted: it would make the term constructible, not the operator any
  more decidable, and is out of this slice's scope (plain
  `str.replace_all` only).

**As landed (S8au, walker 194) — S8ag's remainder.** Suite
`tsymex_rfc0005_s8au_remainder` (35 tests; run time 14 s c / 17 s cpp on
Z3 5.1, 26 s on 4.13.4). Every verdict below was probed on both Z3
versions; the base column is 5ffc922.

- (1) *A local distinct value with no distinct param.* Already closed by
  S8ad (walker 175): a local `distinct int` returned, stored in a field or
  compared is modelled (`sxSat`/`sxUnsat`, no walker fault). Re-pinned. A
  `seq[distinct]` local is a scoped decline (`sxUnknown`,
  `seNestedSeqUnsupported`), never a fault.
- (2) *`start < 0 and y > 1 and start div y == start`.* Already closed by
  S8ad: `sxUnsat` on both versions (0.96M units on 5.1, 1.02M on 4.13.4;
  base 0.94M / 1.02M). With a `find` feeding `start`, the target is
  `sxUnsat` too (18.5M on 5.1 / 19.5M on 4.13.4; base 20.5M / 26.5M). The
  string-indexed variant stays `sxUnknown`, from a different query (the
  `start + 3` overflow raise path; below).
- (3) *Copy-in/copy-out aliasing through a global.* RED at base: a `var`
  or `addr` argument that the callee can also reach through a global (or a
  closure capture) was modelled as a disjoint copy, so a write through one
  name was invisible through the other -- a false `sxSat` on five dead
  labels (`hg_dead`, `hgr_dead`, `hgv_dead`, `hga_dead`, `hc_dead`). The
  parser now collects the callee's outer symbols (`calleeOuterSyms`) and,
  when an argument's cell is reachable from one (`outerReachesCell`),
  declines the call with `feUnsupportedOp` ("var/addr argument reachable
  through a global"). A call whose callee touches no such symbol is
  modelled as before.
- *`var ptr` params passed `addr x`.* Was a `heUnsafeCast` decline. A `var
  ptr T` formal whose body never rebinds the pointer is now treated like a
  `ptr T` formal (`ptrFormalStaysLocal`, `nnkHiddenAddr` in
  `ptrUsesStayLocal`/`substAddrAlias`), so `p[] = v` writes `x`. A rebind
  still declines.
- (4) *Index splits for non-literal needles, multi-char needles and
  rfind.* `find` with any needle and any start, and `rfind`, now lower to
  an `IndexSplit` (`splitNeedle` folds a computed needle to a literal when
  it can). The find axioms generalise S8ag's to a needle of length `n`:
  the no-earlier-match gap is `x ++ c[0 .. n-2]` (a match may overlap the
  gap's end), and the needle's own length replaces the literal 1. An
  `rfind` split states `s = pre ++ c ++ post`, `ix = len(pre)` and no match
  in `c[1 ..] ++ post`; the empty needle is `ix = len(s)` (rfind) or
  `ite(0 <= start <= len s, start, -1)` (find), probed against Nim and
  both Z3s. A computed needle carries the `len(c) == 0` case split. A
  literal needle of 2..16 characters also states `s[ix + k] == c[k]`
  (exact: implied by the word equation); Z3 4.13.4 does not relate a read
  past the first matched character to the word equation without it
  (`mf_dead` ran out at 20M units on either `c notin t` form; with it,
  24k). An rfind split and a find split of the same haystack and needle
  are linked by `find >= 0 -> rfind >= find` (`indexSplitLastLink`). RED at
  base, all `sxUnknown` with no split: the chained `"\r\n"` `mf_dead`
  (20.3M units, ~350 s) is now `sxUnsat` in 0.1M; the rfind/find
  `rf_dead` (20M) in 12k. S8aq's "declined" `foundExceedsLast`, base
  `sxUnknown` at 20M, is now `sxUnsat` in 0.04M (that test is updated).
  The axioms are checked by a 250-round differential per `c notin t` form
  against Nim's `find`/`rfind`, and three mutants (S8ag's 1-char gap on a
  longer needle, an rfind gap blind to an overlap, a computed needle
  without its empty case) are each caught.
- (5) *Chain facts.* All-pairs per haystack became consecutive pairs per
  haystack (each split chained only to the next reached split of its
  haystack), which is linear. Chain facts and hit units (5.1, base all
  pairs -> new): n36 3040 -> 424, 6.07M -> 4.93M; s1c 1520 -> 212, 3.32M
  -> 2.74M; b5_chained 40 -> 20, 0.60M -> 0.58M; q1_scanlift 14 -> 7,
  0.16M -> 0.15M. No verdict regressed in the 20-suite measurement set on
  either version; two improved (s8y 10 -> 9 unknowns on 5.1, s8aq 1 -> 0).
- (6) *`c notin t` per Z3 version.* Kept per version: the regex form on
  5.x, `not contains` on 4.x (`notInFormFor`). Hit units, with item 5 in
  place:

  | suite | 5.1 regex | 5.1 not-contains | 4.13.4 base | 4.13.4 regex | 4.13.4 not-contains |
  |---|---|---|---|---|---|
  | n36_raise_degrade | 4.93M | 82.5M (1 test fails) | 18.40M | 15.79M | 7.30M |
  | s1c_verdict | 2.74M | 27.49M | 10.10M | 10.95M | 3.60M |
  | b1_stringbacked | 0.48M | >= 24.6M (killed) | 0.26M | 0.26M | 3.13M |

  Not-contains costs b1 12x on 4.13.4 (no verdict change) and saves 2.2x
  on n36 and 3x on s1c; regex is not usable on 4.x for n36/s1c and
  not-contains is not usable on 5.1 at all. The choice is cached per
  process from `z3Version()`; `notInFormOverride` is the test hook.

*Term-creation order is part of the encoding.* Z3's cost depended on the
ORDER the split's terms were created in the context, and on terms created
but never asserted: logically identical query text cost 0.37M units with
S8ag's creation order and 7.7M with another (B1-1, 5.1). The split axioms
now create their terms in S8ag's order (regex built up front, the found arm
before its `ix = -1` disjunct, empty-needle and length terms created only
when used), which restored 365389 units, base's exact figure.
`seqLenCaps` marks a query holding an rfind split `lastIndex`, like the
`seq.last_indexof` term it stands for, so it keeps S8o's regime (no
capped verdict, one-shot step 3): without it `tsymex_rfc0005_s8o_termination`
(4) became a cap decline.

*Different mechanisms, reported and not fixed here.*
- **`seq[distinct]` locals decline.** `seNestedSeqUnsupported`, plus a
  stray `feGlobalReadUnmodelled` naming a `__sym_idx_N` temporary. Sound
  (`sxUnknown`), but the second error names a compiler temporary as if it
  were a global.
- **Overflow/range raise paths over string-derived indices.** A query on
  `start + 3` (or `s[i]` with no bound on `i`) over a capped string needs
  `len(s) <= high(int)` to refute the overflow branch; the walker states
  no such fact, so that raise query is `sxUnknown` (capped) while the
  target query is decided. Seen in item 2's string variant and in rf_dead
  without its `i < 100` assume.
- **S8aw's link work now covers native terms only.** The walker no longer
  emits `seq.last_indexof` or `str.indexof` for `rfind`/`find`; S8aw's
  `L` vs `indexof` link applies to those terms where they still arise
  (native `seqRangeFacts` inputs), and the walker path is covered by
  `indexSplitLastLink`.
- **Z3 context order sensitivity.** Above. Any later change to the split's
  term construction can move costs by an order of magnitude with no change
  in the asserted text; S8ag's B1-1 probe (0.37M) is the canary.

**As landed (S8ba, walker 200) — S8au's remainder.** Suite
`tsymex_rfc0005_s8ba_remainder` (32 tests; c and cpp, both Z3 versions;
timings below). The base is 9da3af6 (S8au); every item was RED there
first.

- (1) *A compiler temporary read as a global.* RED: a declined seq index
  or pop (`seq[(int, string)]`) left its result temporary (`__sym_idx_N`,
  `__sym_pop_N`) unbound, and its next read fell to the unbound-name arm,
  which records `feGlobalReadUnmodelled` naming the temporary. Every
  declining arm that owns a result now binds it: `declinedIndexEnv` at
  isIndex's two forks, `declinedPopEnv` at isSeqPop's two (the pop's
  element type is carried on `isSeqPop.spElemTy`), `declinedVariantEnv`
  at the variant construct's four. A parser temporary (`__sym_*`, which
  no Nim identifier can spell) read unbound is now
  `weInternalWalkerFault`, never a global. Audit of the global read and
  write sites: the walker classifies by `isGlobalEnvName` (the `__gl:`
  prefix) and the parser by `isModuleGlobal` (the symbol's owner); no
  other site confuses the two. `tsymex_rfc0005_s6a_budget`'s variant pin
  loses its companion `feGlobalReadUnmodelled`, and
  `tsymex_rfc0005_s8i_models` (4)'s kind write after a declined
  construction no longer declines on its own (`feUnsupportedOp`): it is
  the ordinary write on the bound free variant, and the construction's
  `seUnsupportedSetCharInterop` keeps the run `sxUnknown`.
- (2) *`seq[distinct]` locals.* RED: `seNestedSeqUnsupported` (and the
  stray global of item 1). The cell type of a seq is its element type
  with every distinct layer stripped (`seqCellTy`): the backing array
  holds the base sort, a store unwraps (`ejectBase`), and a read
  re-boxes (`reboxSeqCell`). Literal, `.add`, index read and write,
  `pop`, `for` and the HOF map/filter all route through it. A
  `seq[distinct]` PARAMETER stays a scoped `feUnsupportedWitnessType`
  (its witness needs a distinct-typed renderer). A user `==` on the
  element is never replaced by base equality: `x in s`, `s.find(x)` and
  `s == t` over a `Mod10` element are pinned never `sxUnsat` (they
  decline or go through the user routine), and `s8c_resolution`'s seq pin
  now declines as `feUnsupportedOp` instead of the fragment's kind.
  **Soundness bug found:** `iekSeqAdd` had its own int64/bool store
  dispatch, which stored an `svInt` value (a `range` parameter under the
  default `isOptimised` semantics) as the constant 0, so `var s:
  seq[int]; s.add(x); s[0] == 7` with `x: range[0..10]` was a false
  `sxUnsat`; and `.add` on `seq[int32]`, `seq[byte]`, `seq[string]` or
  `seq[float]` was `weInternalWalkerFault`. It now lowers the value at the
  element's width and stores through `storeSeqElem`. Five round-6 pins
  that used the `seq[byte]` width decline as their evidence that a
  receiver stayed array-modelled (b1 B1-4, b7r B7R-7, lows N25-2, r4
  W2a/W2b) now reach their labels and pin the absence of the
  kind-mismatch decline instead.
- (3) *`len <= high(int)`.* Step 1c asserts, beside `seqRangeFacts`,
  `l <= high(int64)` for every seq / string length its caps name
  (`seqLenCaps` returns them as `lens`; `nimLenFacts`). Built on the 1c
  path only: building them for every query, in `seqLenCaps`, took B1-1
  from 187199 units to 3555731 (the context-cost effect of S8o). RED at
  base, `sxUnknown` ("no model ... 128 elements"): S8au's item-2 string
  variant `t` is now `sxUnsat` (0.98M units; its `hit` `sxSat`, 0.86M),
  and `rf_dead` without its `i < 100` bound `sxUnsat` (21k); both also
  under `isExact` (the bit-vector encoding).
- (4) *By reference through the heap cell.* RED: S8au's five dead labels
  were `sxUnknown` (its decline). A heap `var` actual, or an `addr` one,
  that a global or capture of the callee also reaches
  (`outerReachesCell`) is now passed by reference: the callee is
  specialised (`byRefSub`, `ensureProcRegistered(byRef)`), its formal's
  uses spelled as the caller's lvalue (`f[]` / the hidden deref of a `var`
  formal; a bare `var` formal passed on is `nnkHiddenAddr(lvalue)`, a
  bare `ptr` formal `addr lvalue`), and the lvalue's last ref is a
  hidden parameter in the formal's slot. Its symbol is a copy of the
  caller's (`markByRef`: same symbol and type, a sentinel line info) that
  `strVal` reads as `__byref_<N>`, so every name lookup in the parser
  sees it by construction. The caller passes the ref evaluated at the
  call; there is no write-back and no guard root for that argument, so
  the callee's writes through the formal and through the global land on
  one heap cell in its order, and a callee that rebinds the global does
  not move the address (`hr`). The specialisation is keyed by formal,
  base type (module, line, column; no path) and field path, so a
  recursive call reaches its own key while it is parsed. All five dead
  labels are `sxUnsat`, their live labels `sxSat`; also pinned: a global
  root (`hd`), a rebind in the callee (`hr`), a ref behind two refs
  (`o.inner.x`, `hn`) and a ref in a value field (`t.b.x`, `ht`). A shape
  it cannot spell (a ref reached through an index, a generic callee, a
  formal with a use it cannot rewrite) keeps S8au's decline (pinned:
  `a[0].x`).
- (5) *Split term order.* The axioms of a split are built once, by the
  first query that reaches it: newly reached splits in lowering order,
  each in `indexSplitAxioms`' fixed term order, before any chain or link
  fact, and reused after (`IndexSplit.built`; pinned on a lowered split).
  The query text and its term order are those of S8au. Building them
  eagerly at lowering was measured and rejected: it puts the axioms of
  splits no query reaches into the context, and on Z3 5.1 the target
  units grew 22.9M vs 5.0M on `r6_n36_raise_degrade`, 12.2M vs 2.3M on
  `s1c_verdict` and 10.9M vs 0.95M on `s8au_remainder`, and one more S8ag
  (5) hit became a slow SAT. Canary: B1-1 has a unit ceiling per linked
  Z3: <= 1M on 5.x (187199 in the suite, 380570 alone) and <= 3M on 4.x
  (2293304; the base spends the same 2.29M on 4.13.4).

*Measurements* (target units, `-d:symexQueryStats` totals):

| probe | base 9da3af6 | S8ba |
|---|---|---|
| B1-1, 5.1 / 4.13.4 | 380570 / 2293440 (alone) | 380570 / 2293440 (alone) |
| S8au item-2 string `t`, 5.1 | `sxUnknown` | `sxUnsat`, 0.98M (`hit` `sxSat`, 0.86M) |
| `rf_dead` without `i < 100`, 5.1 | `sxUnknown` | `sxUnsat`, 21k |
| `nimLenFacts` in `seqLenCaps` (rejected), B1-1 5.1 | — | 3555731 |

Split axioms built eagerly at lowering (rejected) against built once at
first reach (landed), suite totals on Z3 5.1:

| suite | eager | first reach |
|---|---|---|
| `r6_n36_raise_degrade` | 22935434 | 4962163 |
| `s1c_verdict` | 12221318 | 2291541 |
| `s8au_remainder` | 10944767 | 952407 |
| `r6_b1_stringbacked` | 437902 | 437902 |

*Suites* (17df7ea plus the per-version B1-1 ceiling; `ok/failed`; Z3
5.1 c, Z3 4.13.4 c). Every suite below passes at the base on both
versions, except where its pin moved by this slice:

| suite | 5.1 | 4.13.4 |
|---|---|---|
| `rfc0005_s8ba_remainder` (new; cpp 5.1 32/0) | 32/0 | 32/0 |
| `rfc0005_s8au_remainder` (re-pinned) | 35/0 | 35/0 |
| `rfc0005_s8ag_indexsplit` | 15/0 | 15/0 |
| `rfc0005_s8y_budget_decline` | 8/0 | 8/0 |
| `rfc0005_s1c_verdict` | 24/0 | 24/0 |
| `r6_n36_raise_degrade` | 8/0 | 8/0 |
| `rfc0005_s8ai_semantic` | 25/0 | 25/0 |
| `rfc0005_s8aq_remainder` | 13/0 | 13/0 |
| `rfc0005_s8an_remainder` | 25/0 | 25/0 |
| `rfc0005_s8o_termination` | 14/0 | 14/0 |
| `phase16_m3_rfind` | 6/0 | 6/0 |
| `phase15_CR2_cachekey` (200) | 6/0 | 6/0 |
| `rfc0005_s6a_budget` (re-pinned) | 31/0 | 31/0 |
| `rfc0005_s8c_resolution` (re-pinned) | 25/0 | 25/0 |
| `r6_n27_placeholder_read_audit` (84 + 3) | 4/0 | 4/0 |
| `r6_b1_stringbacked` (re-pinned) | 7/0 | 7/0 |
| `r6_b7r_bytescan` (re-pinned) | 26/0 | 26/0 |
| `r6_lows_collectors` (re-pinned) | 5/0 | 5/0 |
| `r6_r4_collector_scoping` (re-pinned) | 7/0 | 7/0 |
| `rfc0005_s8i_models` (re-pinned; caught by symex-mingw, outside the first list) | 39/0 | 39/0 |
| 27 more feGlobal / source-scanning suites (`163rev`, `s1_lattice`, `s1b`, `s5_str`, `s6b`, `s8ab`, `s8b`, `s8l`, `s8n`, `s8p`, `s8z`, the A2a / N2 / r11 / pairing / n36 class audits, `inv_structured_kinds`, `b7r2`, `bug2`, `n13`, `lows_declines`, `n27_hof`, `n37`, `r1`, `r6_emit`, `tot1`) | all 0 failed | all 0 failed |

The new suite runs in 53 s (5.1) and 54 s (4.13.4) with its compile.

*Different mechanisms, reported and not fixed here.*
- **`s[i] == 'a'` with `i + 1 > s.len` over a capped string.** `i >= 0
  and i < s.len and s[i] == 'a' and i + 1 > s.len` runs about 41M units
  to `sxUnknown` in both encodings (60-160 s; 96 s at base). Item 3
  removed its overflow-raise error; what is left is the label query
  itself, slow from the Int/BV mixing of `str.at` at a symbolic index.
- **A `seq[distinct]` parameter.** Still a scoped
  `feUnsupportedWitnessType` (a witness renderer for distinct-typed
  elements is its own work).
- **The heap-depth budget.** `hr_dead` and both `hn` labels make more
  than `maxHeapDepth = 8` dereferences on one path and decline as
  `heDepthExhausted` at the default; the suite raises the budget to pin
  the verdict. The budget counts every dereference of a path, not the
  depth of a chain.
- **By reference needs a symbol or a field for the ref.** A ref reached
  through an index (`a[i].x`) or a call keeps S8au's `feUnsupportedOp`.

**As landed (S8bd, walker 204) — S8ba's remainder.** Suite
`tsymex_rfc0005_s8bd_remainder` (23 tests; c both Z3 versions, cpp
5.1). The base is 7af8468 (S8ba); every item was RED there first (item
2's witness did not compile at all: the witness tuple held `int` where
`seq[Meters]` was expected).

- (1) *A bit-vector string index against the length.* RED on both Z3
  versions and both encodings: `i >= 0 and i < s.len and s[i] == 'a' and
  i + 1 > s.len` was `sxUnknown` (`beSolverUndef`) after 41-44M units.
  The cause is not `str.at`: without the character read the cost was the
  same, and with `i > s.len` (no `+ 1`) it was 170k. `i` is a bit-vector
  (its `i + 1` may overflow) that meets `s.len` through two Int views,
  `bv2int(i)` and `bv2int(i + 1)`, and Z3 relates them only by
  bit-blasting the conversion. The label query replayed offline from its
  SMT-LIB text decides (0.77M units on 5.1, 2.77M on 4.13.4), but it
  ran past the whole budget inside the walker's context (S8o's
  context-state effect). `bvOffsetLinks` states, beside every
  `checkCapped` step's query, the exact two's-complement link between
  `bv2int(x +- c)` and `bv2int(x)` (`c` a numeral, unsigned or Z3's
  one-argument signed view), only when both views are in the query.
  Each link is a theorem: the suite checks it against Z3's own `bv2int`
  on a width-8 grid (360 cases: both signs, the wrap at both ends,
  `x + c`, `c + x`, `x - c`). S8aj's rejected general link brought in an
  Int view the query did not hold (6.6M to 31.6M); this one never does
  (pinned: a lone `bv2int(x + 1)` is not linked).
- (2) *A `seq[distinct]` parameter.* `isRenderableSeqElemTy` accepts a
  distinct chain over a renderable int or float (not an enum);
  `emitTyAndReader` reads the cells as the base seq (`seqCellTy`) and
  converts each element back through the chain (`Km(Meters(int(x)))`);
  `witnessFidelity` is faithful in lockstep; `extractSeqElements`
  dispatches on the cell type. `seq[Meters]`, `seq[Grams]` (int32),
  `seq[Secs]` (float) and `seq[Km]` (a distinct of a distinct) are
  `sxSat` with witnesses that replay `roConfirmed`; S8ba's decline pin
  is now `sxSat`.
- (3) *The heap-depth budget.* The count was not needed: the walk of a
  path is finite without it (`maxLoopUnwind` and `maxCallDepth` bound
  every loop and recursion; 0 is not unlimited for either), and the
  budget's own doc and name are a depth. The walker counted every
  dereference of a path (`Path.heapDepth`, never decremented), so a
  straight-line SUT reading one object's field ten times declined at the
  default 8. `maxHeapDepth` now bounds the chain depth of the
  dereference: one more than `heapChainDepth` of the dereferenced ref
  (a read out of a heap cell keyed by a `Ref_T` sort is one more than
  its ref; an `ite` is its deeper side; a read out of a seq's or array's
  backing is its container's; anything else is a root). The check runs
  once the ref is lowered. The count is kept as a hard cap,
  `heapDerefsPerPathCap = 4096`, which bounds the heap terms one query
  can hold. Each decline names its budget (`maxHeapDepth`,
  `heapDerefsPerPathCap`). RED: `mr`/`mr_dead`, `hr_dead`, `hn`,
  `hn_dead` and a seven-link chain were `heDepthExhausted` at the
  default; they decide now, and a nine-link chain (default) or a
  seven-link chain under `maxHeapDepth: 3` still declines and names it.
  R10's exact thresholds (a two-hop chain decides at 3 and declines at
  2), R11b's depth-3 walk and every heap suite are unchanged. S8ba's
  `maxHeapDepth: 32` overrides are gone.
- (4) *By reference: an element, a call result, a generic callee.* RED:
  S8au's `feUnsupportedOp` (`a[0].x` and `s[nextI()].x` through a
  global, `getB().x` without a root, `setGen(p.x, k)`); `a[gI].x` with a
  callee that moves `gI` also hit `heDepthExhausted`. `byRefSub` takes
  a ref that is an element (`a[i]`) or a user call's result, and a
  generic callee. The ref is evaluated once, at its argument's
  position, before the call; a by-reference actual is no longer lowered
  a second time as an lvalue (S8ba lowered both, harmless for a symbol,
  a second call for `getB()`). The callee's parameter is named by a
  mark: an element's ref by a childless copy of its node (it keeps the
  type and names nothing of the caller's; `parseExpr` and `lvalueRoot`
  read it as the parameter), a call's by the callee's own `result`
  symbol (same type). A call result is rooted at the call
  (`byRefRoot`). A generic callee is specialised after monomorphisation,
  under its instantiation's key extended by the by-reference parts, and
  counts against `maxInstantiationsPerProc`. Pinned: `he`, `hi` (the
  index read once, before the callee moves it), `hic` (the index call
  made once), `hcr` (the call made once), `hgen`, and two instantiations
  of one generic (`hgen2`, int16 and int).
  **Soundness bug found:** a generic instance's body uses its own
  parameter symbols, not those of its formal list. The specialisation
  first matched nothing and silently dropped the formal's write (caught
  by `hgen2_dead` before it landed). The same mismatch was live in
  S8an's `ptrFormalStaysLocal`: it scanned the instance's body for the
  formal list's symbol, found no use, and modelled an `addr` argument a
  generic callee stores in a global as a cell for the call only, a
  false `sxSat` (`ge_dead`, RED `sxSat` at the base). `formalInBody`
  resolves the body's symbol for both (by name among the body's
  parameter symbols, outside nested routines; ambiguous is a decline).

*Measurements* (target units, `-d:symexQueryStats` totals; base 7af8468):

| probe | base 5.1 | S8bd 5.1 | base 4.13.4 | S8bd 4.13.4 |
|---|---|---|---|---|
| `s[i] == 'a'`, `i + 1 > s.len` (dead) | `sxUnknown` 41.3M | `sxUnsat` 201k | `sxUnknown` 43.6M | `sxUnsat` 321k |
| the same, `i + 1 == s.len` (live) | `sxSat` 430k | `sxSat` 373k | — | `sxSat` 457k |
| without the character read (dead) | `sxUnknown` 40.4M | `sxUnsat` 227k | `sxUnknown` 43.3M | `sxUnsat` 801k |
| `let j = i + 1` first | `sxRaised` 40.4M | `sxRaised` 319k | — | `sxRaised` 621k |
| `s[i - 1]`, `i - 1 >= s.len` (dead) | `sxUnknown` | `sxUnsat` 438k | `sxUnknown` 43.7M | `sxUnsat` 1.48M |
| dead, `isExact` | `sxUnknown` 41.3M | `sxUnsat` 200k | — | `sxUnsat` 321k |

Offline replay of the dead label's query (SMT-LIB text, fresh context):
as dumped 774639 / 2773337 units (5.1 / 4.13.4); with the exact
unsigned link 2802 / 3990.

*Suites* (5.1 c and 4.13.4 c, `ok/failed`; identical on both versions):

| suite | 5.1 | 4.13.4 |
|---|---|---|
| `rfc0005_s8bd_remainder` (new; cpp 5.1 23/0) | 23/0 | 23/0 |
| `rfc0005_s8ba_remainder` (re-pinned) | 32/0 | 32/0 |
| `rfc0005_s8au_remainder` | 35/0 | 35/0 |
| `rfc0005_s8i_models` | 39/0 | 39/0 |
| `rfc0005_s8ag_indexsplit` | 15/0 | 15/0 |
| `rfc0005_s1c_verdict` | 24/0 | 24/0 |
| `r6_n36_raise_degrade` | 8/0 | 8/0 |
| `rfc0005_s8an_remainder` | 25/0 | 25/0 |
| `rfc0005_s8aj_remainder` | 21/0 | 21/0 |
| `rfc0005_s8ad_remainder` | 13/0 | 13/0 |
| `phase15_CR2_cachekey` (204) | 6/0 | 6/0 |
| heap: `phase15_r9_recursive`, `r10_budget`, `r11b_smoke`, `R1a_ir`, `z3_infra`, `h_witness`, `h_verification`, `configdefaults`, `163rev`, `s0_exhibit`, `s1_lattice`, `s6b_ops`, `s8aa`, `s8ac`, `s8ap` | all 0 failed | all 0 failed |
| feGlobal / source-scanning: `s1b`, `s4_alloc`, `s5_str`, `s6a`, `s7_closure`, `s8ab`, `s8b`, `s8l`, `s8m`, `s8n`, `s8p`, `s8z`, `s8_scope`, `s8x`, `s10_replay`, the A2a / N2 / r11 / pairing / n27 / n36 audits | all 0 failed | all 0 failed |

The new suite runs in 6.4 s without its compile; 69 s (5.1) and 74 s
(4.13.4) with it, on a host at load 14-22.

*Different mechanisms, reported and not fixed here.*
- **Two `var` heap actuals through different refs to one cell.**
  `let q = p; setBoth(p.x, q.x)` with `setBoth(a, b: var int) = b = 2;
  a = 1` is a false `sxSat` for `p.x != 1` (Nim gives 1; the
  write-backs run in argument order and leave 2). `varActualMayAlias`
  asks whether another argument's TYPE can hold a ref to the cell; the
  other actual is `var int`, so it cannot, and the two roots are
  different symbols. Present at the base (S8ac / S8an), not reached by
  S8bd (no global or capture, so no by-reference path).
- **`geDistinctBijectivitySkipped` on a distinct of a distinct over an
  int.** `seq[Km]` (`Km = distinct Meters`, `Meters = distinct int`)
  carries the hint "over non-decidable base itDistinct (FP/String)": the
  round-trip axiom is skipped for a chain whose base is decidable. A
  hint only (the verdict and witness are right here); it under-uses a
  decidable axiom.
- **A by-reference ref with no symbol, element or call form.** A ref
  reached through a pointer dereference (`pb[].x`, `pb: ptr Box`), a
  conversion or a cast is refused by `byRefSub` and falls back to S8au's
  `feUnsupportedOp` (by the code path; not pinned).

**As landed (S8bf, walker 206 provisional; S8be holds 205) — S8bd's
soundness finding.** Suite `tsymex_rfc0005_s8bf_alias` (13 tests; c on
both Z3 versions, cpp 5.1; the binary runs in ~2 s). The base is 09f6804
(S8bd).

- *The bug.* `let q = p; setBoth(p.x, q.x)` with `setBoth(a, b: var
  int) = b = 2; a = 1` was a false `sxSat` for `p.x != 1`: the two
  copy-in/copy-out write-backs ran in argument order, not the callee's
  write order. `varActualMayAlias` asked whether another argument names
  the lvalue's root or has a TYPE that can hold a ref to the cell; `q.x`
  is a different symbol of type `var int`. RED at the base, every dead
  label `sxSat` and every reachable twin `sxUnsat`: a `let` copy, a
  `let`/`var` chain, a ref in a tuple (`t[0].x`), a ref through a field of
  another ref (`o.inner.x`), two parameter refs (`p == q`), a `let` copy
  of a parameter, a `var` formal forwarded to a second callee, two `addr`
  actuals (`ptr int` formals) and a mixed `var` / `addr` pair.
- *The check.* `heapCellsMayMeet` asks whether two heap lvalues may be one
  cell whatever their roots: the objects their last dereferences address
  may be one (same type, or either side takes part in inheritance) and
  one field path from there is a prefix of the other (`p.x`/`q.x`,
  `p.v`/`q.v.n`; an index, a tuple's included, matches any index). A
  `ptr` dereference on either side meets any heap lvalue. Root identity
  plays no part. `varActualMayAlias` and `addrActualMayAlias` consult it
  for every other actual (`actualCell`: a `var` or `addr` actual's
  lvalue, or a non-scalar value Nim may pass by pointer).
- *The model.* `userCallStmt` gives each `var` / `addr` heap actual its
  `peers`, the others whose cell may be its own, and passes every one of
  them by reference (S8ba's `byRefSub`), each excused from the alias
  check by the others: the callee's writes land on the heap in its order
  and the heap decides whether the refs are one (the parameter pair is
  `sxSat` both ways). An actual that cannot be passed so (`pb[].x`,
  `pb: ptr Box`) takes the write-back, which declines `feUnsupportedOp`
  naming it (pinned). Precision gained: one ref named twice
  (`setBoth(p.x, p.x)`) and two elements of one array of refs were
  declines and now decide. Two fields (`p.x`, `q.y`) and two fresh
  allocations stay on the exact write-back path (pinned).
- *Audit.* Every caller of `varActualMayAlias` (the by-reference gate,
  the plain-variable write-back, the heap write-back) and of
  `addrActualMayAlias` (the by-reference gate, the cell model) now sees
  the cell. `outerReachesCell` is type-based (no root identity). The
  walker's `cGuardRoots` compares root names, which is exact for a
  variable; a heap cell reached through another global is
  `outerReachesCell`'s. A plain variable and a `ptr` to it (`let pp = addr
  x; setBoth(pp[], x)`) already declined (the alias is substituted at
  parse). A large object passed by value beside a `var` of the same cell
  (`setRead(p.v, q.v)`, which Nim passes by pointer) now declines.

*Suites* (`ok/failed`, c; identical on 5.1 and 4.13.4): `s8bf_alias`
13/0 (cpp 13/0), `s8bd_remainder` 23/0, `s8ba_remainder` 32/0,
`s8au_remainder` 35/0, `s8an_remainder` 25/0, `s8ac_remainder` 19/0,
`s8i_models` 39/0, `s8_scope` 28/0, `phase15_CR2_cachekey` (206) 6/0,
`phase14_var_param` 1/0, `phase14_var_param_downstream` 2/0,
`163_opaque_transparent` 15/0, `163rev_assign_scope` 10/0,
`163rev_assign_sites` 33/0, `163rev_degrade_classification` 8/0,
`163rev_inert_argfork` 9/0, `163rev_inert_exclusions` 15/0,
`163rev_transparent_guard` 9/0, `163rev_transparent_result` 4/0,
`phase12_witnesses` 10/0, `r5_bv32_width` 8/0, `r6_lows_blockparse`
6/0, `rectify_effects` 5/0, `s2_replay` 15/0, `s6a_budget` 31/0. (S8as
has no suite: its row is pending.)

*Different mechanisms, reported and not fixed here.*
- **SOUNDNESS: a call through a proc-valued variable drops its `var`
  writes.** `let f = setBoth; var x = k; var y = k; f(x, y); if x != 1:
  symexTarget("d")` is `sxSat` with no error (Nim gives `x == 1`); the
  same with a heap actual (`f(p.x, y)`). The closure-call arm
  (`mkClosureCall`) lowers the arguments by value and has no write-back
  at all; not an aliasing question.
- **SOUNDNESS: a `ptr` parameter never addresses a ref object's field.**
  `proc s(pi: ptr int; q: Box) = q.x = 1; pi[] = 2; if q.x == 2:
  symexTarget("pd")` is `sxUnsat` (hint `hePtrFamily` only); Nim reaches
  it with `pi = addr q.x`. The heap keeps `ptr int` cells apart from
  `Box.x` fields, with or without a call (`setBoth(pi[], q.x)` is the same
  `sxUnsat`, at the base by write-back and now by reference).
- **SOUNDNESS (to confirm): an inheritance ref conversion is
  ill-sorted.** `Base(d) == b` (`d: Derived`, `b: Base`) is
  `weInternalWalkerFault` ("Z3 sort mismatch at equality"), and with
  `setBoth(Base(d).x, b.x)` the dead label reports `sxRaised` beside the
  faults. Identical at the base.
- **PRECISION: a ref reached through a pointer dereference.** `pb[].x`
  still cannot be passed by reference (S8bd's reported item), so a pair
  holding it declines.

**As landed (S8bh, walker 208 provisional) — S8bf's remainder.** Suite
`tsymex_rfc0005_s8bh_remainder` (32 tests; c on both Z3 versions, cpp
5.1; the binary runs in ~5 s). The base is 77e57a7 (S8bf). S8ax is not
in the base: item 2 builds on S8an's `addr` cells, not on S8ax's address
cells.

- *Item 1: a call through a proc value drops its `var` writes.* `let f =
  setBoth; f(x, y); if x != 1` was a false `sxSat`, and so was every heap
  form (`f(p.x, y)`, S8bf's peers `f(p.x, q.x)`); an `addr` actual
  declined. The closure-call arm now applies the call's effects as a
  direct call does: a `var` formal's exit value, merged over the body's
  value exits, is written to its actual by name (`closureVarOuts`); a
  raise carries the value where the body raised; a non-variable lvalue
  goes through a temporary written back on return and on raise (S8ac's
  shape); an `addr` actual is an S8an cell. One location passed twice
  runs a body specialised to it (`lambdaAliasBodies`); two heap peers
  branch on their refs' equality. It declines (`feUnsupportedOp` /
  `ceCaptureByRefUnmodelled`, naming S8bh) when the body can reach an
  actual's location outside its formals or an `addr` cell's pointer may
  escape. An unknown target havocs its `var` actuals and the heap. Audit,
  all pinned: a proc-valued variable, a lambda, a generic callee's proc
  parameter, a proc passed to a callee, a call in an expression and
  under a branch, a write before a raise; a proc field in an object and
  a method call decline. The six new closure-sink sites are counted in
  the S7 source pins (`tsymex_rfc0005_s7_closure`, 13 -> 19; the
  two-kind site is split so each line names its kind).
- *Item 2: a `ptr` of unknown origin addresses only its own cells.* `q.x
  = 1; pi[] = 2; if q.x == 2` was a false `sxUnsat`, likewise a global
  (`addr g`), a `var` parameter (`addr v`), a `ptr string` against a
  string field, and the write in a callee. Each address of the pointer
  sort now has a target, chosen by the free input array `<T>__@ptrsel`:
  0 is the own cell; a field family's code names that family at the
  object `<T>__@ptrobj__<K>[P]` (a free input array too); a variable's
  code names a global or a root `var` parameter. Both arrays are
  functions of the address, so every deref of one pointer, and of every
  pointer equal to it, agrees on its target. A read is the `ite` chain
  over the candidates; a write stores into each under its guard (and into
  the own cell). The candidates are the field families the path has
  materialised (one it has not touched reads its free input cell, so a
  write it missed stays possible), the env's globals and the SUT's `var`
  parameters. A `new` (so an `addr` cell) stores `sel = 0` at its fresh
  address, and a pointer the walk allocated has no candidates; a target
  object predates every allocation (`ptrPreKey`, read by
  `assertFreshness`). Scoped declines (`feUnsupportedOp`, naming S8bh),
  where no finite candidate set exists in this model: an element of a
  seq/table/set held in a heap cell; a part of a by-value aggregate
  global or `var` parameter; a root `var` parameter while a callee runs;
  a callee's or a closure's `var` formal (copied in and out). The
  snapshot aims a pointer whose input target is a field of a cell it
  holds at that field (`aliasRef = "&<cell>.<field>"`), and the typed
  witness hands the pointer the field's address: the alias witness
  replays `roConfirmed` (pinned). Controls pinned `sxUnsat`: an `int`
  pointer against a `bool` field, an object the SUT allocates, a local.
- *Item 3: a ref converted along its inheritance chain.* Every type of a
  hierarchy keyed its own Ref sort and field heaps, and a derived type's
  IR held only its declared fields: `Base(d) == b` was ill-sorted
  (`weInternalWalkerFault`), `setBoth(Base(d).x, b.x)` was `sxRaised`, a
  `Base` parameter never aliased a `Derived` one (a false `sxUnsat`),
  `Derived()` left inherited fields unzeroed (a false `sxSat`), and a
  down-conversion never raised. A hierarchy now names one address space:
  the sort keys on the root (`inheritChain[0]`), a field's heap on the
  type that declares it (`ownedFieldIds`), and a derived type carries
  its ancestors' fields. An up-conversion is the operand. A
  down-conversion checks a non-nil ref's run-type tag, stored per depth
  at allocation with a sentinel one level below (`inheritTagKey`), and
  raises `ObjectConversionDefect`; a parameter's tags are free, so its
  conversion may go either way. A converted base passes by reference to
  a `var` formal.

*Suites* (`ok/failed`, c; 5.1 / 4.13.4 where they differ): `h_witness` 11/0, `phase15_CR2_cachekey` 6/0, `s7_closure` 37/0, `s8_scope` 28/0, `s8ac_remainder` 19/0, `s8an_remainder` 25/0, `s8au_remainder` 35/0, `s8bd_remainder` 23/0, `s8ba_remainder` 32/0, `s8bf_alias` 13/0, `s8bh_remainder` 32/0, `s8i_models` 39/0, `s9_vetoes` 19/0, `s8ab_letaudit` 28/0 (see below). With the rest of the closure / HOF / ptr / inheritance / witness suites (`command grep -l` over `ptr `, `closure`, `proc(`, `of RootObj`, `heapSnapshot`) and every `163`/`163rev` suite: 128 suites; the 127 besides `s8ab_letaudit` hold 1832 checks, all OK, identical on 5.1 and 4.13.4 at 3422595; cpp 5.1 `s8bh_remainder` 32/0. `s8ab_letaudit` did not compile at 3422595 (below) and is 28/0 on both versions at 657f37a; `s8x_vm_alias` 7/0 there.

*Windows:* at 3422595 all three legs were red on one suite, `tsymex_rfc0005_s8ab_letaudit` (compile error in `vm_alias_guard`, fuzzer-mingw 37058311018, symex-mingw 37058311067, fuzzer-msvc 37058311020). Fixed in 657f37a: `bodyMutatesRoot` read `strVal` off a callee name node that S8bh's parser code spells as neither an identifier nor a symbol (now `calleeName`, total), and the walk then flagged a real VM let-alias in `closureCallIR` (now a `var` copy). At 657f37a all green: fuzzer-mingw 37063867369, symex-mingw 37063867374, fuzzer-msvc 37063867415.

*Different mechanisms, reported and not fixed here.*
- **PRECISION: a ptr alias witness depends on parameter order.** The
  typed witness builds positions in parameter order, so a pointer whose
  target object's parameter comes after it (`s(pi: ptr int; q: Q)`)
  keeps its own cell and the replay refutes the (sound) `sxSat`.
- **PRECISION: a ptr aimed at a global or a `var` parameter has no
  renderable witness.** The snapshot holds no cell for either; the
  `sxSat` is sound and its replay refutes.
- **PRECISION: a callee's or closure's `var` formal declines any ptr
  deref of a type it may hold**, also when its actual is a local no
  outside pointer can address (copy-in/copy-out has no location for it).
- **PRECISION: a ptr into a seq/table/set element held in a heap cell, or
  into a by-value aggregate global or `var` parameter, declines.**
- **PRECISION: an always-raising void closure reports
  `ceClosureBodyDiverged`.**
- **PRECISION: a proc field in an object and a method call decline**
  (item 1's audit); the unknown-target havoc does not reach globals, the
  path's taint covers it.
- **PRECISION: the `of` operator is unsupported**, and a general `nil`
  literal (`let b: Base = nil`) does not parse (both pre-existing).
- **PRECISION: generic, `{.inheritable.}` and case-object hierarchies
  keep per-type keying**, so a conversion among them still declines or
  stays per-type.
- **PRECISION: a parameter's run-type tags are free**, unconstrained by
  its static type, so alias states may be over-approximated.

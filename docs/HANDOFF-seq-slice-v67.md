# Handoff — seq-slice VALUE modeling (v67 WIP, uncommitted)

Status: **working tree only, deliberately not committed.** `main` is clean
at 0.3.0 + the corpus-key fix (`9b02da6`). Everything below lives in the
dirty tree: `smt/{types,dsl_parser,runtime,abstraction,canonicalize}.nim`
and the new `tests/tsymex_r4_seq_slice.nim`.

## Why it's unfinished

The SAT direction works; a non-SAT query **dies silently** (no output, the
exit-255 signature this repo's calibration maps to a stack overflow —
inside the v64 16 MB solve fiber). Shipping a soundness-adjacent modeling
change whose non-SAT direction crashes would violate §0 and the
dt-bounded doctrine, so it stays out of the release.

## What is already established (do not re-derive)

**The prior "seq slices prove on HEAD" ledger note was an artifact** — a
slice VALUE (`let p = data[4 .. ^1]`) was a macro-time compile abort, and
a `discard`ed slice was silently dropped by the discard arm, so the
earlier probes proved nothing was modeled. Retracted in the v67 note.

**The design** (`iekSeqSlice`): an ARRAY-LAMBDA VIEW —
`len = hi - lo + 1`, `data = (lambda (i) (select base (+ i lo)))` via raw
`Z3_mk_lambda_const`/`Z3_mk_select`, element-sort-generic and
quantifier-free; Z3 beta-reduces selects natively so `isIndex`/`iekSeqLen`
need no changes. Copy semantics are free (the lambda closes over the
base's array AST at slice time). Bounds follow ADR-0027 (svInt proto;
BV-sorted bound declines classified). OOB deposits a real IndexDefect
fork through the SND-4 sink.

**Three routing walls found and fixed** (all still wanted, independent of
the crash):
1. system's slice `[]` takes an **openArray receiver**, so `data[a..b]`
   arrives as `[]`(nnkHiddenStdConv(openArray[T], data), HSlice…) — the
   bare receiver classify sees openArray, not itSeq (the v65
   `contains`-via-openArray precedent).
2. **`^1` does NOT pre-expand for seqs** — it stays `BackwardsIndex(1)`
   in the typed AST (strings have their own expanding overload); rewritten
   to `len(base) - k` in both the bracket and call forms.
3. `ensureProcRegistered`'s unresolvable-`getImpl` **macro `error()`** —
   the last §0 clause-(b) compile wall — now degrades classified
   (`feUnsupportedOp` + a never-registered key → the missing-callee arm).

**Crash triage, already narrowed — start here:**
- NOT Z3 solving: `queryRLimit: 1` does not prevent it (the solver is
  stopped almost immediately and it still dies).
- NOT the IndexDefect fork: disabling the OOB deposit
  (`-d:symexSliceNoOobFork`, a `when` left in `runtime.nim` for exactly
  this bisect) does not prevent it.
- NOT the SAT direction: `payload.len == data.len - 4` proves sxSat with
  a witness cross-checked against real Nim slicing.
- Therefore: the **lambda-backed `svSeq` term on the non-SAT path** —
  term construction, or how a lambda-valued `seqDataRaw` is handled once
  the solver returns non-sat (witness extraction / canonicalize /
  frontier). Next step is a **stack-trace-enabled debug build** (the
  silent death eats the traceback), not more black-box bisection.

## Repro

    docker run --rm -v '<repo>:C:\app' -w 'C:\app' chapulin-symex:2.2.10 \
      powershell -NoProfile -Command 'nim c -r --threads:on \
      --cincludes:C:/z3/include scratch\probe_sq5.nim'

`scratch/probe_sq5.nim` is the minimal case (rlimit-1 variant);
`scratch/probe_sq2.nim` walks all five remaining pins with markers.

**Container hygiene**: always use a named container + a hard `timeout` +
forced `docker rm -f`. A tool-level timeout kills the docker CLIENT and
leaves the container running — that is how two 3-hour Z3 hangs went
unnoticed earlier in this round (the hazard `scripts/dt-bounded.sh`
exists for).

## Also in the dirty tree (ready, blocked only by file entanglement)

`types.nim` carries the **`maxLoopUnwind` documentation** (dev item 2):
an intentional decidability boundary, not a budget knob — chapulin's own
unwind-2-vs-5 bisect gives the identical `sxUnknown`; exhaustion is
always classified (`beBudgetExhausted`) with the configured bound; the
real levers are the closed-form lifts (ADR-0025, ADR-0026). It ships with
this slice because it shares `types.nim` with the `iekSeqSlice` enum.

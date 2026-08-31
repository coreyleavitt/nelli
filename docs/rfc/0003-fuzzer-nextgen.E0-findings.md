# E0 — parallel-corpus-sync spike: findings & decision record

**Slice:** E0 (Track E prerequisite spike). **Status:** empirical run in progress; design
answers below are final, the serialization verdict is stamped once the spike numbers land.
**Spike code (throwaway):** `scratchpad/e0_corpus_sync/` — may be deleted after E3b consumes
this record. **This document is the durable deliverable**, not the spike code.

E0's purpose (RFC §Track E): prove the concurrency model for the corpus before the real
executor commits, so a wrong sync model is discovered on a throwaway rather than on the whole
executor. E0 must (i) choose among three serializations, (ii) demonstrate throughput scaling +
a coherent merged frontier, and (iii) resolve five named mandate items. E3b then builds the
*real* discipline on this record; its size is assigned here.

---

## Topology recap (why the race is NOT "N fuzzing workers")

Under the round-2 centralized-orchestrator topology the corpus has a **single writer** (the
orchestrator); dumb workers never touch the corpus. The single in-memory `CoverageFrontier`
lives in the one orchestrator process, so **there is no cross-process frontier merge** — the
round-1 "merge N workers' frontiers without a lock bottleneck" problem dissolves. The merged
frontier is a permutation-invariant in-memory fold of each returned `Observation` (that fold's
order-independence is E3a's pure-algebra test, not E0's).

The residual disk races E0 actually retires are therefore:
- **(a)** orchestrator `saveCorpus` (hot, append-heavy) vs a **shrinker**'s `save`/`remove`/
  `saveSecondary` on the *same per-testId file* (primary+secondary+corpus are one file today);
- **(b)** orchestrator `saveCorpus` vs a **`forAll` snapshot read** of the corpus (Track U/U2);
- **(4)** **shrinker vs shrinker** — plural shrink slots RMW-ing the same `.bin` concurrently.

The spike models these as *multiple concurrent writers to one file* + *a concurrent snapshot
reader*, which is exactly the filesystem-boundary race regardless of whether the writers are
threads or processes.

---

## Decision: split the corpus onto an append-only delta log; keep `.bin` single-writer

Two structural moves close every residual race by construction, not by locking the hot path:

### Move 1 — split `corpus` into its own file/stream (mandate item 1: **YES, split**)

The corpus section moves out of `<safeKey>.bin` into its own per-testId stream
`<safeKey>.corpus.log`. `<safeKey>.bin` retains only `primary`+`secondary`.

Rationale: the corpus is the **only** section written on the hot path (one append per admitted
seed), and it is written by the **orchestrator alone**. `primary`/`secondary` are written by the
**shrinker** and `dbReusePhase`. Splitting the two means the hot append path never shares a
rewrite target with the shrinker's RMW — **race (a) is eliminated structurally**, not mediated.
What remains on `.bin` is only writer-vs-writer among shrink jobs → mandate item 4.

### Move 2 — the corpus stream is an append-only delta log (serialization candidate 2)

Each corpus mutation appends one length-prefixed record to `<safeKey>.corpus.log` opened
`O_APPEND`; POSIX guarantees a whole-record `write()` to a regular file under `O_APPEND` is
atomic and never interleaves with a concurrent appender, so **concurrent appends compose
losslessly with no global RMW and no hot-path lock**. A reader replays the log to reconstruct
the live set. Record shape:

```
corpus.log := header  record*
header     := "NLC0" (4B magic)  u16 formatVersion  u16 flags
record     := u32 recLen  u8 op  payload         # op ∈ {addCorpus, tombstone, resetBulk}
  addCorpus  payload := <toBytes(choices)>
  tombstone  payload := <toBytes(choices)>        # S4 eviction — logical delete
  resetBulk  payload := u32 n  (u32 len  bytes)*  # compaction preamble: the folded live set
```

Replay semantics reuse `db.nim`'s existing `dedupPrepend` policy (newest-first, dedup, cap the
tail) so a corpus loaded through the log is byte-order-identical to today's in-file corpus — the
`ExampleDatabase` corpus contract is preserved, only the transport changes.

**Why not the alternatives.** (1) Advisory whole-file `flock` LOCK_EX around the RMW is correct
but serializes every writer on the hot path — it re-introduces the lock the append-only design
avoids, and the throughput table (§Empirical) is the tie-breaker. (3) A single-writer mediator
(a dedicated corpus-writer process/queue) is *already* what the centralized orchestrator is for
corpus writes; the delta log is the on-disk representation the mediator writes, so (3) and (2)
compose rather than compete. **flock is retained only** as a belt-and-suspenders cross-process
guard for a foreign tool opening the same DB dir (not the hot path).

---

## Mandate items

### (1) Split corpus into its own file/stream — **RESOLVED: yes** (Move 1 above).

### (2) Compaction design for the delta log — **RESOLVED**

The log grows monotonically (admits append; S4 eviction appends `tombstone` deltas; every reader
replays full history), so compaction is mandatory. Design:

- **Trigger:** size-based, `logBytes > compactionRatio × liveSetBytes` (start at 4×) so
  compaction is amortized O(1) per append and never on the critical path of a single admit.
- **Fold:** replay the log → current live set → emit a fresh log whose first record is a single
  `resetBulk` carrying the folded set, followed by nothing (subsequent appends resume after it).
  Readers thus see **one** format: a compacted file is just a log that begins with `resetBulk`.
- **Who runs it:** the orchestrator (the single corpus writer), so compaction never races another
  corpus *writer*. It races only *readers* → item 3. Compaction is itself a batched fold that
  must publish atomically under the same discipline (item 3's generation swap), or it would
  re-open exactly the race E0 exists to kill.

### (3) Compaction publish is reader-safe on **both** platforms — **RESOLVED (generation + head pointer)**

POSIX `rename`/`unlink` over an open fd keeps the old inode valid, so a `forAll` reader pinned to
a pre-compaction cut point is unaffected — the spike verifies this (§Empirical E.2). **Windows is
not POSIX:** replacing a file a reader holds is governed by sharing-mode flags and
`MOVEFILE_REPLACE_EXISTING` semantics that do *not* preserve the old bytes for existing handles; a
naive in-place fold-and-rename throws `ERROR_SHARING_VIOLATION` or exposes reader-visible
divergence. So we do **not** rename over a held file on either platform. Instead:

- The compactor writes the new snapshot to a fresh generation file `<key>.corpus.<gen>.log`.
- Publication is a single atomic write of a tiny pointer file `<key>.corpus.head` naming the live
  generation (atomic tmp+rename of a ~16-byte file that no long-lived reader holds open).
- A `forAll` reader resolves `head` **once** at snapshot-open and pins that generation for the
  life of its snapshot (open the generation file + capture a byte-offset cut point within it).
- The compactor never unlinks a generation still pinned by a live reader: a bounded **lease**
  (reader registers its pinned gen; GC unlinks a superseded gen only after all leases on it drop
  or a max-lease timeout expires). On Windows, readers open with
  `FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE` so a lease-expired unlink can proceed.

This "generation file + head pointer + lease" scheme is correct **by construction** on both
platforms — it never replaces bytes under a live handle — and subsumes the POSIX inode-retention
case uniformly. The Windows arm cannot be exercised in the Linux container; it is Windows-correct
by construction and is re-verified live at E4a/E4b. The POSIX arm is spike-tested now.

### (4) Shrinker-vs-shrinker write race — **RESOLVED: shrink writes funnel through the orchestrator**

After Move 1, `.bin` (primary+secondary) is written only by shrink jobs and `dbReusePhase`.
Round-2 gives *plural* shrink slots, so >1 shrink job can RMW the same `.bin` concurrently — the
lost-update race relabeled from fuzzing workers to shrink workers. Resolution: **shrink jobs do
not touch `db.nim` directly from a worker slot; they submit `save`/`remove`/`saveSecondary`
*requests* to the orchestrator, which applies them single-writer** through the same critical
section that already serializes admission. This preserves one uniform invariant — *exactly one
writer per file* (corpus: single-writer append log; `.bin`: orchestrator-serialized RMW) — with no
new locking primitive. Shrink writes are rare relative to fuzzing, so the funnel's serialization
cost is negligible; the simpler invariant wins over an N-way `flock` on `.bin`. (The flock path
stays documented as the fallback if a future profile shows `.bin` write contention, and as the
cross-process guard for foreign openers.)

### (5) Corpus-format version tag + incompatible-format rule — **RESOLVED**

The `corpus.log` header carries `formatVersion` (u16). On open, mirroring SW's floor-pin
discipline:

- **file newer than code** (`fileVersion > currentVersion`): **refuse and message**, naming both
  versions ("corpus written by a newer nelli; upgrade or use a separate corpus dir") — never a
  silent misread.
- **file older than code** (`fileVersion < currentVersion`): the reader knows the old layout, reads
  it, and the **next compaction rewrites at the current version** (transparent forward
  auto-migration).
- **unknown magic / corrupt header**: refuse and message (same class as `DbCorrupt` today).
- **legacy single-file corpus** (pre-E0 `.bin` at db-format v3/v4 whose corpus section is *inside*
  `.bin`): a **one-time externalization migration** extracts the `.bin` corpus section into a fresh
  `.corpus.log` and rewrites `.bin` at a bumped db-format version ("corpus externalized"). **U3**
  (which already reconciles doc/code drift and owns `byte-mode → interop-only` corpus migration)
  hosts this migration/rejection logic; E3b provides the reader/writer, U3 wires the one-time move.

---

## Empirical results (spike run 2026-08-25, container `localhost/nelli-dev:latest`)

**Verdict: append-only delta log — CONFIRMED.** All three gating conditions met: (A) the
baseline race reproduces at high magnitude, (B) the delta log shows zero loss, (D) it out-scales
the lock and, unlike the lock, does not degrade under contention.

Throughput (records/sec), W = concurrent writers:

| candidate             | W=1     | W=2     | W=4     | W=8     | zero-loss?            |
|-----------------------|---------|---------|---------|---------|-----------------------|
| baseline (unsafe RMW) | 791     | 1610    | 2739    | 4732    | **NO — 87% lost**     |
| flock LOCK_EX RMW     | 729     | 640     | 562     | 543     | yes (correct)         |
| append-only delta log | 50 814  | 62 122  | 56 293  | 36 641  | yes (correct)         |

- **A — race reproduced:** yes, **87.1% loss** at W=8,K=200 (avg 5 reps; ~206/1600 survive,
  tight variance, no tuning needed). `maxEntries = W*K+1000` so dedup/cap could not mask loss.
- **B — delta log zero-loss:** 1600/1600 every rep (5/5) at W=8,K=200.
- **C — flock zero-loss:** 1600/1600 every rep (5/5) — the lock is *correct*, just slow.
- **D — scaling:** the delta log out-scales flock **~70–115x at every W**; flock *degrades* under
  contention (729->543 rec/s, W1->W8) because every writer serializes on the hot path, while the
  log's append path has no lock to contend on (37k-62k rec/s, flat in W). **Do not read
  baseline's column as scaling** — its rising numbers are *more lost-update work*, not durable
  saves (only flock-vs-log is an apples-to-apples comparison of two correct candidates).
- **E — snapshot consistency:** PASS — 150 mid-flight reader probes across 5 reps, 0 torn
  records, every snapshot a consistent prefix (subset of the final set, no phantom/partial
  entries), parse consumed exactly `cutOffset` bytes. Confirms O_APPEND single-`write()` records
  are atomic against concurrent appenders at these record sizes.
- **E — POSIX compaction reader-safety:** PASS — a reader's pre-compaction open fd reads the old
  inode's bytes unchanged after the compactor's tmp+rename; a fresh open sees the compacted
  content. Confirms the POSIX arm of the generation-swap design (§item 3).

### Two additional findings the spike surfaced (fold into E2/E3 design)

- **F-1 — the orchestrator must hold ONE long-lived DB handle, never construct per-worker.**
  `directoryBasedDatabase(path)`'s constructor sweeps stray `.tmp.*` files on startup, so two
  *concurrent constructions* against the same directory delete each other's in-flight tmp file
  (`OSError` on `moveFile`) — a race distinct from the RMW race. The centralized orchestrator
  already implies a single long-lived handle; **make it a stated E3b invariant** (construct once
  in the orchestrator, share the handle to any code path that needs the DB). A worker slot must
  never construct its own `directoryBasedDatabase` on the shared dir.
- **F-2 — the delta log's win is not only lock-avoidance; it also sidesteps the whole-file
  rewrite.** The shipping backend rewrites the *entire* per-testId file on every save, so an
  uncapped corpus makes each save O(corpus size) and K saves O(K^2) — the spike's D run had to
  cap baseline/flock at `maxEntries=256` to reach realistic steady state. The append-only log is
  O(1)-per-append by construction, so it fixes both the lock-contention cost *and* the
  whole-file-rewrite cost. This strengthens the choice: even single-writer (no contention at
  all), the log is the better representation for a growing corpus.

---

## What E0 hands to the rest of Track E

- **E2a/E2b** wire protocol is independent of this (separate version tag); no coupling.
- **E3a** (freshness) is E0-independent — proceeds regardless.
- **E3b** builds: `<key>.corpus.log` reader/writer (append + replay + `dedupPrepend` semantics),
  the size-triggered compactor, the generation-file + head-pointer + lease publish scheme, and
  the `.bin` orchestrator-funnel for shrink writes. **Size: M** (log + replay + compactor +
  generation/lease; the Windows arm is design-complete here, coded at E4a/E4b). Not S (delta log,
  not a bare file lock) and not L (single-writer topology removes cross-process frontier merge).
- **U2** consumes the snapshot **cut point** = (pinned generation, byte-offset), record-atomic;
  it must not surface for the first time inside U2 — E3b delivers it.
- **U3** hosts the legacy-single-file → `.corpus.log` externalization migration and the
  refuse-on-newer rule.

# RFC-z3-optional — downstream audit for 0.7.0

Two known consumers. One is done; one is a runnable spec because the repo is
not on this machine.

## amoxtli — CLEAR, no action

Audited during stage 2: **zero** nelli imports anywhere in the repo. Nothing
in 0.7.0 can reach it. Recorded here rather than carried as an open task.

## chapulin — the only real downstream, and it must migrate across TWO releases

chapulin is a Windows consumer and is not checked out on the dev host, so this
is the audit to run there, not a result.

It has **not yet absorbed v0.6.0's `FuzzSettings` regroup**, so 0.7.0's
changes land on top of an already-pending migration. That is an argument for
shipping 0.7.0 promptly rather than sitting on it — one migration, not two.
`CHANGELOG.md` covers both releases for this reason.

### 1. The import surface — the break that produces compile errors at a distance

```sh
# Anything that reaches symex/concolic symbols through a bare `import nelli`
# stops compiling. These greps find the call sites BEFORE the compiler does.
# They are a pre-filter, not the audit itself: `import nelli` used to
# transitively re-export the ENTIRE symex+DSL surface (symex.nim -> choice.nim,
# smt/dsl.nim -> smt/types.nim, smt/abstraction.nim, smt/dsl_parser.nim,
# smt/dsl_typebridge.nim, smt/runtime.nim, smt/stdlib_models.nim -> db.nim), and
# any name from that surface reaching chapulin through a bare import breaks the
# same way. The ground truth is compiling chapulin against 0.7.0 — these greps
# only find the call sites faster than the compiler will.
grep -rn 'import nelli' --include='*.nim' .

# Named API surface: the eight symbols §Breaking change names, plus the
# settings/impl types they carry. (This audit previously keyed on five of
# them, which is why it is widened here.)
grep -rn 'z3FullVersion\|symexFind\|symexForAll\|assertCoveredBy\|concolicCollect\|symexOpaque\|concolicFlip\|SymexProgram\|SymexSettings\|runConcolicFlipImpl' --include='*.nim' .

# Choice-IR surface: every choice constructor re-exported from choice.nim,
# plus the IRExprKind enum and its iek* value names re-exported through
# smt/dsl.nim -> smt/types.nim. A call site naming any of these compiled
# under a bare `import nelli` and will not after 0.7.0.
grep -rn 'integerChoice\|floatChoice\|booleanChoice\|bytesChoice\|stringChoice\|IRExprKind\|iek[A-Z]' --include='*.nim' .
```

For each file that hits either of the last two greps, check the first: a file
that has `import nelli` but not `import nelli/symex` needs the explicit
import added. Treat a clean grep as a lead, not a clearance — the definitive
check is compiling chapulin against 0.7.0.

**Not affected:** `symexTarget` / `symexAssert` / `symexAssume` and the
`assertCoveredBy` capture cluster. S1c moved them to `nelli/engine/markers`,
reachable from bare `import nelli`, precisely so marker-annotated production
code survives this break untouched. If chapulin annotates its SUTs, those
files need no change.

### 2. The removed `GuidanceConfig` fields — a compile error naming the field

```sh
grep -rn 'stallRounds\|concolicMaxBranchAttempts' --include='*.nim' .
```

- Inside a `GuidanceConfig(...)` literal → **removed**. Migrate to
  `fuzzConcolic(s, p, settings)`, adding `import nelli/concolic`.
- Inside an `orchestratorPolicy(...)` call → **unchanged**, leave it. The raw
  orchestrator seam deliberately keeps both knobs.

### 3. The `fuzz` proc's bridge parameter

```sh
grep -rn 'concolicBridge' --include='*.nim' .
```

- `fuzz(..., concolicBridge = b)` → `fuzz(..., assist = ConcolicAssist(bridge: b, stallRounds: 1))`.
- `newOrchestrator(..., concolicBridge = b)` → **unchanged**.

### 4. Behavior change with no compile error — read these by hand

The only migration item that does *not* announce itself at compile time:

- A hand-built `ConcolicAssist` (or a `fuzz` call that previously relied on a
  wired bridge plus `stallRounds: 0` to stay inert) is now **coerced active**.
  If chapulin has a call site whose intent was "bridge available but
  disabled", it must now pass **no assist at all**.
- A `ConcolicAssist(stallRounds: n)` with no bridge raises
  `ConcolicAssistError` at campaign start rather than running assist-free.

### 5. Toolchain expectations

Unchanged for the base library, and strictly *relaxed* for consumers that do
not use symex or concolic: after 0.7.0 a chapulin build that only uses
`import nelli` needs no Z3 on the Nim path at all. If chapulin's build
currently passes `--path` entries for z3/softlink solely to satisfy
`import nelli`, they can go.

Consumers that DO use `nelli/concolic` or `nelli/symex` need what they always
needed: Nim ≥ 2.2.10, nim-z3 on the path, and libz3 loadable at runtime — with
the new softening that a *missing* libz3 now degrades a concolic campaign
instead of aborting it (see `CHANGELOG.md`).

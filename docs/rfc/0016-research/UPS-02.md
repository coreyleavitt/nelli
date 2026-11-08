# UPS-02 (draft, not filed): Z3 5.1.0, `Failed to verify: m_cache.mk_unique(p) == p` (`nlsat_solver.cpp:3178`) on a three-assertion integer factoring problem; `unknown` where 4.13.4 answers `sat`

Target: Z3Prover/z3. RFC-0016 section 5.6, decision D-0016-3 (held until
S8cj reduced it; reduced 2026-11-07, slice S8cj). Nothing here has been
filed. nelli reaches this through its default solver on every nonlinear
integer query, so this is not a courtesy report: on Z3 5.1 a factoring
branch the 4.13.4 build decides is declined.

## Title

Z3 5.1.0: nlsat `VERIFY(m_cache.mk_unique(p) == p)` fails (assertion
violation printed, check returns `unknown`) on `p > 1, q > 1, p * q = c`
for any `c`; 4.13.4 answers `sat` in 2.2M rlimit units

## Summary

With the default solver (`Z3_mk_solver`, so the QF_NIA strategy) and
`rlimit` set, the three assertions below make Z3 5.1.0.0 print

```
ASSERTION VIOLATION
File: .../src/nlsat/nlsat_solver.cpp
Line: 3178
Failed to verify: m_cache.mk_unique(p) == p
5.1.0.0
Please file an issue ...
```

early in the search (before 5M rlimit units), after which the check runs to
its rlimit and returns `unknown` with `reason_unknown = "canceled"`. Z3
4.13.4.0 prints nothing and answers `sat` in 2,175,259 units (1.4 s). The
input is satisfiable (`p = 4093, q = 4099`); the same happens for a prime
`c` (unsatisfiable) and for `c = 1022117`, for any `rlimit` from 5M to 50M,
and with `p, q` bounded above. Dropping the two lower bounds makes 5.1
answer `sat` at once (128 units) without the message. The message appears
once per check (three times under `arith.nl.order = false`).

## Reproduction

Input (`UPS-02-min.smt2`):

```
(declare-const p Int) (declare-const q Int)
(assert (> p 1)) (assert (> q 1)) (assert (= (* p q) 16777207))
(check-sat)
```

(`16777207 = 4093 * 4099`.) Driver: parse with `Z3_parse_smtlib2_string`,
assert the three terms on a `Z3_mk_solver` solver with params `rlimit =
50000000` and `random_seed = 0`, call `Z3_solver_check`. In nelli's
research tree the driver is `docs/rfc/0016-research/s8cj/probe_s8cj_ups02b.nim`
(nim-z3), and the raw logs are `s8cj/ups02b-{c,cpp}-z3-5.1.log` and
`s8cj/ups02b-c-z3-4.13.4.log`.

Whether the `z3` command-line binary shows it is not yet checked (the
binary's default exit action on a failed VERIFY is `exit`, so it would
print the message and stop; a context made with `Z3_mk_context_rc` throws
instead, which is what the API path below shows).

## Matrix (all with `rlimit = 50M`, `random_seed = 0` unless noted)

| Variant | Z3 5.1.0.0 (nim-z3, c and cpp backends agree) | Z3 4.13.4.0 |
|---|---|---|
| the three assertions | VERIFY; `unknown (canceled)` at 50,000,020 units, 26-28 s | `sat`, 2,175,259 units, 1.4 s |
| plus `(< p x)` (S8by's shape) | VERIFY; `unknown (canceled)` 50,000,027 | `sat`, 2,438,387 |
| `rlimit = 5M` | VERIFY; `unknown (canceled)` 5,000,020, 2.5 s | `sat`, 2,175,259 |
| prime product 16777213 (UNSAT) | VERIFY; `unknown (canceled)` | `unknown (canceled)` |
| plus `p < 200000, q < 200000` | VERIFY; `unknown (canceled)` 50,000,034 | `sat`, 22,300,690 |
| `c = 1022117` (plus `p < x`) | VERIFY; `unknown (canceled)` 50,000,027 (first round) | (not run; nelli's S8by query with `p, q < 2000` decides in 24k-911k) |
| without `p > 1, q > 1` | `sat`, 128 units, no message | - |
| `arith.nl.nra = false` | VERIFY; `unknown (incomplete (theory arithmetic))`, 444,699 units | `sat`, 2,175,259 |
| `arith.nl.grobner = false` | VERIFY; `unknown (canceled)` | `sat`, 2,175,259 |
| `arith.nl.order = false` | three VERIFY messages; `unknown (unreachable)`, 741,565 units, 0.2 s | `sat`, 2,175,259 |
| `random_seed = 1` | VERIFY; `unknown (unreachable)`, 41,475,772 units (cpp run) | `sat`, 2,175,259 |
| global `nlsat.reorder = false` | VERIFY; `unknown (canceled)` | `sat`, 2,179,719 |
| global `nlsat.simplify_conflicts = false` | VERIFY; `unknown (canceled)` | `sat`, 2,180,593 |
| global `nlsat.factor = false` | VERIFY; `unknown (canceled)` | `sat`, 2,173,455 |
| global `nlsat.seed = 7` | VERIFY; `unknown (canceled)` | `sat`, 2,172,712 |

Two outcomes of the failure are visible from the API: with the default
parameters the limit is cut before the exception reaches the API, and the
check returns `unknown` / `canceled` with no error code set; under
`arith.nl.order = false` or `random_seed = 1` the exception reaches
`Z3_solver_check` first, and the check returns `unknown` with
`reason_unknown = "unreachable"` (the `default_exception("unreachable")`
that `invoke_exit_action(ERR_UNREACHABLE)` throws for an `_rc` context).

## Where the check is (5.1.0 source)

Both `VERIFY(m_cache.mk_unique(p) == p)` sites are in
`nlsat::solver::imp::reinit_cache(atom*)` (the ineq-atom and root-atom
branches), called from the no-argument `reinit_cache()`, whose only callers
are `reorder(unsigned sz, var const* p)`, around `m_cache.reset()`. After
the polynomial cache is reset during variable reordering, an atom's
polynomial is not the cache's unique representative: two atoms hold
structurally equal polynomials as different objects. `VERIFY` is compiled
into release builds (`util/debug.h`): `notify_assertion_violation` prints
the block above, then `invoke_exit_action(ERR_UNREACHABLE)`, which is
`exit` by default and `throw default_exception` for a context made with
`Z3_mk_context_rc` (`api_context.cpp`). The throw unwinds through
`nra_solver::check` (rethrown unless canceled), `theory_lra`, `smt::context`
(catches only `oom_exception`) to `_solver_check` in `api_solver.cpp`,
which sets `reason_unknown` and returns `Z3_L_UNDEF`.

## Versions

| Z3 | How obtained | Result |
|---|---|---|
| 4.13.4.0 | openSUSE Tumbleweed `libz3.so.4.13` (podman image `nelli-dev:z3-4.13.4`) | no message; `sat` 2,175,259 units |
| 5.1.0.0 | openSUSE Tumbleweed `libz3-5_1-5.1.0-1.1` (podman image `nelli-dev:latest`) | reproduces, every run |
| 5.4.0 nightly | not yet run (UPS-03 used `z3-5.4.0-x64-glibc-2.39.zip` from the `Z3Prover/z3` "Nightly" release, 2026-11-07) | - |

Linux x86-64, glibc 2.43, gcc; Nim 2.2.10 through nim-z3, c and cpp
backends (identical results).

## Effect in nelli

A factoring branch condition that 4.13.4 decides is `sxUnknown` on 5.1
(the search is cut by the rlimit after the failure): a precision loss, not
a soundness one. The verdict after the message is never `sat` or `unsat`
in either path (canceled or `unreachable`), pinned by
`tests/tsymex_0016_s8cj_mkunique.nim` through `symexFind` with fd 2
captured.

## How it was found

RFC-0005 slice S8by (the concolic scratch solves) observed the message on
`x * y` with `x, y < 200000` on Z3 5.1; S8cj reduced it to the three
assertions above and ran the matrix.

Fileable as-is: yes for the API path (a 3-line SMT-LIB input plus any
C-API driver setting `rlimit` on a `Z3_mk_solver` solver); the `z3` binary
and the nightly are still to be run, and the report should say whether the
binary exits on the VERIFY.

# S8bn -- DONE

(Written by the sls2 parent session from the agent's final report, because the agent could not write this file. The sha and Windows run ids were re-verified with git and `gh run list`.)

- **sha:** 22361d704587de9db4181964aaf5d0b67d4a20ca on `rfc-0005-s8bn`.
- **base:** a28c9c3 (rfc-0005-s8bh, walker 208).
- **walker:** 215. CR2 is pinned to 215, and the S8bn suite has a `>= 215` floor.
- **History:**
  1. 62382e0 `feat(symex): RFC-0005 S8bn -- ptr witnesses, var-formal reachability, a raising closure`. Items 1-3 and 5, plus the RFC row.
  2. a8d99c5 `feat(symex): RFC-0005 S8bn -- S8bk's late address on a call through a proc value`. Item 6b, self-contained, with its pins in their own test block.
  3. 22361d7 `feat(symex): RFC-0005 S8bn -- proc fields, methods, of / nil, hierarchies, aggregate ptr targets; walker 215`. Items 4 and 6-9, the repins, CR2, the floor pin, and the RFC "As landed (S8bn)" section with the row flipped to done.

## Windows (22361d7), all success
| Leg | Run id |
|---|---|
| symex-mingw | 37125136671 |
| fuzzer-mingw | 37125136599 |
| fuzzer-msvc | 37125136579 |

An earlier run on 2f16ac9 was also all success (37120957833, 37120957825, 37120957845).

## Suites
The suites ran at 2f16ac9; 22361d7 only adds the RFC text on top of it.

| Configuration | Suites | Tests | Failed |
|---|---|---|---|
| Z3 5.1, c | 101 | 1448 | 0 |
| Z3 4.13.4, c | 101 | 1448 | 0 |

- Per-suite counts are identical on the two Z3 versions.
- cpp, Z3 5.1: `tsymex_rfc0005_s8bn_remainder` 36/36.
- The S8bn suite has 36 tests, is registered in `nelli.nimble`, and its binary runs in about 3 s.
- The 101 suites are:
  - the S8 remainders;
  - the closure, ptr, witness, hierarchy and 163-audit families;
  - every suite that reads the source (the N2, A2a, r6 and s8ab audits and similar).

## CI reds fixed during this round (folded into commit 3)
- **N2 kindgate audit:** the new routine-kind checks used inline `nskProc`/`nskFunc` sets. They now go through `isUserRoutine` and a new named const, `procValueSymKinds`, in `dsl_typebridge.nim`.
- **phase1_dsl:** "node has no type". The check that recognises Nim's folded `of` now uses `typeKind == ntyBool`.
- **Repins:**
  - `s2_replay`: a `ptr string` witness now runs (roConfirmed), so the "unexecutable ptr witness" example is now `ptr seq[int]`.
  - `s8d_typeheads`: the user generic `Option` is now sxSat. `options.Option` still declines.
- **Earlier repins:**
  - S8bh: `pfld_dead` and `m_dead` are now sxUnsat, `psg` declines with "may dangle", and `pvf` is a clean sxSat.
  - S8ab: the macro count goes from 22 to 24.
  - S8ao and S8ap: the unrecognised-generic example is now a generic case object.

## RED / GREEN
| Item | RED | GREEN |
|---|---|---|
| 1 | `po`/`pos` replayed roRefuted | roConfirmed |
| 2 | `pg`/`pv`/`pvf` replayed roRefuted; `pgs` was sxUnknown | roConfirmed |
| 3 | `vfl`/`vff`/`vfc` declined | clean; the `vfa`/`vfr`/`vfh` controls still decline |
| 4 | aggregates declined: "by-value aggregate this model holds no cell for" and "held in a heap cell" | roConfirmed; `_dead` twins sxUnsat; resized containers decline "may dangle" |
| 5 | `ceClosureBodyDiverged` | a raise |
| 6 | `pf`/`pp`/`pe`/`pr`: "call to `o.f` not in supported fragment"; methods: unregistered callee `setM6`; `ug_moved`: no candidate | sat or unsat as Nim gives; method dispatch works; `ug_moved` gets a candidate |
| 6b | `lcp`/`lad`/`lar`/`lsq` inverted (reachable label sxUnsat, `_dead` twin sxSat) | correct |
| 7 | `of` unsupported; `ofs` walker fault; `nnkNilLit` declined | `of` tests the run-type tag; `nil` parses |
| 8 | `ia`/`ca` Ref sort mismatch; `ra` false sxUnsat; `cd_dead` false sxSat; generics `feUnsupportedParamType` | correct; `ga`/`gv`/`gl` roConfirmed |
| 9 | `ta_dead`/`ts_dead` false sxSat | sxUnsat |

## Soundness bugs found (all fixed here)
- **6b:** a by-address actual of a call through a proc value was addressed where it stands, not at the call. This gave inverted verdicts.
- **9:** a parameter's run-type tags were free, giving false sxSat.
- **`of RootRef` hierarchy:** parameters never aliased, a false sxUnsat (`ra`).
- **Case-object down-conversion:** a false sxSat (`cd_dead`).
- **Crash class:**
  - a folded `of` reached the walker as an int and caused a walker fault;
  - a field the classified type does not list failed the build with a macro `error`;
  - unwrapped raw Z3 ASTs were reused after a later Z3 call (a refcount bug).

## Design
- **1:** the witness binds parameters in rank order and builds the tuple in parameter order.
- **2:** the pointer is aimed at the variable by name (`@aim:<name>`) and the replay hands it that variable's address. A `ptr string` merges through `ptrIteSV`.
- **3:** the parser records which `var` actuals no pointer can address (`cVarPtrSafe` / `CallFrame.ptrRiskFormals`).
- **4:** per-part targets (`ptrVarLeaves`) carry S8ax's identity:
  - `<T>__@ptridx` for a seq element;
  - `<T>__@ptrkey` for a table value.

  Guards against resizing are `lenUntouched`, `tabNoDeletion` and the same-term length check. A set holds no target. Replay uses `ptrAimInto`.
- **5:** the divergence degrade applies only when no raise escapes the body.
- **6, proc fields:**
  - A heap object's proc field is held as shadow code `@pf_<f>`.
  - Candidates come from the `procFieldAssigns` scan.
  - Anything else takes a decline that applies only on feasible paths (`unIfFeasible`).
- **6, methods:** the caller-scope `symexRegisterMethods` re-expansion, then deepest-first tag dispatch.
- **6, havoc:** an unknown target havocs every bound global.
- **7:** a tag test against the type's chain; a bool-typed IntLit becomes a bool literal; `nil` becomes `mkNil` of the position's type.
- **8:** `{.inheritable.}`, `RootRef` and one case level join the hierarchy. Generic instances are classified with their arguments substituted (`classifyGenericInstance`, `genericFrames`) and named in witnesses as `head[args]`.
- **9:** `allocateSym` ties a parameter's tag levels to its static type's chain.

## For the batch integrator
- **S8bk:**
  - `placeLateAddrs` (commit a8d99c5) is superseded by S8bk's `placeLateAddr` / `orderOperands`. Drop a8d99c5, or merge it into S8bk's helper.
  - S8bn's decline is `feUnsupportedOp`; S8bk's is `feEvalOrderUnmodelled`. The 6b pins should pass with only the kind changed; the `lim` needle is "never checked".
  - Keep `unIfFeasible` and `declineMarker(..., ifFeasible)`: commit 3's heap proc-field dispatch also uses them.
- **S8ax:** item 4 re-implements S8ax's element identity (root, path, snapshot index) on S8bh's `ptrsel`, not on S8ax's address cells. Reconcile with `elemAddrNode` (621af8f) when both are in.

## Different mechanisms, reported and not fixed here (also in the RFC)
- **PRECISION:** a pointer into a case object, a seq of aggregates, or a table of a non-`int` value still declines; so does any generic case object.
- **PRECISION:** reading an aggregate global (`var g: tuple[...]`, an array global) is `feGlobalReadUnmodelled` on this base, before any pointer is involved. Item 4's global path is therefore pinned through `var` parameters.
- **SOUNDNESS:** reading an element of an array global (`gArr[2]`) is a walker fault (the `recv.kind == svArray` assertion), a crash-class bug of its own.

## Tree state
- `probe/` and the `s8bn-red` worktree have been removed.
- `$W/reports-out/s8bn.progress.md` is current.

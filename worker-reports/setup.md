# Job 1: setup (worker sls2)

Status: DONE. The environment is ready, and all smoke tests pass on both Z3 versions.

## Host

- openSUSE Tumbleweed 20260103 on WSL2 (kernel 6.6.87.2-microsoft-standard-WSL2).
- `nproc`: 8.
- `free -g`: Mem 31 total / 1 used / 28 free (29 available); Swap 8.
- podman 5.8.2.
- Image `localhost/nelli-dev:latest` = `dbf4162a866f17113fb2aa6bc147e1b0f4294d2965214caa57a03b0aacfbe63d`.
  - Nim 2.2.10. The image's Z3 is 5.1.0.0 (`libz3-5_1-5.1.0-1.1`), and PCRE 8.45 is built from source.
- Repo: `~/work/nelli` at `rfc-0005-soundness-channels` f488986. Walker is 202.
- Deps:
  - softlink 872042789d93942e2258d08ff167f44ebc5c8104 (v0.11.2);
  - nim-z3 ae509f0eea606bd085064ce1f1ab107c2cdd5806.
- `gh` is authenticated as coreyleavitt, so this worker can watch the Windows CI legs itself.

## Deviations from the setup instructions (all required to make things work)

1. **The image build failed as written.** `scripts/build-dev-image.sh` fails at STEP 2/5 (the first RUN). There was no network problem: ghcr and zypper were both reachable.

       runc create failed: unable to start container process: unable to apply cgroup
       configuration: unable to start unit "runc-buildah-buildah959003134.scope" ...: Permission denied

   The cause is that buildah requests the systemd cgroup manager, and WSL has no systemd user session. `podman run` falls back to cgroupfs by itself, but `podman build` does not. I built with the script's exact command plus `--cgroup-manager=cgroupfs`:

       podman --cgroup-manager=cgroupfs build -t localhost/nelli-dev:latest -f scripts/Containerfile scripts/

   That took 1m39s and succeeded. I did not change any podman or system config. A rebuild on this host needs the same flag.

2. **The absolute `_deps` symlinks do not resolve inside the container.** `dt-bounded.sh` mounts only the checkout at `/work`, so `_deps/z3 -> /home/corey/work/deps/nim-z3` dangles in the container. Every suite that imports symex failed to compile with `src/nelli/symex.nim(33, 8) Error: cannot open file: z3`. CR2 passed only because it doesn't import z3.

   The fix: the dep checkouts now live as real directories at `~/work/nelli/_deps/{softlink,z3}`, still at the pinned shas. `~/work/deps/{softlink,nim-z3}` are now symlinks pointing back to them.

   **Consequence for WORKER-BRIEF.md's worktree recipe:** `ln -sfn ~/work/deps/... _deps/...` in a worktree will hit the same compile error. Worktrees on this host have to copy the deps instead: `mkdir -p _deps && cp -a ~/work/nelli/_deps/softlink ~/work/nelli/_deps/z3 _deps/`. The copy is small. This worker does that for every worktree it creates.

3. **`~/work/dt413.sh`** is `scripts/dt-bounded.sh` with two changes:
   - `-v ~/work/z3-4.13.4-x64-glibc-2.35/bin:/z3413:ro -e LD_LIBRARY_PATH=/z3413` is added to `podman run`;
   - `cd "$(dirname "$0")/.."` is replaced with `cd "$(git rev-parse --show-toplevel)"`, because the script lives outside the repo. Run it from inside a checkout or worktree.

   A probe calling `z3FullVersion()` confirms what each runner loads: `dt-bounded.sh` gets 5.1.0.0 and `dt413.sh` gets 4.13.4.0.

## Smoke tests (c backend, f488986, run one at a time on an idle box)

Wall time includes the nim compile.

| Suite | Z3 5.1 (`dt-bounded.sh c`) | Z3 4.13.4 (`dt413.sh c`) |
|---|---|---|
| tsymex_phase15_CR2_cachekey | PASS, 6 OK, 4.4s (walker pin "202" checked) | PASS, 6 OK, 3.8s |
| tsymex_rfc0005_s8au_remainder | PASS, 35 OK, 32.8s | PASS, 35 OK, 33.8s |
| tsymex_rfc0005_s8ay_remainder | PASS, 40 OK, 62.9s | PASS, 40 OK, 54.8s |

## Recommended `scripts/sweep.sh -j`

- **`-j 6`** for a dedicated gate sweep on an idle box. That leaves 2 of the 8 cores for nim/gcc compile bursts and podman overhead, so 900s timeouts are not inflated by CPU starvation. Memory (29 GB available) is not the binding constraint at that width.
- **`-j 4`** if the sweep has to share the box with the slice agents' test runs. Jobs 2 and 3 will be running at the same time on this machine, so a gate sweep arriving mid-slice will run at `-j 4`, or at `-j 6` with the slice agents' runs paused.

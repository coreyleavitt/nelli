# RFC-fuzzer-nextgen — Windows verification capability (Eci DoD artifact)

This is the durable, greppable capability flag the RFC's Eci slice requires
(RFC-fuzzer-nextgen.md §Track E, Eci: "emits a checked-in capability flag …
E4a–c's own `/tdd` invocation checks it as a precondition"). Machine-readable
keys below; prose after.

```
WINDOWS_LOCAL_TOOLCHAIN: cross-compile-only
WINDOWS_LOCAL_RUN: unavailable
WINDOWS_RUN_CHANNEL: ci-push-and-wait
WINDOWS_RUN_WORKFLOWS: fuzzer-windows.yaml symex-windows.yaml
WINDOWS_PUSH_AUTHORIZED: yes (Corey, 2026-08-26, branch rfc-fuzzer-nextgen)
```

## Determination (made during Eci, 2026-08-26)

- The dev host is Linux; podman/docker on Linux cannot run Windows
  containers. The `chapulin-symex` Windows container referenced in CLAUDE.md
  lives on CI/a Windows machine, not this host. **No local Windows RUN
  capability exists.**
- The local dev image (`localhost/nelli-dev:latest`, scripts/Containerfile)
  now carries the **mingw64 cross toolchain**; `scripts/dt-crosswin.sh <c|cpp>
  <file.nim>` compiles **and links** any module or test for
  `--os:windows --cpu:amd64` in seconds. This is the fast local feedback the
  RFC's round-2 feasibility fix demanded: it catches missing
  `when defined(posix)` gating, Windows API misuse, and link errors without a
  CI round-trip. It **cannot execute** the result — a green cross-compile is
  NOT a green test run.
- Wine was rejected as a run channel: Job Object limits, CreateProcess
  semantics, and unhandled-exception filtering (exactly E4a–c's subject
  matter) are not faithfully emulated, so a wine-green result would be the
  "silently declares GREEN off a non-Windows compile" failure mode the RFC
  names, one layer up.

## Consequence for E4a / E4b / E4c

Per the RFC, with no local run channel these slices are **push-and-wait**:
platform-independent logic (frame parsing, dispatch, breaker policy) gets
ordinary local RED-GREEN via `dt-bounded.sh`; the Windows syscall glue gets
build-checked via `dt-crosswin.sh`, and RUN-verified by pushing
`rfc-fuzzer-nextgen` and reading the `fuzzer-windows` workflow result
(`gh run list --workflow=fuzzer-windows.yaml`). Corey authorized the push
channel on 2026-08-26, so push-and-wait is grindable without further
per-push approval on this branch.

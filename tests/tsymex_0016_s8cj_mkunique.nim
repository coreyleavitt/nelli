## RFC-0016 S8cj (UPS-02, PND-10). Z3 5.1.0 fails its own
## `VERIFY(m_cache.mk_unique(p) == p)` (`nlsat_solver.cpp:3178`, in
## `nlsat::solver::imp::reinit_cache`, called only from the variable
## reordering) on a wide factoring query -- `p > 1, q > 1, p * q ==
## 16777207` (SAT: 4093 * 4099) -- prints an ASSERTION VIOLATION to stderr
## and runs the check to its rlimit, returning unknown
## (`docs/rfc/0016-research/UPS-02.md`). PND-10 asked whether a verdict
## reached after that message can be trusted.
##
## Pinned here, natively, through `symexFind` on that SUT:
##   (1) the verdict is never a false `sxUnsat` (the target is reachable);
##   (2) where the message was printed in this process, the verdict is
##       `sxUnknown`: the VERIFY throws, the throw unwinds to the API's
##       check, which returns `unknown` (the limit is canceled by then, so
##       no `Z3_EXCEPTION` is set), and the walk declines;
##   (3) a `sxSat` (Z3 4.13.4 decides the query in 191,361 units and prints
##       nothing) carries a witness that is checked natively.
## The message itself is a Z3 defect, not pinned: a Z3 that no longer prints
## it passes through (3).
import std/[unittest, strutils, os]
import nelli/symex
import nelli/smt/types
when defined(posix): import std/posix

proc wideFactoring(p, q: int) =
  if p > 1 and q > 1 and p * q == 16777207:
    symexTarget("s8cj_wide_factoring")

const bounded = SymexSettings(budget: ResourceBudget(queryRLimit: 20_000_000))
  ## The message appears before 5M units on Z3 5.1; 20M bounds the test's
  ## wall time on a build that neither prints it nor decides the query.

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template captureStderr(body: untyped): string =
  ## Runs `body` with fd 2 redirected to a file and returns what landed
  ## there (Z3 prints its assertion violations to `std::cerr`). POSIX only;
  ## elsewhere `body` runs and the capture is empty.
  when defined(posix):
    let path = getTempDir() / "s8cj_stderr_" & $getCurrentProcessId() & ".txt"
    stderr.flushFile()
    let saved = dup(2.cint)
    let fd = posix.open(path.cstring, O_WRONLY or O_CREAT or O_TRUNC, Mode(0o600))
    doAssert fd >= 0 and dup2(fd, 2.cint) == 2
    body
    stderr.flushFile()
    doAssert dup2(saved, 2.cint) == 2
    discard posix.close(fd)
    discard posix.close(saved)
    let captured = readFile(path)
    removeFile(path)
    captured
  else:
    body
    ""

suite "S8cj: a verdict after Z3's mk_unique message is never a trusted sat/unsat":

  test "wide factoring through symexFind":
    var status: SymexStatusKind
    var errs: string
    var witnessOk = false
    let captured = captureStderr:
      let r = symexFind(wideFactoring, tLabel("s8cj_wide_factoring"), bounded)
      status = r.status
      errs = show(r.errors)
      if r.status == sxSat:
        let (p, q) = r.witness
        witnessOk = p > 1 and q > 1 and p * q == 16777207
    let saw = "mk_unique" in captured
    # Echoed, not only checkpointed: a passing run should still show which
    # Z3 build's behaviour it saw.
    echo "s8cj_mkunique: status=", status, " errors=", errs
    echo(if saw: "s8cj_mkunique: Z3 printed the mk_unique assertion violation in this process"
         else: "s8cj_mkunique: no mk_unique message in this process")
    # (1) the target is reachable: a refutation would be a false verdict.
    check status != sxUnsat
    # (2) after the message, never a verdict.
    if saw: check status == sxUnknown
    # (3) a decision carries a witness that holds natively.
    if status == sxSat: check witnessOk

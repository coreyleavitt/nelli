<#
.SYNOPSIS
  Builds and runs one symex suite on the Windows CI leg under a wall-clock
  and memory watchdog.

.DESCRIPTION
  RFC-0005 S8r. `corpus (shard 2)` of symex-mingw lost its runner ("The
  hosted runner lost communication with the server") at 6772146, 8b9e4b4
  and 5dc201f. A lost runner uploads no step log, so the suite that starved
  it could not be named. This wrapper keeps a single suite from taking the
  runner down with it:

    - the suite is compiled first (`nim c`), then its binary is started as a
      child process and polled every 2 s;
    - past -TimeoutSec of wall clock, or once the child's peak working set
      passes -MaxWorkingSetMB, the child is killed and the suite is reported
      as failed with the reason, so the shard step still finishes and
      uploads its log;
    - every suite prints one `<== <suite> rc=... wall=... peakWS=...` line,
      so a green run also records where the shard's time and memory go.

  Exit code: the suite's own exit code, 124 on a wall-clock kill, 125 on a
  memory kill, or the compiler's exit code on a build failure.

.PARAMETER Suite
  Test file stem under tests/ (e.g. tsymex_r6_b3_scanpair).
.PARAMETER TimeoutSec
  Wall-clock limit for the test binary (compile time excluded).
.PARAMETER MaxWorkingSetMB
  Peak working-set limit for the test binary, in MB.
.PARAMETER ExtraNimArgs
  Additional `nim c` arguments (e.g. -d:symexCiLeanB5).
#>
param(
  [Parameter(Mandatory = $true)][string]$Suite,
  [int]$TimeoutSec = 240,
  [int]$MaxWorkingSetMB = 6144,
  [string[]]$ExtraNimArgs = @()
)

$ErrorActionPreference = 'Stop'

Write-Host "==> $Suite"
# -Wl,--stack: link an 8 MB main-thread stack (Linux parity). Windows
# defaults to 1 MB, and deep walker/Z3 recursion intermittently overflowed it
# as a silent crash (catalog #11 class).
nim c --cc:gcc --threads:on --hints:off --colors:off `
  --path:src --path:_deps/z3/src --path:_deps/softlink/src `
  --cincludes:C:/z3/include `
  --passL:"-Wl,--stack,8388608" @ExtraNimArgs "tests/$Suite.nim"
if ($LASTEXITCODE -ne 0) {
  Write-Host "<== $Suite rc=$LASTEXITCODE (compile failed)"
  exit $LASTEXITCODE
}

$exe = Join-Path (Get-Location) "tests/$Suite.exe"
$sw = [System.Diagnostics.Stopwatch]::StartNew()
# -NoNewWindow keeps the child's stdout/stderr on this step's console.
$p = Start-Process -FilePath $exe -NoNewWindow -PassThru
# Touch the handle now: without it, ExitCode reads back as $null after exit.
$null = $p.Handle
$killed = ''
$peakMB = 0
while (-not $p.WaitForExit(2000)) {
  $p.Refresh()
  $peakMB = [math]::Max($peakMB, [math]::Round($p.PeakWorkingSet64 / 1MB))
  if ($peakMB -gt $MaxWorkingSetMB) {
    $killed = "memory: peak working set ${peakMB} MB > ${MaxWorkingSetMB} MB"
  } elseif ($sw.Elapsed.TotalSeconds -gt $TimeoutSec) {
    $killed = "wall clock: over ${TimeoutSec} s"
  }
  if ($killed) {
    Stop-Process -Id $p.Id -Force -ErrorAction SilentlyContinue
    $p.WaitForExit()
    break
  }
}
$wall = [math]::Round($sw.Elapsed.TotalSeconds, 1)
if (-not $killed) {
  # PeakWorkingSet64 is not readable after exit on every runtime; keep the
  # last polled value then.
  try { $peakMB = [math]::Max($peakMB, [math]::Round($p.PeakWorkingSet64 / 1MB)) } catch {}
}
if ($killed) {
  $rc = if ($killed.StartsWith('memory')) { 125 } else { 124 }
  Write-Host "<== $Suite rc=$rc wall=${wall}s peakWS=${peakMB}MB KILLED ($killed)"
  exit $rc
}
$rc = $p.ExitCode
Write-Host "<== $Suite rc=$rc wall=${wall}s peakWS=${peakMB}MB"
exit $rc

# One-off measurement for RFC-0005 S8cm: where a suite's compile goes on Windows.
$ErrorActionPreference = 'Continue'
Write-Host "PROBE cpus=$env:NUMBER_OF_PROCESSORS"
(Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory / 1GB | ForEach-Object { Write-Host "PROBE memGB=$_" }
(Get-CimInstance Win32_Processor | Select-Object -First 1).Name | ForEach-Object { Write-Host "PROBE cpu=$_" }
try { Get-MpComputerStatus | Select-Object RealTimeProtectionEnabled | ForEach-Object { Write-Host "PROBE defender=$($_.RealTimeProtectionEnabled)" } } catch { Write-Host 'PROBE defender=unknown' }

$nimArgs = @('--cc:gcc', '--threads:on', '--hints:off', '--colors:off', '--path:src', '--path:_deps/z3/src',
             '--path:_deps/softlink/src', '--cincludes:C:/z3/include', '--passL:-Wl,--stack,8388608')

function Clock([string]$label, [scriptblock]$body) {
  $sw = [System.Diagnostics.Stopwatch]::StartNew()
  & $body *> $null
  Write-Host ("PROBE {0} {1:n1}" -f $label, $sw.Elapsed.TotalSeconds)
}

function Serial([string]$t, [string]$cache, [string]$extra) {
  # One TU at a time, largest first, from the build's own command list.
  $j = Get-Content -Raw "$cache/$t.json" | ConvertFrom-Json
  $rows = @()
  foreach ($c in $j.compile) {
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    cmd /c "$($c[1]) $extra" *> $null
    $rows += [pscustomobject]@{ F = (Split-Path $c[0] -Leaf); Sec = $sw.Elapsed.TotalSeconds; MB = (Get-Item $c[0]).Length / 1MB }
  }
  $sum = ($rows | Measure-Object Sec -Sum).Sum
  Write-Host ("PROBE {0} serial-gcc[{1}] sum={2:n1} files={3}" -f $t, $extra, $sum, $rows.Count)
  foreach ($r in ($rows | Sort-Object Sec -Descending | Select-Object -First 5)) {
    Write-Host ("PROBE   {0:n1} s  {1:n1} MB  {2}" -f $r.Sec, $r.MB, $r.F)
  }
}

foreach ($t in @('tsymex_phase14_b5_replaymiss', 'tsymex_configdefaults_depth', 'tsymex_rfc0005_s8ar_remainder')) {
  $cache = "C:/nc/$t"
  Clock "$t frontend" { nim c --compileOnly "--nimcache:$cache" @nimArgs "tests/$t.nim" }
  $cbytes = (Get-ChildItem "$cache/*.c" | Measure-Object Length -Sum).Sum / 1MB
  Write-Host ("PROBE {0} cMB={1:n1}" -f $t, $cbytes)
  Serial $t $cache ''
  Serial $t $cache '-pipe'
  Remove-Item -Recurse -Force $cache
  Clock "$t full" { nim c "--nimcache:$cache" @nimArgs "tests/$t.nim" }
  # A second full build: every object is reused, so this is the frontend plus the link.
  Clock "$t relink" { nim c "--nimcache:$cache" --forceBuild:off @nimArgs "tests/$t.nim" }
}

# Two compiles at once, against one after the other (a shard's possible concurrency).
$a = 'tsymex_rfc0005_s8ax_remainder'; $b = 'tsymex_rfc0005_s8bn_remainder'
Clock 'serial-pair' { nim c "--nimcache:C:/nc2/$a" @nimArgs "tests/$a.nim"; nim c "--nimcache:C:/nc2/$b" @nimArgs "tests/$b.nim" }
Remove-Item -Recurse -Force C:/nc2
$sw = [System.Diagnostics.Stopwatch]::StartNew()
$jobs = foreach ($t in @($a, $b)) {
  Start-Process -FilePath nim -PassThru -NoNewWindow -RedirectStandardOutput "C:/out_$t.txt" -RedirectStandardError "C:/err_$t.txt" `
    -ArgumentList (@('c', "--nimcache:C:/nc2/$t") + $nimArgs + @("tests/$t.nim"))
}
$jobs | ForEach-Object { $_.WaitForExit() }
Write-Host ("PROBE parallel-pair {0:n1}" -f $sw.Elapsed.TotalSeconds)
exit 0

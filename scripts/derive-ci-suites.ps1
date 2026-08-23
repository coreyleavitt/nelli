<#
.SYNOPSIS
  Derives + shards the symex CI suite corpus from nelli.nimble's `test` task.

.DESCRIPTION
  Round-6 mechanical-debt slice (item 6): this was ~170 lines of inline pwsh
  in .github/workflows/symex-windows.yaml's `derive-suites` job. Extracted
  here, unchanged in behavior, so it can be run locally (not just inside a
  GitHub Actions runner) and so the workflow file itself stays a thin
  invocation instead of carrying the whole parser/accounting logic inline.

  See symex-windows.yaml's own header comment ("DERIVED CORPUS, NOT A
  HARDCODED LIST") for why this exists: the corpus is parsed out of
  nelli.nimble's `test` task at run time rather than hand-maintained, so a
  newly registered tsymex_* suite is automatically picked up.

  Behavior preserved EXACTLY from the inline step this replaces:
    - parses the `task test` suite array out of nelli.nimble
    - restricts to tsymex_* names
    - cross-checks the scan-tail job's own `matrix: suite:` list (parsed out
      of this repo's symex-windows.yaml) against the hardcoded $matrixSuites
      list below, failing loudly on any drift
    - subtracts the scan-tail matrix suites and the annotated skip list from
      the tsymex_* set to get the shard-eligible corpus
    - asserts a corpus floor (150) and full accounting (matrix + skip +
      corpus == total tsymex_* count)
    - round-robins the sorted corpus into 3 deterministic shards
    - emits `shards_json` via $env:GITHUB_OUTPUT when running under GitHub
      Actions (the env var is set), or prints it to stdout otherwise, so a
      developer can run this script locally without a CI environment.

.PARAMETER RepoRoot
  Path to the repository root (the directory containing nelli.nimble and
  .github/workflows/symex-windows.yaml). Defaults to the current directory.
#>
param(
  [string]$RepoRoot = (Get-Location).Path
)

$ErrorActionPreference = 'Stop'

$nimblePath = Join-Path $RepoRoot 'nelli.nimble'
$nimbleText = Get-Content -Raw $nimblePath

# Isolate the `test` task's suite array: from `for f in [` to the
# matching `]:`. If nelli.nimble's task syntax ever changes shape,
# this match fails and we throw below rather than silently
# deriving nothing.
$taskMatch = [regex]::Match($nimbleText, '(?s)task test,.*?for f in \[(?<body>.*?)\]:')
if (-not $taskMatch.Success) {
  throw "derive-suites: could not locate 'task test' suite array in nelli.nimble -- parser is out of sync with the file format"
}
$body = $taskMatch.Groups['body'].Value

$allNames = [regex]::Matches($body, '"(?<name>[^"]+)"') | ForEach-Object { $_.Groups['name'].Value }
if ($allNames.Count -lt 50) {
  throw "derive-suites: parsed suspiciously few task entries ($($allNames.Count)) -- treating as a parse failure"
}

$allTsymex = $allNames | Where-Object { $_ -like 'tsymex_*' } | Sort-Object -Unique

# Scan-tail matrix suites: kept explicit for runner-isolation
# reasons (each gets its own CI job so a runner death names its
# suite and a heavy Z3 query gets a whole runner to itself). Do
# not derive these -- must match the `scan-tail` job's matrix
# below exactly.
$matrixSuites = @(
  'tsymex_r6_b5_chained',
  'tsymex_r6_b6_optionregion',
  'tsymex_r6_nulwitness',
  'tsymex_r6_bug2_scopeddecline',
  'tsymex_r6_a6r_callwitness',
  'tsymex_r6_b7r_bytescan',
  'tsymex_r6_b7r2_pathscope',
  'tsymex_phase15_g8_multi_param',
  'tsymex_phase15_g10_smoke'
)

# Loud cross-check (design finding, round-6 re-review): the
# `$matrixSuites` list above and the `scan-tail` job's own YAML
# `matrix: suite:` list (in symex-windows.yaml) are hand-synced
# twins -- nothing previously enforced they match. A silent drift
# (an entry edited into/out of one list but not the other) either
# double-runs a suite (present in both the derived corpus AND the
# scan-tail matrix) or drops it from CI entirely (excluded from
# the corpus via `$matrixSuites`, but no longer present in
# scan-tail's own matrix either) -- exactly the silent-divergence
# failure mode the whole derive-suites mechanism exists to
# prevent (see the workflow's header, "DERIVED CORPUS, NOT A
# HARDCODED LIST"). Parse the scan-tail job's OWN matrix out of
# the workflow file and assert set-equality against `$matrixSuites`,
# failing loudly (naming exactly which suites are on which side) on any
# drift instead of letting the two lists silently diverge.
$selfWorkflowPath = Join-Path $RepoRoot '.github/workflows/symex-windows.yaml'
$selfText = Get-Content -Raw $selfWorkflowPath
$scanTailIdx = $selfText.IndexOf("`n  scan-tail:")
if ($scanTailIdx -lt 0) {
  throw "derive-suites: could not locate the 'scan-tail:' job in $selfWorkflowPath -- cross-check parser is out of sync with the file format"
}
$scanTailText = $selfText.Substring($scanTailIdx)
# Round-6 re-review (item 6, walker v115): each item line tolerates
# an optional trailing `# comment` -- a bare `\S+` before the line's
# `\r?\n` would swallow the whole run including any `#...` (corrupting
# the parsed name) or, if a comment sits right after the whitespace-
# only trailer, fail that single repetition and truncate the WHOLE
# `(?<items>...)+` capture at that line (silently dropping every
# entry from the comment onward) -- or, if the FIRST entry carries a
# comment, fail the block match entirely and throw the misleading
# "parser is out of sync" error above, even though the file is
# perfectly well-formed YAML. The name-capture group excludes `#`
# explicitly (`[^\s#]+`, not `\S+`) so a same-line comment can never
# be appended onto the captured name either.
$scanTailMatrixMatch = [regex]::Match($scanTailText,
  '(?s)matrix:\s*\r?\n\s*suite:\s*\r?\n(?<items>(?:\s*-\s*[^\s#]+[ \t]*(?:#[^\r\n]*)?\r?\n)+)')
if (-not $scanTailMatrixMatch.Success) {
  throw "derive-suites: could not locate the scan-tail job's 'matrix: suite:' list in $selfWorkflowPath -- cross-check parser is out of sync with the file format"
}
$scanTailSuites = [regex]::Matches($scanTailMatrixMatch.Groups['items'].Value, '-\s*(?<name>[^\s#]+)') |
  ForEach-Object { $_.Groups['name'].Value }
if ($scanTailSuites.Count -eq 0) {
  throw "derive-suites: parsed zero suites from the scan-tail job's matrix -- treating as a parse failure"
}

$matrixSuitesSet = [System.Collections.Generic.HashSet[string]]::new([string[]]$matrixSuites)
$scanTailSuitesSet = [System.Collections.Generic.HashSet[string]]::new([string[]]$scanTailSuites)
$onlyInDeriveMatrix = $matrixSuites | Where-Object { -not $scanTailSuitesSet.Contains($_) }
$onlyInScanTailMatrix = $scanTailSuites | Where-Object { -not $matrixSuitesSet.Contains($_) }
if ($onlyInDeriveMatrix.Count -gt 0 -or $onlyInScanTailMatrix.Count -gt 0) {
  $driftMsg = "derive-suites: '`$matrixSuites' (this script) and the scan-tail job's own matrix have drifted apart -- these two lists MUST be kept identical.`n"
  if ($onlyInDeriveMatrix.Count -gt 0) {
    $driftMsg += "  in derive-suites `$matrixSuites but MISSING from the scan-tail job matrix: $($onlyInDeriveMatrix -join ', ')`n"
  }
  if ($onlyInScanTailMatrix.Count -gt 0) {
    $driftMsg += "  in the scan-tail job matrix but MISSING from derive-suites `$matrixSuites: $($onlyInScanTailMatrix -join ', ')`n"
  }
  throw $driftMsg
}
Write-Host "matrix cross-check OK: $($matrixSuites.Count) suites identical in derive-suites `$matrixSuites and the scan-tail job matrix"

# Explicit skip list -- every entry MUST carry a ledger reason.
# Additions require a ledger entry (see the workflow header
# comment); this is the pressure valve, not a place to silence
# surprises. The three reactivated audit suites (A2a_atomicir,
# A2a_chokepoint, N2_kindgate -- switched from staticRead to
# runtime readFile to dodge MSVC C2026) are deliberately NOT
# skip-listed: they should work on mingw.
#
# A1 adjudication (walker v116): the three suites this list used
# to carry as "next-round seed" (S3_strindex, S10b_strconv,
# A1_bitwise) were adjudicated -- all three were genuine engine
# defects, not stale pins, and are fixed at HEAD (S3's `.high`
# occluded by the A0 low/high-on-type gate; S10b's `parseFloat`
# degrade-placeholder kind mismatch masking its own classified
# error as weInternalWalkerFault; A1 cell 6's same-width int
# reinterpret mis-scoped as a B2 decline). All three now join the
# derived corpus below instead of this list.
$skipReasons = [ordered]@{
  'tsymex_phase15_C4_hof'       = 'known-red, ledger N29 HOF lambda sort-mismatch class (predates round 6)'
  'tsymex_phase15_C6_smoke'     = 'known-red, ledger N29 HOF lambda sort-mismatch class (predates round 6)'
}

# Sanity: matrix/skip entries must actually exist in the nimble
# task (guards against stale references as suites get renamed or
# removed).
$allSet = [System.Collections.Generic.HashSet[string]]::new([string[]]$allTsymex)
foreach ($m in $matrixSuites) {
  if (-not $allSet.Contains($m)) { throw "derive-suites: matrix suite '$m' is not present in nelli.nimble's test task" }
}
foreach ($s in $skipReasons.Keys) {
  if (-not $allSet.Contains($s)) { throw "derive-suites: skip-listed suite '$s' is not present in nelli.nimble's test task" }
}

$excludeSet = [System.Collections.Generic.HashSet[string]]::new([string[]]($matrixSuites + [string[]]$skipReasons.Keys))
$corpus = $allTsymex | Where-Object { -not $excludeSet.Contains($_) } | Sort-Object

if ($corpus.Count -lt 150) {
  throw "derive-suites: derived corpus has only $($corpus.Count) suites (floor 150) -- likely a parse failure, failing loudly instead of running an empty/truncated CI leg"
}

$accountedFor = $matrixSuites.Count + $skipReasons.Count + $corpus.Count
if ($accountedFor -ne $allTsymex.Count) {
  throw "derive-suites: accounting mismatch -- $($allTsymex.Count) total tsymex_* suites vs $accountedFor accounted for (matrix + skip + corpus)"
}

# Round-robin by index into 3 shards, deterministic given the
# sorted corpus.
$shardCount = 3
$shards = @(
  (New-Object 'System.Collections.Generic.List[string]'),
  (New-Object 'System.Collections.Generic.List[string]'),
  (New-Object 'System.Collections.Generic.List[string]')
)
for ($i = 0; $i -lt $corpus.Count; $i++) {
  $shards[$i % $shardCount].Add($corpus[$i])
}

Write-Host "=== derive-suites accounting ==="
Write-Host "total tsymex_* suites in nelli.nimble : $($allTsymex.Count)"
Write-Host "scan-tail matrix (explicit)           : $($matrixSuites.Count)"
Write-Host "skip list (annotated)                 : $($skipReasons.Count)"
Write-Host "derived corpus (shard-eligible)       : $($corpus.Count)"
for ($i = 0; $i -lt $shardCount; $i++) {
  Write-Host "  shard $i : $($shards[$i].Count) suites"
}
Write-Host ""
Write-Host "skip list:"
foreach ($k in $skipReasons.Keys) { Write-Host "  $k -- $($skipReasons[$k])" }

$shardsObj = [ordered]@{
  '0' = @($shards[0])
  '1' = @($shards[1])
  '2' = @($shards[2])
}
$shardsJson = $shardsObj | ConvertTo-Json -Compress -Depth 5

if ($env:GITHUB_OUTPUT) {
  "shards_json=$shardsJson" >> $env:GITHUB_OUTPUT
} else {
  # Local/dev run (no GITHUB_OUTPUT env var): print instead of writing to
  # the (nonexistent) GitHub Actions output file, same output contract
  # otherwise -- a developer can pipe/inspect this directly.
  Write-Host ""
  Write-Host "shards_json (no `$env:GITHUB_OUTPUT set -- printing instead of writing to it):"
  Write-Output $shardsJson
}

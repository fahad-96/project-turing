param([string]$Pkg, [string]$Out, [int]$ChunkMB = 600)
# Packs the prebuilt Mathlib (and dependency) .olean / .olean.private files of the laptop's
# pinned Lean project into gzip tar chunks small enough to move to Claude's cloud workspace.
# Read-only on the Lean project: it only reads files under $Pkg and writes into $Out.
$ErrorActionPreference = "Stop"
$status = Join-Path $Out "pack_status.txt"
function Log($m) {
  $line = "{0} {1}" -f (Get-Date -Format "HH:mm:ss"), $m
  Add-Content -Path $status -Value $line
  Write-Host $line
}
Log "Scanning $Pkg"
$files = New-Object System.Collections.Generic.List[object]
Get-ChildItem -Path $Pkg -Directory | ForEach-Object {
  $lib = Join-Path $_.FullName ".lake\build\lib\lean"
  if (Test-Path $lib) {
    $n = 0
    Get-ChildItem -Path $lib -Recurse -File | ForEach-Object {
      if ($_.Name.EndsWith(".olean") -or $_.Name.EndsWith(".olean.private")) { $files.Add($_); $n++ }
    }
    Log ("  {0}: {1} files" -f $_.Name, $n)
  }
}
$total = ($files | Measure-Object -Property Length -Sum).Sum
Log ("Total: {0} files, {1:N0} MB raw" -f $files.Count, ($total / 1MB))
$limit = $ChunkMB * 1MB
$chunks = New-Object System.Collections.Generic.List[object]
$cur = New-Object System.Collections.Generic.List[object]; $curSize = 0
foreach ($f in $files) {
  if ($curSize + $f.Length -gt $limit -and $cur.Count -gt 0) { $chunks.Add($cur); $cur = New-Object System.Collections.Generic.List[object]; $curSize = 0 }
  $cur.Add($f); $curSize += $f.Length
}
if ($cur.Count -gt 0) { $chunks.Add($cur) }
Log ("{0} chunks of at most {1} MB raw" -f $chunks.Count, $ChunkMB)
$manifest = Join-Path $Out "pack_manifest.txt"
Set-Content -Path $manifest -Value ("chunk`tfiles`traw_bytes`tgz_bytes")
$prefixLen = $Pkg.TrimEnd('\').Length + 1
$i = 0
foreach ($c in $chunks) {
  $i++
  $tag = "{0:D2}" -f $i
  $list = Join-Path $Out ("list_{0}.txt" -f $tag)
  $tgz = Join-Path $Out ("oleans_{0}.tgz" -f $tag)
  $rel = $c | ForEach-Object { $_.FullName.Substring($prefixLen) }
  # one path per line, UTF-8 without BOM, LF line ends
  [System.IO.File]::WriteAllText($list, (($rel -join "`n") + "`n"), (New-Object System.Text.UTF8Encoding($false)))
  $raw = ($c | Measure-Object -Property Length -Sum).Sum
  Log ("chunk {0}: {1} files, {2:N0} MB raw -> {3}" -f $tag, $c.Count, ($raw / 1MB), $tgz)
  if (Test-Path $tgz) { Remove-Item $tgz }
  & tar.exe -c -z --options "gzip:compression-level=1" -f $tgz -C $Pkg -T $list
  if ($LASTEXITCODE -ne 0) {
    Log "  tar with fast gzip failed (exit $LASTEXITCODE), retrying with default gzip"
    if (Test-Path $tgz) { Remove-Item $tgz }
    & tar.exe -c -z -f $tgz -C $Pkg -T $list
    if ($LASTEXITCODE -ne 0) { Log "  tar failed again (exit $LASTEXITCODE)"; throw "tar failed" }
  }
  $gz = (Get-Item $tgz).Length
  Log ("  -> {0:N0} MB compressed" -f ($gz / 1MB))
  Add-Content -Path $manifest -Value ("{0}`t{1}`t{2}`t{3}" -f ("oleans_{0}.tgz" -f $tag), $c.Count, $raw, $gz)
}
Log "ALL CHUNKS DONE"

@echo off
setlocal EnableExtensions
title Project Turing - move C:\lean to D:\lean
set "HERE=%~dp0"
set "STATUS=%HERE%move_lean_status.txt"
echo Move of C:\lean to D:\lean started %DATE% %TIME% > "%STATUS%"
echo.
echo This moves the Lean project (C:\lean, about 6 GB) to D:\lean and leaves a link
echo at C:\lean, so every path (worker, scripts, C:\opt\mathlib4) keeps working.
echo Close the lean_worker window and VS Code before continuing.
echo.
pause

tasklist /FI "IMAGENAME eq lean.exe" | find /I "lean.exe" >nul
if not errorlevel 1 goto :busy
tasklist /FI "IMAGENAME eq lake.exe" | find /I "lake.exe" >nul
if not errorlevel 1 goto :busy
dir /AL /B C:\ 2>nul | findstr /I /X "lean" >nul
if not errorlevel 1 goto :already
if not exist "C:\lean\TuringTask\lakefile.toml" goto :noproject
if exist "D:\lean" goto :dexists

echo [1/5] Measuring sizes ...
powershell -NoProfile -Command "$s=(Get-ChildItem C:\lean -Recurse -File -Force -ErrorAction SilentlyContinue | Where-Object { -not ($_.Attributes -band [IO.FileAttributes]::ReparsePoint) } | Measure-Object Length -Sum).Sum; $f=(Get-PSDrive D).Free; Write-Output ('C:\lean size {0:N1} GB, D: free {1:N1} GB' -f ($s/1GB), ($f/1GB)); if ($f -lt $s + 2GB) { exit 1 }" >> "%STATUS%"
if errorlevel 1 goto :nospace
type "%STATUS%"

echo [2/5] Copying C:\lean to D:\lean. This takes several minutes ...
robocopy C:\lean D:\lean /E /COPY:DAT /DCOPY:DAT /XJ /R:1 /W:1 /NFL /NDL /NP /LOG:"%HERE%move_lean_robocopy_log.txt"
if errorlevel 8 goto :copyfail
echo Copy finished (robocopy log: move_lean_robocopy_log.txt) >> "%STATUS%"

echo [3/5] Checking the copy of C:\lean\TuringTask ...
powershell -NoProfile -Command "$a=Get-ChildItem C:\lean\TuringTask -Recurse -File -Force -ErrorAction SilentlyContinue | Measure-Object Length -Sum; $b=Get-ChildItem D:\lean\TuringTask -Recurse -File -Force -ErrorAction SilentlyContinue | Measure-Object Length -Sum; Write-Output ('C: {0} files {1} bytes; D: {2} files {3} bytes' -f $a.Count,$a.Sum,$b.Count,$b.Sum); if ($a.Count -ne $b.Count -or $a.Sum -ne $b.Sum) { exit 1 }" >> "%STATUS%"
if errorlevel 1 goto :verifyfail
type "%STATUS%"

echo [4/5] Removing the old copy on C: ...
rmdir /S /Q C:\lean
if exist C:\lean goto :rmfail

echo [5/5] Linking C:\lean to D:\lean ...
mklink /J C:\lean D:\lean >> "%STATUS%"
if not exist "C:\lean\TuringTask\lakefile.toml" goto :linkfail
powershell -NoProfile -Command "'Now C: free {0:N1} GB, D: free {1:N1} GB' -f ((Get-PSDrive C).Free/1GB), ((Get-PSDrive D).Free/1GB)" >> "%STATUS%"
echo DONE >> "%STATUS%"
type "%STATUS%"
echo.
echo Done. Start lean_worker.bat again and tell Claude.
pause
exit /b 0

:busy
echo lean.exe or lake.exe is still running. Close the worker window and VS Code, then run this again.
echo STOPPED: lean or lake still running >> "%STATUS%"
pause
exit /b 1
:already
echo C:\lean is already a link. Nothing to do.
echo C:\lean is already a link >> "%STATUS%"
pause
exit /b 0
:noproject
echo C:\lean\TuringTask was not found. Nothing was changed.
echo STOPPED: C:\lean\TuringTask not found >> "%STATUS%"
pause
exit /b 1
:dexists
echo D:\lean already exists. Nothing was changed. Tell Claude.
echo STOPPED: D:\lean already exists >> "%STATUS%"
pause
exit /b 1
:nospace
type "%STATUS%"
echo Not enough free space on D:. Nothing was changed.
echo STOPPED: not enough space on D: >> "%STATUS%"
pause
exit /b 1
:copyfail
echo The copy failed. Nothing was deleted on C:. Tell Claude.
echo STOPPED: robocopy failed, C:\lean untouched >> "%STATUS%"
pause
exit /b 1
:verifyfail
type "%STATUS%"
echo The copy does not match. Nothing was deleted on C:. Tell Claude.
echo STOPPED: copy check failed, C:\lean untouched >> "%STATUS%"
pause
exit /b 1
:rmfail
echo Some files in C:\lean could not be removed (a program still uses them).
echo Close it, then tell Claude. D:\lean holds the full copy.
echo STOPPED: C:\lean partly removed, D:\lean complete >> "%STATUS%"
pause
exit /b 1
:linkfail
echo The link C:\lean could not be created. Tell Claude. D:\lean holds the full copy.
echo STOPPED: mklink failed, D:\lean complete >> "%STATUS%"
pause
exit /b 1

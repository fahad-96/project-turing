@echo off
setlocal EnableExtensions EnableDelayedExpansion
title Pack Mathlib oleans for Claude's cloud (one time, read-only on the Lean project)
rem Copies nothing into the Lean project and deletes nothing. It reads the prebuilt .olean and
rem .olean.private files of Mathlib and its dependencies from the pinned project and writes
rem gzip chunks (about 300 MB each) into D:\lean\_xfer, which Claude then stages to the cloud.
rem Afterwards the folder D:\lean\_xfer can be deleted by hand.
set "PKG=D:\lean\TuringTask\.lake\packages"
set "OUT=D:\lean\_xfer"
if not exist "%PKG%\mathlib\.lake\build\lib\lean\Mathlib.olean" (
  echo Mathlib build not found under %PKG%
  pause
  exit /b 1
)
if not exist "%OUT%" mkdir "%OUT%"
echo Packing started %DATE% %TIME% > "%OUT%\pack_status.txt"
echo This takes roughly 10 to 20 minutes. Progress is written to %OUT%\pack_status.txt
echo You can keep using the computer; leave this window open until it says ALL CHUNKS DONE.
echo.
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0pack_oleans.ps1" -Pkg "%PKG%" -Out "%OUT%" -ChunkMB 600
echo Finished %DATE% %TIME% >> "%OUT%\pack_status.txt"
echo.
echo Done. Tell Claude. (Status: %OUT%\pack_status.txt)
pause

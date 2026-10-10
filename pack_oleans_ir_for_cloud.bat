@echo off
setlocal EnableExtensions EnableDelayedExpansion
title Pack Mathlib .ir files for Claude's cloud (one time, read-only, about 1 minute)
rem Companion of pack_oleans_for_cloud.bat: the small .ir and .ir.sig files (compiled IR) that Lean also reads.
set "PKG=D:\lean\TuringTask\.lake\packages"
set "OUT=D:\lean\_xfer"
if not exist "%OUT%" mkdir "%OUT%"
echo Packing started %DATE% %TIME% > "%OUT%\pack_ir_status.txt"
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0pack_oleans_ir.ps1" -Pkg "%PKG%" -Out "%OUT%" -ChunkMB 600
echo Finished %DATE% %TIME% >> "%OUT%\pack_ir_status.txt"
echo.
echo Done. Tell Claude. (Status: %OUT%\pack_ir_status.txt)
pause

@echo off
setlocal EnableExtensions
title Project Turing - finish the move to D:\lean
set "HERE=%~dp0"
set "STATUS=%HERE%finish_move_status.txt"
set "MATH=D:\lean\TuringTask\.lake\packages\mathlib"
echo Finish move started %DATE% %TIME% > "%STATUS%"
if not exist "D:\lean\TuringTask\lakefile.toml" goto :nod
if not exist "%MATH%\lakefile.lean" goto :nomath

echo [1/3] /opt/mathlib4 links (C: and D:) to the pinned Mathlib on D:
for %%R in (C D) do (
  if not exist "%%R:\opt" mkdir "%%R:\opt"
  if exist "%%R:\opt\mathlib4" rmdir "%%R:\opt\mathlib4"
  mklink /J "%%R:\opt\mathlib4" "%MATH%" >> "%STATUS%" 2>&1
  if exist "%%R:\opt\mathlib4\lakefile.lean" (echo %%R:\opt\mathlib4 ok >> "%STATUS%") else (echo %%R:\opt\mathlib4 FAILED >> "%STATUS%")
)

echo [2/3] old path C:\lean\TuringTask as a link to D:\lean\TuringTask
if not exist "C:\lean" mkdir "C:\lean"
if not exist "C:\lean\TuringTask" mklink /J "C:\lean\TuringTask" "D:\lean\TuringTask" >> "%STATUS%" 2>&1
if exist "C:\lean\TuringTask\lakefile.toml" (echo C:\lean\TuringTask link ok >> "%STATUS%") else (echo C:\lean\TuringTask link FAILED >> "%STATUS%")

echo [3/3] free space
powershell -NoProfile -Command "'C: free {0:N1} GB, D: free {1:N1} GB' -f ((Get-PSDrive C).Free/1GB), ((Get-PSDrive D).Free/1GB)" >> "%STATUS%"
echo DONE >> "%STATUS%"
type "%STATUS%"
echo.
echo Done. Now start lean_worker.bat again (it now uses D:\lean\TuringTask) and tell Claude.
pause
exit /b 0

:nod
echo D:\lean\TuringTask not found. Nothing was changed.
echo STOPPED: D:\lean\TuringTask not found >> "%STATUS%"
pause
exit /b 1
:nomath
echo Mathlib not found in %MATH%. Nothing was changed.
echo STOPPED: Mathlib not found on D: >> "%STATUS%"
pause
exit /b 1

@echo off
setlocal EnableExtensions EnableDelayedExpansion
title Lean worker - leave this window open
set "DEST=D:\lean\TuringTask"
set "JOBS=%DEST%\_jobs"
set "PATH=%USERPROFILE%\.elan\bin;%PATH%"
if not exist "%DEST%\lakefile.toml" goto :noproject
if not exist "%JOBS%" mkdir "%JOBS%"
echo Lean worker is running.
echo It builds the Lean jobs that Claude places in %JOBS%
echo and writes each result to a log file there.
echo Leave this window open while you work with Claude. Close it to stop.
echo.
:loop
for /d %%J in ("%JOBS%\*") do (
  if exist "%%J\READY" if not exist "%%J\DONE" call :run "%%J"
)
echo worker alive %DATE% %TIME% > "%JOBS%\worker_alive.txt"
timeout /t 5 /nobreak >nul
goto :loop

:noproject
echo %DEST% not found.
pause
exit /b 1

:run
set "J=%~1"
echo [%TIME%] building job %~nx1 - about 10 to 15 minutes
echo Job %~nx1 started %DATE% %TIME% > "%J%\log.tmp"
if exist "%DEST%\TuringTask" rmdir /S /Q "%DEST%\TuringTask"
xcopy "%J%\src\TuringTask" "%DEST%\TuringTask\" /E /I /Y >nul
if exist "%J%\src\TuringTask.lean" copy /Y "%J%\src\TuringTask.lean" "%DEST%\TuringTask.lean" >nul
if not exist "%J%\src\TuringTask.lean" echo import TuringTask.Basic> "%DEST%\TuringTask.lean"
pushd "%DEST%"
echo ===== lake build >> "%J%\log.tmp"
lake build >> "%J%\log.tmp" 2>&1
echo BUILD EXIT CODE !ERRORLEVEL! >> "%J%\log.tmp"
if not exist "%J%\check.lean" goto :nocheck
copy /Y "%J%\check.lean" "%DEST%\JobCheck.lean" >nul
echo ===== check file >> "%J%\log.tmp"
lake env lean JobCheck.lean >> "%J%\log.tmp" 2>&1
echo CHECK EXIT CODE !ERRORLEVEL! >> "%J%\log.tmp"
:nocheck
popd
move /Y "%J%\log.tmp" "%J%\log.txt" >nul
echo done> "%J%\DONE"
echo [%TIME%] finished job %~nx1
goto :eof

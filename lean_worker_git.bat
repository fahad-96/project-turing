@echo off
setlocal EnableExtensions EnableDelayedExpansion
title Lean worker GIT - leave this window open
rem Lean worker with a Git-based job queue.
rem Builds jobs from two roots, ONE job at a time:
rem   1. legacy  D:\lean\TuringTask\_jobs\<job>\   (same behaviour as lean_worker.bat)
rem   2. repo    <this folder>\jobs\<job>\          (synced with GitHub)
rem Every ~15 s: git add -A, commit, pull --rebase --autostash, push.
rem Never force-pushes, never resets, never deletes files.
rem Do NOT run this together with lean_worker.bat.
set "DEST=D:\lean\TuringTask"
set "JOBS=%DEST%\_jobs"
set "REPO=%~dp0"
if "%REPO:~-1%"=="\" set "REPO=%REPO:~0,-1%"
set "RJOBS=%REPO%\jobs"
set "CONFLICT=%REPO%\WORKER_GIT_CONFLICT.txt"
set "GITOUT=%TEMP%\lean_worker_git_out.txt"
set "GIT_TERMINAL_PROMPT=0"
set "PATH=%USERPROFILE%\.elan\bin;%PATH%"
set "SELF=%~f0"
if "%~1"==":heartbeat" goto :heartbeat
if not exist "%DEST%\lakefile.toml" goto :noproject
if not exist "%REPO%\.git" goto :norepo
where git >nul 2>&1
if errorlevel 1 goto :nogit
rem refuse to start if another Lean worker window is already running
powershell -NoProfile -Command "$me=(Get-CimInstance Win32_Process -Filter ('ProcessId='+$PID)).ParentProcessId; exit @(Get-CimInstance Win32_Process -Filter 'Name=''cmd.exe''' | Where-Object { $_.ProcessId -ne $me -and $_.CommandLine -like '*lean_worker*.bat*' -and $_.CommandLine -notlike '*:heartbeat*' }).Count"
if not errorlevel 1 goto :start
echo Another Lean worker window - lean_worker.bat or lean_worker_git.bat - is already running.
echo Close it first: two workers must never build at the same time.
pause
exit /b 1

:start
if not exist "%JOBS%" mkdir "%JOBS%"
if not exist "%RJOBS%" mkdir "%RJOBS%"
echo Lean worker GIT is running.
echo It builds the Lean jobs that Claude places in
echo   %JOBS%
echo   %RJOBS%   - synced with GitHub
echo and writes each result to a log file there. One job at a time.
echo Every 15 s it commits, pulls and pushes this repository.
echo Leave this window open while you work with Claude. Close it to stop.
echo Do not run lean_worker.bat at the same time.
echo.
del "%TEMP%\lean_worker_git_busy_*.flag" >nul 2>&1
set /a TICK=3
set /a HB=40
set /a CWARN=0
set /a PW=0
set /a PLFAIL=0
set /a PSFAIL=0
:loop
set "OTHER="
for /d %%J in ("%JOBS%\*") do (
  if exist "%%J\READY" if not exist "%%J\DONE" call :job legacy "%%J"
)
for /d %%J in ("%RJOBS%\*") do (
  if exist "%%J\READY" if not exist "%%J\DONE" call :job repo "%%J"
)
echo worker alive %DATE% %TIME% > "%JOBS%\worker_alive.txt"
if defined OTHER echo PAUSED %DATE% %TIME% - lean_worker.bat is also running on %COMPUTERNAME%; close that window> "%RJOBS%\worker_alive.txt"
if not defined OTHER echo worker alive %DATE% %TIME% - lean_worker_git.bat on %COMPUTERNAME%> "%RJOBS%\worker_alive.txt"
set /a TICK+=1
if !TICK! GEQ 3 (
  set /a TICK=0
  call :gitsync "sync !DATE! !TIME!"
)
timeout /t 5 /nobreak >nul
goto :loop

:noproject
echo %DEST% not found.
pause
exit /b 1

:norepo
echo %REPO% is not a Git repository.
pause
exit /b 1

:nogit
echo git was not found on PATH. Install Git for Windows: winget install --id Git.Git
pause
exit /b 1

rem ---------------------------------------------------------------------
rem one pending job (%1 = legacy or repo, %2 = job folder).
rem Never starts a build while another worker window is open, and keeps
rem the legacy worker_alive.txt fresh while the build runs.
:job
if defined OTHER goto :eof
call :otherworker
if defined OTHER goto :paused
set /a PW=0
set "BUSY=%TEMP%\lean_worker_git_busy_%RANDOM%%RANDOM%.flag"
echo busy> "%BUSY%"
start "" /b cmd /c ""%SELF%" :heartbeat "%BUSY%""
if "%~1"=="repo" call :runrepo "%~2"
if not "%~1"=="repo" call :run "%~2"
del "%BUSY%" >nul 2>&1
goto :eof

:paused
set /a PW+=1
if !PW! EQU 1 (
  color 6F
  echo.
  echo ##########################################################################
  echo ##  PAUSED: another Lean worker window - lean_worker.bat - is open.     ##
  echo ##  Not building %~nx2
  echo ##  Close the other window; this one continues by itself.              ##
  echo ##########################################################################
  echo.
)
if !PW! GEQ 60 set /a PW=0
goto :eof

rem sets OTHER=1 when another worker window (not this one) is running
:otherworker
set "OTHER="
powershell -NoProfile -Command "$me=(Get-CimInstance Win32_Process -Filter ('ProcessId='+$PID)).ParentProcessId; exit @(Get-CimInstance Win32_Process -Filter 'Name=''cmd.exe''' | Where-Object { $_.ProcessId -ne $me -and $_.CommandLine -like '*lean_worker*.bat*' -and $_.CommandLine -notlike '*:heartbeat*' }).Count"
if errorlevel 1 set "OTHER=1"
if not defined OTHER if !PW! NEQ 0 color 07
goto :eof

rem background helper: refreshes the legacy worker_alive.txt every 5 s
rem while the build named by the flag file %2 is running
:heartbeat
if not exist "%~2" exit
echo worker alive %DATE% %TIME% > "%JOBS%\worker_alive.txt"
ping -n 6 127.0.0.1 >nul
goto :heartbeat

rem ---------------------------------------------------------------------
rem repo job: announce on GitHub, build exactly like the legacy worker,
rem then push the log back.
:runrepo
set "RJ=%~nx1"
echo building job %RJ% since %DATE% %TIME% - lean_worker_git.bat on %COMPUTERNAME%> "%RJOBS%\worker_alive.txt"
set /a HB=40
call :gitsync "worker: %RJ% started"
if not exist "%~1\READY" goto :eof
if exist "%~1\DONE" goto :eof
call :run "%~1"
echo worker alive %DATE% %TIME% - lean_worker_git.bat on %COMPUTERNAME%> "%RJOBS%\worker_alive.txt"
set /a HB=40
call :gitsync "worker: %RJ% done"
goto :eof

rem ---------------------------------------------------------------------
rem build one job - identical to lean_worker.bat
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

rem ---------------------------------------------------------------------
rem commit local changes, pull --rebase --autostash, push.
rem jobs/worker_alive.txt is committed only about every 10 minutes
rem (or with a job start/finish) so the history stays readable.
:gitsync
set "GMSG=%~1"
pushd "%REPO%"
git add -A -- . ":(exclude)jobs/worker_alive.txt" >nul 2>&1
set /a HB+=1
if !HB! GEQ 40 (
  set /a HB=0
  git add -- "jobs/worker_alive.txt" >nul 2>&1
)
git diff --cached --quiet
if errorlevel 1 git commit -q -m "%GMSG%" >nul 2>&1
if exist "%CONFLICT%" goto :gitconflictmode
if !CWARN! NEQ 0 (
  set /a CWARN=0
  color 07
  echo [%TIME%] WORKER_GIT_CONFLICT.txt removed - pushing and pulling again
)
git pull --rebase --autostash -q > "%GITOUT%" 2>&1
if errorlevel 1 goto :pullfail
set /a PLFAIL=0
set "AHEAD=0"
for /f %%N in ('git rev-list --count @{u}..HEAD 2^>nul') do set "AHEAD=%%N"
if "%AHEAD%"=="0" goto :gitend
git push -q > "%GITOUT%" 2>&1
if errorlevel 1 goto :pushfail
set /a PSFAIL=0
echo [%TIME%] pushed %AHEAD% commit(s) - %GMSG%
goto :gitend

:pullfail
set "INREBASE="
if exist "%REPO%\.git\rebase-merge" set "INREBASE=1"
if exist "%REPO%\.git\rebase-apply" set "INREBASE=1"
if defined INREBASE (
  git rebase --abort >> "%GITOUT%" 2>&1
  call :writeconflict "git pull --rebase --autostash stopped on a conflict. The rebase was aborted - nothing was lost."
  goto :gitend
)
call :isnetwork
if defined NETERR (
  echo [%TIME%] git pull failed - offline? will retry
  goto :gitend
)
rem anything else (e.g. another git command ran at the same moment): retry,
rem and only stop syncing when it fails three times in a row
set /a PLFAIL+=1
if !PLFAIL! LSS 3 (
  echo [%TIME%] git pull failed - try !PLFAIL! of 3 - will retry
  goto :gitend
)
set /a PLFAIL=0
call :writeconflict "git pull --rebase --autostash failed three times in a row."
goto :gitend

:pushfail
call :isnetwork
if defined NETERR (
  echo [%TIME%] git push failed - offline? will retry
  goto :gitend
)
findstr /i /c:"fetch first" /c:"non-fast-forward" "%GITOUT%" >nul 2>&1
if not errorlevel 1 (
  echo [%TIME%] git push rejected - GitHub moved on; will pull and retry
  goto :gitend
)
set /a PSFAIL+=1
if !PSFAIL! LSS 3 (
  echo [%TIME%] git push failed - try !PSFAIL! of 3 - will retry
  goto :gitend
)
set /a PSFAIL=0
call :writeconflict "git push failed three times in a row."
goto :gitend

:gitconflictmode
set /a CWARN+=1
if !CWARN! EQU 1 call :loud
if !CWARN! GEQ 20 (
  set /a CWARN=2
  echo [%TIME%] still NOT pushing: delete WORKER_GIT_CONFLICT.txt after fixing the repository
)
goto :gitend

:gitend
popd
goto :eof

:isnetwork
set "NETERR="
findstr /i /c:"Could not resolve host" /c:"unable to access" /c:"Failed to connect" /c:"timed out" /c:"Connection was reset" /c:"Could not read from remote" "%GITOUT%" >nul 2>&1
if not errorlevel 1 set "NETERR=1"
goto :eof

:writeconflict
> "%CONFLICT%" (
  echo WORKER_GIT_CONFLICT  %DATE% %TIME%  on %COMPUTERNAME%
  echo %~1
  echo.
  echo lean_worker_git.bat keeps building jobs and committing locally, but it does
  echo NOT pull or push until this file is deleted by hand.
  echo To fix: open a terminal in this folder, run  git pull --rebase  and resolve the
  echo conflicting files, then  git rebase --continue  and  git push.
  echo Never force-push. Then delete this file.
  echo.
  echo ----- git output -----
  type "%GITOUT%"
)
set /a CWARN=1
call :loud
goto :eof

:loud
color 4F
echo.
echo ##########################################################################
echo ##  GIT CONFLICT - the worker is NOT pushing or pulling any more.       ##
echo ##  See WORKER_GIT_CONFLICT.txt in the repository folder.               ##
echo ##  Jobs are still being built. Delete that file after fixing.          ##
echo ##########################################################################
echo.
goto :eof

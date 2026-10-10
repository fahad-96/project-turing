@echo off
setlocal EnableExtensions EnableDelayedExpansion
title Golden zip - offline check of a fresh copy
rem Emulates the review environment: Mathlib at /opt/mathlib4, dependencies linked into
rem .lake\packages (what lean-offline-init does), no network, project used exactly as zipped.
set "HERE=%~dp0"
set "T=%~1"
if "%T%"=="" set /p "T=Task number: "
set "ZIP=%HERE%tasks\task %T%\golden\golden_solution.zip"
set "LOG=%HERE%tasks\task %T%\golden\golden_offline_check_log.txt"
set "PKG=D:\lean\TuringTask\.lake\packages"
set "WORK=D:\lean\golden_check_t%T%_%RANDOM%"
set "PATH=%USERPROFILE%\.elan\bin;%PATH%"
if not exist "%ZIP%" (echo golden_solution.zip not found & pause & exit /b 1)
if not exist "%PKG%\mathlib\lakefile.lean" (echo Mathlib not found in %PKG% & pause & exit /b 1)

echo Offline check of golden_solution.zip started %DATE% %TIME% > "%LOG%"
echo [1/5] /opt/mathlib4 = the pinned Mathlib checkout (the work folder is on D:, so D:\opt\mathlib4)
if not exist "D:\opt" mkdir "D:\opt"
if not exist "D:\opt\mathlib4\lakefile.lean" (
  if exist "D:\opt\mathlib4" rmdir "D:\opt\mathlib4"
  mklink /J "D:\opt\mathlib4" "%PKG%\mathlib" >> "%LOG%" 2>&1
)
echo ===== /opt/mathlib4 commit >> "%LOG%"
git -C "D:\opt\mathlib4" rev-parse HEAD >> "%LOG%" 2>&1

echo [2/5] fresh copy of the zip in %WORK%
mkdir "%WORK%"
tar -xf "%ZIP%" -C "%WORK%" >> "%LOG%" 2>&1
echo ===== fresh folder %WORK% >> "%LOG%"
dir /b "%WORK%\golden_solution" >> "%LOG%" 2>&1
cd /d "%WORK%\golden_solution"

echo [3/5] link the local dependencies (as lean-offline-init does)
mkdir ".lake\packages"
for %%P in (plausible LeanSearchClient importGraph proofwidgets aesop Qq batteries Cli) do (
  mklink /J ".lake\packages\%%P" "%PKG%\%%P" >nul
)

echo [4/5] no network: every download is refused
set "GIT_ALLOW_PROTOCOL=file"
set "HTTP_PROXY=http://127.0.0.1:9"
set "HTTPS_PROXY=http://127.0.0.1:9"
set "ALL_PROXY=http://127.0.0.1:9"
set "GIT_TERMINAL_PROMPT=0"
echo ===== lean --version >> "%LOG%"
lean --version >> "%LOG%" 2>&1

echo [5/5] lake build, then the statement and axioms check (a few minutes)
echo ===== lake build >> "%LOG%"
lake build >> "%LOG%" 2>&1
echo BUILD EXIT CODE !ERRORLEVEL! >> "%LOG%"
echo ===== lake env lean StatementAndAxiomsCheck.lean >> "%LOG%"
lake env lean StatementAndAxiomsCheck.lean >> "%LOG%" 2>&1
echo CHECK EXIT CODE !ERRORLEVEL! >> "%LOG%"
echo ===== source files in the fresh copy >> "%LOG%"
dir /s /-c "%WORK%\golden_solution\TuringTask" >> "%LOG%" 2>&1
echo Finished %DATE% %TIME% >> "%LOG%"
echo.
echo Done. Tell Claude. The log is tasks\task %T%\golden\golden_offline_check_log.txt
pause

@echo off
setlocal EnableExtensions
title Project Turing - Lean setup

set "HERE=%~dp0"
set "SRC=%HERE%TuringTask_starter"
set "DEST=C:\lean\TuringTask"
set "ELAN_BIN=%USERPROFILE%\.elan\bin"
set "LOG=%HERE%setup_lean_status.txt"

echo Lean setup started %DATE% %TIME% > "%LOG%"

echo.
echo ============================================================
echo  Project Turing - Lean setup
echo  Installs Lean and downloads Mathlib - several GB.
echo  This can take 10 to 30 minutes. Leave this window open.
echo ============================================================
echo.

echo [1/7] Checking Git...
where git >nul 2>&1
if not "%ERRORLEVEL%"=="0" goto :nogit
echo STEP 1 git: OK >> "%LOG%"

echo [2/7] Installing elan, the Lean version manager...
if exist "%ELAN_BIN%\elan.exe" goto :haveelan
curl -sSfL -o "%TEMP%\elan-init.ps1" https://elan.lean-lang.org/elan-init.ps1
if not "%ERRORLEVEL%"=="0" goto :noelan
powershell -NoProfile -ExecutionPolicy Bypass -Command "& '%TEMP%\elan-init.ps1' -NoPrompt 1 -DefaultToolchain none"
del "%TEMP%\elan-init.ps1" >nul 2>&1
:haveelan
if not exist "%ELAN_BIN%\lake.exe" goto :noelan
echo STEP 2 elan: OK >> "%LOG%"
set "PATH=%ELAN_BIN%;%PATH%"

echo [3/7] Creating the project folder %DEST% ...
if exist "%DEST%\lakefile.toml" goto :havecopy
if not exist "%SRC%\lakefile.toml" goto :nocopy
xcopy "%SRC%" "%DEST%\" /E /I /Y >nul
if not "%ERRORLEVEL%"=="0" goto :nocopy
:havecopy
echo STEP 3 copy: OK >> "%LOG%"

cd /d "%DEST%"
rem Allow long file paths for git during this run only. Does not change your git settings.
set GIT_CONFIG_COUNT=1
set GIT_CONFIG_KEY_0=core.longpaths
set GIT_CONFIG_VALUE_0=true

echo [4/7] Installing Lean v4.33.0-rc1 and checking that Windows lets it run...
lean --version
if not "%ERRORLEVEL%"=="0" goto :blocked
lean --version | findstr /C:"4.33.0-rc1" >nul
if not "%ERRORLEVEL%"=="0" goto :blocked
echo STEP 4 lean runs: OK >> "%LOG%"

echo [5/7] Downloading Mathlib at the pinned commit...
lake update
if not "%ERRORLEVEL%"=="0" goto :noupdate
if not exist ".lake\packages\mathlib\Mathlib.lean" goto :noupdate
echo STEP 5 lake update: OK >> "%LOG%"

echo [6/7] Downloading the prebuilt Mathlib cache...
lake exe cache get
if not "%ERRORLEVEL%"=="0" goto :nocache
echo STEP 6 cache get: OK >> "%LOG%"

echo [7/7] Building the test file...
lake build
if not "%ERRORLEVEL%"=="0" goto :nobuild
echo STEP 7 lake build: OK >> "%LOG%"

echo --- lean version >> "%LOG%"
lean --version >> "%LOG%" 2>&1
echo --- lean-toolchain file >> "%LOG%"
type lean-toolchain >> "%LOG%" 2>&1
echo --- mathlib commit >> "%LOG%"
git -C .lake\packages\mathlib rev-parse HEAD >> "%LOG%" 2>&1
echo RESULT: SUCCESS >> "%LOG%"

echo.
echo ============================================================
echo  SUCCESS. Lean is ready in %DEST%
echo  You can close this window and tell Claude it finished.
echo ============================================================
pause
exit /b 0

:blocked
echo STEP 4 lean runs: FAILED - exit code %ERRORLEVEL% >> "%LOG%"
echo.
echo  Windows did not let Lean run. If a "Bad Image" box appeared,
echo  Smart App Control is blocking Lean. Tell Claude.
goto :fail
:nogit
echo STEP 1 git: FAILED - git not found >> "%LOG%"
goto :fail
:noelan
echo STEP 2 elan: FAILED >> "%LOG%"
goto :fail
:nocopy
echo STEP 3 copy: FAILED >> "%LOG%"
goto :fail
:noupdate
echo STEP 5 lake update: FAILED - exit code %ERRORLEVEL% >> "%LOG%"
goto :fail
:nocache
echo STEP 6 cache get: FAILED - exit code %ERRORLEVEL% >> "%LOG%"
goto :fail
:nobuild
echo STEP 7 lake build: FAILED - exit code %ERRORLEVEL% >> "%LOG%"
goto :fail

:fail
echo RESULT: FAILED >> "%LOG%"
echo.
echo ============================================================
echo  SETUP DID NOT FINISH.
echo  Take a screenshot of this window and send it to Claude.
echo ============================================================
pause
exit /b 1

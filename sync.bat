@echo off
setlocal EnableExtensions
title Project Turing - sync with GitHub
rem One-click sync: commit everything, pull --rebase --autostash, push.
rem Use it when lean_worker_git.bat is NOT running (the worker syncs by itself).
rem Never force-pushes, never resets, never deletes files.
cd /d "%~dp0"
set "GIT_TERMINAL_PROMPT=0"
echo Syncing %CD% with GitHub ...
echo.
git add -A
git diff --cached --quiet
if errorlevel 1 goto :commit
echo No local changes to commit.
goto :pull

:commit
git commit -q -m "sync %DATE% %TIME%"
if errorlevel 1 goto :fail
echo Committed: sync %DATE% %TIME%

:pull
git pull --rebase --autostash
if errorlevel 1 goto :pullfail
git push
if errorlevel 1 goto :fail
echo.
echo OK - this folder and GitHub are in sync. Latest commit:
git log -1 --format="  %%h  %%s"
echo.
pause
exit /b 0

:pullfail
if exist ".git\rebase-merge" goto :conflict
if exist ".git\rebase-apply" goto :conflict
goto :fail

:conflict
git rebase --abort
echo.
echo ##################################################################
echo ##  CONFLICT: GitHub and this folder changed the same file.     ##
echo ##  The pull was undone; nothing was lost and nothing pushed.   ##
echo ##  Ask Claude to resolve it, or run  git pull --rebase  in     ##
echo ##  this folder and fix the files by hand. Never force-push.    ##
echo ##################################################################
echo.
pause
exit /b 1

:fail
echo.
echo SYNC FAILED - see the messages above. Nothing was deleted.
echo If you are offline, just run sync.bat again later.
echo.
pause
exit /b 1

# Project Turing - repository protocol

Repository (PRIVATE): https://github.com/fahad-96/project-turing
Default branch: `main`

    git clone https://github.com/fahad-96/project-turing.git

Laptop copy (the working folder, repository root):
`D:\HandShake\project turing\Project Turing` on the Honor laptop "fahad".
It became a Git repository on 10 Oct 2026; nothing was moved or renamed.

## 1. Rules for every Claude chat

1. Clone or `git pull --rebase` BEFORE reading or editing anything. The
   files on GitHub are the truth; a stale copy is not.
2. Commit with a message that names the task, e.g.
   `task 13: golden explanation v2` or `tracker: task 14 row updated`.
3. Push immediately after each logical change (`git push`). Do not sit on
   local commits; the laptop worker commits and pushes every ~15 s.
4. Conflicts are resolved by the chat that pulls: `git pull --rebase`, fix
   the conflicting files by hand keeping BOTH sides' content where it makes
   sense, `git add`, `git rebase --continue`, `git push`.
   Never overwrite someone else's change to make a conflict go away.
5. Never force-push, never `git reset --hard`, never rewrite history, never
   delete or rename the user's files unless the user asks in chat.
6. Everything written into the repository is pure ASCII.

## 2. Line endings and binary files

`.gitattributes` contains the single line `* -text` and the laptop repo has
`core.autocrlf false`. Git therefore never converts line endings: Lean files,
golden zips and model output zips round-trip byte for byte (they are compared
by sha256). In a fresh clone also run

    git config core.autocrlf false

and do not "normalise" line endings in any file.

## 3. What is ignored (.gitignore)

`__pycache__/`, `*.pyc`, `.lake/`, `*.olean`, `*.ilean`, `*.tmp`, `log.tmp`,
`Thumbs.db`, `desktop.ini`, `WORKER_GIT_CONFLICT.txt` (local worker state).
Everything else is committed: documents, scripts, generators, prompts,
Lean files, logs, model output zips, golden zips.

## 4. Lean build queue (jobs/)

The Lean project lives OUTSIDE the repository at `D:\lean\TuringTask`
(toolchain leanprover/lean4:v4.33.0-rc1, Mathlib 9944fe2973b8dc0b86949101ed98232c07cd54a0,
cache in .lake - never touch .lake).

A chat that can reach only GitHub submits a build like this:

    jobs/<NNN_name>/src/TuringTask/*.lean    required
    jobs/<NNN_name>/src/TuringTask.lean      optional root module
    jobs/<NNN_name>/check.lean               optional, run as JobCheck.lean
    jobs/<NNN_name>/READY                    empty file, ADD IT LAST

Commit and push; then `git pull` every minute or so until
`jobs/<NNN_name>/DONE` and `log.txt` arrive. The log ends with
`BUILD EXIT CODE n` and (with a check file) `CHECK EXIT CODE n`; 0 = ok.
Full details: `jobs/README.md`. Use a new folder name for every job; never
edit a folder that already has DONE.

`jobs/worker_alive.txt` on GitHub shows the worker's last heartbeat (pushed
about every 10 minutes and at every job start/finish). If it is older than
~15 minutes and does not say "building job", the worker is not running:
ask the user to double-click `lean_worker_git.bat`.

## 5. The worker script (there is only one)

- `lean_worker_git.bat` - THE ONLY WORKER. Double-click to start; leave the
  window open. It serves both queues, one job at a time:
  the legacy local queue `D:\lean\TuringTask\_jobs\` (unchanged behaviour)
  and the repository queue `jobs\`. Every ~15 s it runs
  `git add -A`, commits ("sync <date time>", or "worker: <job> started/done"),
  `git pull --rebase --autostash`, `git push`. So model output zips dropped
  into `tasks\task N\model_outputs\` are pushed automatically.
  On a real conflict it runs `git rebase --abort`, writes
  `WORKER_GIT_CONFLICT.txt` (with the git output), turns the window red and
  keeps building jobs and committing locally WITHOUT pulling or pushing until
  that file is deleted by hand (after resolving: `git pull --rebase`, fix,
  `git rebase --continue`, `git push`). Being offline is not a conflict; it
  just retries, and any other git failure is retried three times before the
  conflict file is written. While the worker is running do NOT run git
  commands by hand in the laptop folder (two git commands at the same moment
  can fail): just edit files and let the worker commit, or work in a separate
  clone and push. It refuses to start if another worker window is open, and
  before every job it checks again: if the retired worker is also open it turns
  yellow, builds nothing (PAUSED) and continues by itself once that window is
  closed. While a build runs it keeps the legacy `_jobs\worker_alive.txt`
  fresh every 5 s, so a long build does not look like a dead worker.
  A long build is never a reason to start another worker.
- `lean_worker.bat` is RETIRED (10 Oct 2026). The file was renamed to
  `lean_worker_OLD_do_not_run.bat` and is kept for reference only. Do not run
  it and do not rename it back (two Mathlib builds must never run in parallel
  on this laptop). Where an older document or prompt says "start
  lean_worker.bat", start `lean_worker_git.bat` instead.

Changing `lean_worker_git.bat` itself: cmd reads a running batch file from
disk, so a pulled change to it can confuse the running worker. Close the
worker window, pull, then start it again.

## 6. sync.bat (for the user)

Double-click when lean_worker_git.bat is NOT running: `git add -A`, commit
"sync <date time>" if anything changed, `git pull --rebase --autostash`,
`git push`, shows the result and waits for a key. On a conflict it aborts the
rebase (nothing lost, nothing pushed) and says so. While the worker runs it is
not needed - the worker syncs every 15 s.

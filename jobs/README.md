# jobs/ - Git-based Lean build queue

`lean_worker_git.bat` (running on the laptop "fahad") builds every job folder
in this directory, one at a time, and pushes the result back to GitHub.
A Claude chat that can only reach GitHub submits a job by pushing a folder
here and pulling until `DONE` appears.

## Job folder layout

    jobs/<NNN_name>/
      src/TuringTask/*.lean     required - copied over D:\lean\TuringTask\TuringTask\
      src/TuringTask.lean       optional - root module; default is "import TuringTask.Basic"
      check.lean                optional - run with "lake env lean JobCheck.lean" after the build
      READY                     empty file - ADD IT LAST
      log.txt                   written by the worker (build output, exit codes)
      DONE                      written by the worker when log.txt is complete

Use a new, unique folder name for every job (e.g. `021a_t12_r1`, numbered
like the legacy queue). Never reuse or edit a folder that already has `DONE`;
make a new one instead.

## Rule: READY last

The worker builds any folder that contains `READY` and no `DONE`. So commit
and push the sources first, or put `READY` in the same commit as the sources,
never before them. A job without `READY` is ignored.

## What the worker does

1. `git pull` (every ~15 s) brings the job in.
2. Commits and pushes "worker: <job> started" (jobs/worker_alive.txt says
   "building job <job> since ...").
3. Replaces D:\lean\TuringTask\TuringTask\ with src/TuringTask, runs
   `lake build`, then `lake env lean JobCheck.lean` if check.lean exists.
   Output goes to log.tmp (not committed) and is renamed to log.txt.
4. Writes `DONE`, commits "worker: <job> done" and pushes.

The log ends with `BUILD EXIT CODE n` and, with a check file,
`CHECK EXIT CODE n` (0 = success). A first build after a long idle
can take about 10 minutes; later ones are faster.

## worker_alive.txt

`jobs/worker_alive.txt` is rewritten every loop and committed about every
10 minutes and at every job start/finish. If its time stamp on GitHub is
older than about 15 minutes and it does not say "building job", the worker
is probably not running - ask the user to double-click lean_worker_git.bat.

## Legacy queue

`D:\lean\TuringTask\_jobs\` (local only, not in Git) uses the same layout
and is still served by both lean_worker.bat and lean_worker_git.bat.
Only one of the two workers may run at a time.

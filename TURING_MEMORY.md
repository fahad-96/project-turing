The project folder is a Git repository (see REPO_PROTOCOL.md); pull before editing, push after
# Project Turing - compact memory (read this first, then TURING_HANDOFF_2026-10-06.md)

Last updated: 10 Oct 2026, about 08:20 IST: task 13 golden built and worker-verified (jobs 027a/027b); offline check pending.

NEW ACCOUNT (9 Oct): read `TURING_PLAYBOOK.md` first (complete method and templates). The tracker is now
the file `TURING_TRACKER_EXPORT.md` (the artifact below belongs to the old account).

OLD TRACKER (old account only): the artifact "Turing Task Tracker"
(https://claude.ai/artifact/J1dRbUWM7fSRbdhS73YVhM). Its rows (all tasks on both laptops), reviews and
rules are exported to `TURING_TRACKER_EXPORT.md`. Reserve the next free task number in the export
before creating files and update the row after every step. Task 7 exists on both laptops; the Honor
laptop's task 7 is listed as 7.5.

## The job
Handshake AI, Project Turing: Lean 4 proof-writing tasks. Per task: prompt -> platform runs 3 models
-> at least one genuine failure -> own golden zip + step-by-step explanation -> rubric CSV
(5-20 binary items, weight +1). Targets: golden >= 90 percent, at least 1 of 3 outputs < 40 percent.
Pinned: Lean `leanprover/lean4:v4.33.0-rc1`, Mathlib `9944fe2973b8dc0b86949101ed98232c07cd54a0`.

## The fellow's standing rules
- Do things yourself; keep his manual steps minimal, but ask for a manual step when it saves a
  long wait (for example starting `lean_worker_git.bat`).
- No long silent waits. Say what is running; hand over each file as soon as it is usable.
- Everything for a submission field is pure ASCII.
- Prompts short, neutral names, no hints about the proof method.
- Be brief; say plainly what is verified and what is not. Aim at 5/5 from the reviewer.
- Never promise a model failure or a reviewer score.
- The golden is written only after a failure is confirmed and never copies a model output.

## Reviewer rules (task 5 feedback, 8 Oct) - apply to every golden and rubric
1. Golden zip: `lakefile.toml` requires mathlib with `path = "/opt/mathlib4"`; `lake-manifest.json`
   in model-output format (copy a model output's manifest, change only "name").
2. Extract the FINAL zip into a fresh folder and run `lake build` and
   `lake env lean StatementAndAxiomsCheck.lean` offline (script `verify_golden_offline_t6.bat`:
   change ZIP and LOG paths; junction `C:\opt\mathlib4` already exists).
3. Rubric: one +1 build item (pinned versions, build includes `TuringTask/Basic.lean`).
4. Definition items and proof items are separate; each says what it does NOT judge.
5. Rerun grading for golden and all evaluated responses after any rubric change.
6. Arithmetic: 1 build + k definitions + 5 theorems. A sorry-only output scores (1+k)/(6+k).
   With k = 0: proving one theorem gives 33 percent; with k = 1 it gives 43 percent (too high).
   Prefer prompts without definitions, or one definition at most.
Rubric CSV: header `"ID","Criterion","Weight"`, all fields quoted, LF, no trailing newline.

## Machines
- Laptop "fahad" (Honor): folder `D:\HandShake\project turing\Project Turing`; Lean in
  `D:\lean\TuringTask` since 8 Oct 22:40 (moved from C:, which was full; `finish_move.bat` links
  C:\lean\TuringTask, C:\opt\mathlib4 and D:\opt\mathlib4 to it). Fresh-copy check of a golden zip:
  `verify_golden_offline.bat <task number>` (works on D:, uses D:\opt\mathlib4).
  The only worker is `lean_worker_git.bat`; `lean_worker.bat` is retired (renamed
  `lean_worker_OLD_do_not_run.bat`, do not run it). It watches `D:\lean\TuringTask\_jobs\<job>\`
  (src\TuringTask\*.lean, optional src\TuringTask.lean, check.lean, READY written LAST in a separate
  commit; result log.txt + DONE). Warm build about 25 s per file, cold first build 500-730 s.
  NEVER build several Mathlib-importing files in parallel here (memory error, stale check output):
  one import chain, or one job per file with a stub TuringTask.lean.
- The PC shell (device_bash) does not start on this laptop: use stage/commit only.
- Warm worker: about 25 s per Mathlib-importing file, so golden iteration through worker jobs is
  2-3 min per round. If a build fails, the check part of the log shows STALE results.
- Before writing a golden, scan for shared lines with the model outputs (decl names, long lines)
  and never build on an earlier draft that shares names or lines with a model output.
- Drive C: was nearly full on 8 Oct (that broke jobs 009, 009b, 010); keep Lean data on D:.
- Cloud workspace (per chat, lost later): pinned Lean in /home/claude/lean, partial Mathlib build in
  /home/claude/work/mathlib, benchmark clones in /home/claude/work/bench. pip is blocked.

## Generators
One self-checking Python generator per task (`tasks\task N\turing_tN_generator.py`) writes the
prompt, `TuringTask\Basic.lean`, `StatementAndAxiomsCheck.lean`, `check_outputs.bat`, asserts ASCII
and Lean lines <= 100 chars. Use `_explicit_args` (top-level binders only) in check_source; the old
regex picked up `(p : Int)` inside binder types (task 7 bug, fixed).

## Novelty hazards (check every topic)
Mathlib at the pinned commit; PutnamBench, miniF2F, ProofNet, compfiles, formal-conjectures;
`TauCetiProject/TauCeti` (11,600 AI-written files, grows daily); `tomdif/RamanujanLean` (q-series,
sums of two and four squares - this whole family is off limits); `AxiomMath/RogersRamanujan`;
`riccardobrasca/KummerCriterion` (Kummer congruences, Voronoi, quadratic Gauss sum sign, h^-, L-values -
Bernoulli congruences are off limits); `leanprover-community/flt-regular`.
NEW (9 Oct): `AllenGrahamHart/FormalConjectures-Bench` (29,000+ Lean files, AI-written solutions of
"research solved" statements; has Sylvester-Schur and Wolstenholme: both OFF LIMITS). Clone it shallow
and grep it for every topic. Also in Mathlib: Lucas-Lehmer necessity, Kronecker's theorem on roots of
unity in the unit disc (NumberField.Embeddings.pow_eq_one_of_norm_le_one, MahlerMeasure.lean).
Mathlib already has: von Staudt-Clausen, Jacobi sums with `J = -1 + z (mu - 1)^2`,
degrees of irreducible factors of cyclotomic polynomials mod p, Burnside, Dirichlet's theorem.

## What fails the models
Elementary or glue work (tasks 1-3: determinants, Farey) was solved by all three models.
Failures came when every theorem needs one missing classical core (task 4 Jacobi identity: 2 of 3
failed; task 6 sign of the quadratic Gauss sum: 1 failed, 1 passed with 2,868 lines).
Choose a single hard core that all five statements need; avoid statements a model can prove
independently of the core.
Task 11 (local lemma + 5 applications) was solved by all three models (836-1,217 lines): a
self-contained probabilistic/counting core is not hard enough.
Task 7.5 (Jacobsthal sums, p = 1 mod 4) was solved by all three models (1,126-1,781 lines): a
character-sum evaluation whose core is finite-field manipulation (substitutions, orbit counting,
Euler's criterion) is not hard enough either. Post-mortem (playbook 4.1): no wording leak; (1) the
missing core had a 20-line textbook proof and Mathlib supplied the rest; (2) the five statements
were the textbook's ladder of lemmas (1 and 3 prove 2; 2 and 3 give 4 and 5), so the prompt handed
over the plan. Before every new prompt apply the playbook 4.1 hardness checklist: short-core,
ladder, textbook, Mathlib-assist and finite-manipulation tests; reject on two "yes" answers.
Length never fails the models (they write 1,000-2,900 lines in 6 h); only a missing idea does.
Task 10 (Zsigmondy) is the best result: two genuine failures, third rollout died. Its core mixes
cyclotomic algebra, p-adic valuations, real estimates and exceptional cases.

## Task status (8 Oct 2026, 18:00 IST)
- 1, 2, 3: rejected (no failure).
- 4: submitted (golden 100, responses 29/29).
- 5: returned by reviewer (minor issue), the fellow is fixing it.
- 6: golden and 8-item rubric fixed to the reviewer rules, offline fresh-copy check passed; waiting
  for the fellow's platform rerun verdicts; response 2 not received.
- 7 = tracker 7.5 (cubic character sum mod p, Jacobsthal): 9 Oct - all three models PASSED
  (official jobs 018a-c: 1,781 / 1,126 / 1,302 lines, build 0, check 0, standard axioms).
  REJECTED, no golden. Handoff section 30.
- 8 (equidistribution, Weyl): v1 (job 007, linear case as theorem 1) was never run and is superseded.
  v2 (9 Oct, job 018d): all five theorems need the quadratic / polynomial case (uniform {n^2 x},
  polynomial with irrational leading coefficient, digits of 2^(n^2), mean |sin n^2|, mean cos(n^2 x)).
  10 Oct 14:06 IST - R1 GENUINE FAILURE (64 lines; declares TuringTask.abs := 0 and
  TuringTask.Filter.Tendsto := True, so the statements change; job t8_r1_check: build 0, check 1),
  R2 PASS (1,740 lines, t8_r2_check), R3 PASS (1,754 lines; t8_r3_check hit the parallel-build olean
  error, sequential reruns t8_r3_rerun_1..4 pass). GOLDEN BUILT (own route, cloud loop about 1 h):
  7 files, 1,177 lines, job t8_golden_01 build 0, no warnings, check 0, standard axioms;
  tasks\task 8\golden has zip + generator + explanation + 6-item rubric (proof items also require the
  statement's names to be Mathlib's, because of R1). Expected golden 6/6, R1 1/6 = 17, R2 and R3 6/6.
  Offline check (verify_golden_offline.bat 8) PASSED 14:16 IST; the fellow reported the platform steps
  done 14:19 IST (verdicts and submit status not yet recorded). Handoff section 38.
  Lessons: a model may "prove" the statements by shadowing Mathlib names inside the namespace; only
  the check file catches it, so the rubric must name it. A model output whose modules do not form one
  chain fails on the laptop with 'failed to read ...olean.private': rerun one module per job.
- 9 (cubes mod p, Gauss/Jacobi): prompt compiled officially (job 008), handed over 8 Oct.
- 9 (cubes mod p): 9 Oct - R3 genuine failure (all five theorems absent), R1 and R2 pass. Golden
  (5 files, 899 lines) built officially (job 012g) and passed the fresh-copy offline check;
  6-item rubric; expected golden 100, R3 17 percent. Ready for the platform. Handoff section 25.
- 11 (local lemma): 9 Oct - all three models passed (official jobs 013a-c), REJECTED, no golden.
  Handoff section 26.
- 10 (Zsigmondy): 9 Oct - R1 FAIL (sorry, job 014a), R2 rollout failed, R3 FAIL (theorems absent,
  job 014b). Golden (7 files, 1,017 lines) built by job 016c, no warnings; 6-item rubric; expected
  golden 100, R1 and R3 17 percent. SUBMITTED 9 Oct about 17:40 IST WITHOUT the fresh-copy offline
  check (run `verify_golden_offline.bat 10` if the review asks). Handoff section 27.
- 12 (new prime factors of Fibonacci and Lucas numbers, Carmichael) and 13 (resultants and
  discriminants of cyclotomic polynomials, Apostol): prompts compiled officially 9 Oct (jobs 017a,
  017b: build 0, five sorry warnings, check 0), novelty checked (nothing in Lean anywhere), handed
  over 9 Oct about 19:30 IST. Task 13 risk: Mathlib's resultant API is rich (resultant_eq_prod_eval,
  isUnit_resultant_iff_isCoprime, resultant_deriv). Plans in handoff section 29.
- 12 (Fibonacci/Lucas primitive divisors, Carmichael): 9 Oct 21:10 - R1 FAIL (sorry in the two
  core theorems, job 019a), R3 FAIL (empty proofs, build error, job 019c), R2 still running. Golden
  (8 files, 2,017 lines) built officially by job 020a (23:55 IST, no warnings, standard axioms);
  6-item rubric; expected golden 100, R1 17, R3 0. Fresh-copy offline check pending, then the
  platform. Handoff section 32.
- CLOUD LEAN (9 Oct): the laptop's prebuilt oleans can be packed with pack_oleans_for_cloud.bat,
  pack_oleans_server_for_cloud.bat and pack_oleans_ir_for_cloud.bat (chunks in D:\lean\_xfer, 2.2 GB,
  reusable) and staged into a chat; with lean-4.33.0-rc1-linux.zip from GitHub, `import Mathlib`
  then compiles in about 9 s there. Playbook section 3.3. The worker and verify_golden_offline.bat
  stay the official checks.
- 13 (cyclotomic resultants): 10 Oct 00:05 - R3 GENUINE FAILURE (no theorems, job 020c), R1 and R2 PASS
  (jobs 020a, 020b). 10 Oct 08:10 - GOLDEN BUILT (own route: fibre lemma via ZMod.unitsMap, reduction
  mod q for theorem 1, recursion for Res(Phi_n, Psi_n) for the discriminant), 949 lines in 4 files,
  worker jobs 027a (cold 779 s) and 027b pass, no warnings, standard axioms; tasks\task 13\golden has
  zip + generator + explanation + rubric. Written in the cloud Lean loop in about 2.5 h. Offline check
  and platform steps pending. Handoff sections 35, 36.
- 14 (average order of the divisor function, hyperbola method, Euler-Mascheroni) and 15 (Polya-Vinogradov,
  least non-residues): prompts compiled 9 Oct (jobs 018e, 018d), handed over about 20:00 IST; running.
  Handoff section 33.
- 14 (divisor function averages): 10 Oct 13:55 IST - all three models PASSED (jobs t14_r1_check,
  t14_r2_check, t14_r3_check: 1,812 / 1,255 / 1,745 lines, build 0, check 0, standard axioms). REJECTED,
  no golden. R3's root `TuringTask.lean` imports only `TuringTask.Second`, so plain `lake build` skips
  Basic.lean (packaging slip, not counted). Lesson: a textbook analytic estimate (hyperbola method) with
  Mathlib's Euler-Mascheroni bounds is within reach of all three; expect the same for task 17.
  When a model's root module does not import Basic, run the check job with the default root and a
  second job with the model's root (stale oleans otherwise answer the check). Handoff section 37.
- 15 (Polya-Vinogradov, least non-residues): 10 Oct 14:27 IST - all three models PASSED (jobs t15_r1_check,
  t15_r2_check, t15_r3_check: 925 / 619 / 626 lines, build 0, check 0, standard axioms). REJECTED, no golden.
  Lesson: when Mathlib has the Gauss-sum identities, the classical inequality is a 600-900 line exercise for
  all three models (same as task 14). Handoff section 39.
- 16 (Cohn: square, twice-square, power-of-two Fibonacci and Lucas numbers) and 17 (6/pi^2 densities):
  prompts compiled 9 Oct (jobs 023a, 023b), handed over about 21:20 IST; running. Handoff section 34.
- 16 (Cohn: square Fibonacci and Lucas numbers): 10 Oct 14:57 IST - R1 FAIL (sorry in four theorems, only
  fib_eq_two_pow proved; job t16_r1_check), R3 FAIL (all five sorry, t16_r3_check), R2 PASS (1,437 lines).
  GOLDEN BUILT (own route, Cohn's shift congruences mod L(k) with Int.fib and a power-of-3 index split; cloud
  loop about 40 min): 4 files, 641 lines, job t16_golden_01 build 0, no warnings, check 0, standard axioms;
  tasks\task 16\golden has zip + generator + explanation + 6-item rubric. Expected golden 6/6, R1 2/6 = 33,
  R2 6/6, R3 1/6 = 17. Offline check PASSED 15:20 IST; platform pending. Handoff section 41.
- 17 (6/pi^2 densities): 10 Oct 15:03 IST - all three models PASSED (jobs t17_r1_check, t17_r2_check,
  t17_r3_check: 790 / 777 / 1,049 lines, build 0, check 0, standard axioms). REJECTED, no golden.
  Lesson: tasks 14, 15 and 17 (classical analytic estimates whose core Mathlib supplies: zeta(2), Moebius
  inversion, Euler-Mascheroni bounds, Gauss sums) were all solved by all three. Handoff section 40.
- 22 (x^3 + y^3 = 2z^3 only trivially; rational points of y^2 = x^3 + 1 and y^2 = x^3 - 27; x^3 - 2y^3 = +-1;
  triangular cubes) and 23 (Stormer: n(n+1) and x^2 - 1 7-smooth, x^2 + 1 13-smooth up to 239, x^2 - 2y^2 = +-1
  with y 13-smooth up to 13860): prompts compiled 10 Oct (jobs t22_statements, t23_statements: build 0, five sorry
  warnings, check 0), handed over about 18:00 IST by the chat that cooks tasks 22-29 (18-21 belong to another
  laptop). Golden plans in handoff section 42. Novelty hazards found 10 Oct: Ramanujan-Nagell is formalized in Lean 4
  (arXiv 2604.09808); Catalan's conjecture incl. Euler's x^2 = y^3 + 1 and Ko Chao is formalized (cadamcat/catalan-lean4).
  Prompt conventions added: finite sets as `Membership.mem (S : Finset ...) a` (ASCII for a in S), divisibility as
  `N % p = 0`, and a paragraph after the Rules forbidding declarations in `TuringTask` that shadow Mathlib names.
- 24 (Pisano period pi and entry point z of the Fibonacci numbers: pi(n) <= 6n, pi(n) = 6n iff n = 2*5^j (j >= 1),
  pi(n) = n iff n = 1 or 24*5^j, z(n) = 2n iff n = 6*5^j, z(n) = n iff n = 5^j or 12*5^j) and 25 (Cohn II: F_n + 1
  square only for n = 0, 4, 6; F_n = x^2 + 1 only 1, 2, 3, 5; F_n = 2x^2 + 1 only 1, 2, 4; L_n = x^2 + 1 only 0,
  1; L_n + 1 = 2x^2 only 1, 4, 11): prompts compiled 10 Oct (jobs t24_statements, t25_statements: build 0, five
  sorry warnings, check 0), handed over about 19:55 IST by the chat that cooks tasks 22-29. Golden plans in
  handoff section 43 (task 25 reuses the task 16 golden). Lucas numbers are written additively (L_n = c as
  `Nat.fib n + c = 2 * Nat.fib (n + 1)`), no Nat subtraction. Rejected this round: Mordell equations (textbook),
  triangular F and L (Jacobi coverings incomplete).
- 26 (primes x^2 + ny^2 with one class per genus: p = x^2 + 5y^2 iff p = 5 or 1, 9 mod 20; p, q = 3, 7 mod 20 give
  pq = x^2 + 5y^2; n = 6 mod 24 {1, 7}; n = 13 mod 52; n = 21 mod 84 {1, 25, 37}) and 27 (representation numbers
  of x^2 + xy + y^2, x^2 + 3y^2, x^2 + 2y^2, x^2 + xy + 2y^2, x^2 + 7y^2 as Jacobi-symbol divisor sums): prompts
  compiled 10 Oct (jobs t26_statements, t27_statements: build 0, five sorry warnings, check 0), handed over about
  21:20 IST by the chat that cooks tasks 22-29. Golden plans in handoff section 44. Novelty hazard found: the
  cannonball problem is formalized in Lean 4 (int-y1/proofs, SquarePyramid, Anglin's proof), so the y^2 = x^3 -
  36x family is out. Counts are stated over the box Finset.Icc (-n) n with `Prod Int Int` (ASCII).
- Tracker: next free task number 18. Worker job reservations: 019 task 12 outputs, 020 task 13 outputs
  (used), 021 task 8 v2, 022 task 14, 024 task 15, 025 task 16, 026 task 17, 027 task 13 golden (used);
  next free 028.
- Next free task number: see the tracker (other chats opened tasks 13-17 on 9 Oct). Worker job
  numbers are shared by all chats: check `_jobs` before choosing one (this chat used 018a-d, 019a,
  019c, 020a_t12_golden). Handoff section 28 = handover to
  the new account, 29 = tasks 12 and 13.
- 10 (primitive prime divisors, Zsigmondy) and 11 (local lemma applications: hypergraph colouring,
  k-SAT, Ramsey and van der Waerden lower bounds): prompts made 8 Oct about 19:00 IST, worker jobs
  009 and 010. Plans in handoff section 23.
- Task 6 novelty note: KummerCriterion proves the quadratic Gauss sum sign for primes (overlaps
  theorem 3 only); add a disclosure sentence if not yet submitted.

# Project Turing - task tracker (export, replaces the old tracker artifact)

Exported 9 Oct 2026, about 17:50 IST, from the artifact "Turing Task Tracker" of the old Claude
account (https://claude.ai/artifact/J1dRbUWM7fSRbdhS73YVhM - a new account cannot open it).
From now on THIS FILE is the tracker: update the row of a task after every step (prompt,
outputs, golden, platform scores, submit, review) and keep the "Updated" line current.

Next free task number: 18 (unless the fellow says another number is taken).
Numbering note: number 7 was used on both laptops; the Honor laptop's task 7 (folder
`tasks\task 7` on the Honor laptop) is listed as 7.5.

## Summary

| No. | Title | Laptop | Status | Models | Next |
| --- | --- | --- | --- | --- | --- |
| 1 | Smith's LCM determinants | waris-pc | rejected | all passed | - |
| 2 | Circulant determinants | waris-pc | rejected | all passed | - |
| 3 | Farey neighbours | waris-pc | rejected | all passed | - |
| 4 | Congruences for coloured partitions | waris-pc chat, Honor laptop platform | submitted | R1 fail, R2 rollout failed, R3 fail | confirm submitted; if returned apply the task 5 v2 fix |
| 5 | Square and triangular sums of partition numbers | waris-pc | submitted | R1 fail, R2 rollout failed, R3 pass | awaiting re-review |
| 6 | Exponential sums over squares (sign of the quadratic Gauss sum) | Honor laptop | golden | R1 fail, R2 not received, R3 pass | platform upload and grading, then submit |
| 7 | Convolution identities for quadratic sequences | waris-pc | golden | R1 fail, R2 no output, R3 fail | platform upload and grading, then submit |
| 7.5 | Cubic character sum x^3 - c x mod p (Honor laptop's task 7) | Honor laptop | rejected | all passed (official jobs 018a-c, 9 Oct) | - |
| 8 | Fractional parts of n^2 x and polynomial values (Weyl), v2 | Honor laptop | golden | R1 fail (statements changed: declares TuringTask.abs and TuringTask.Filter.Tendsto), R2 pass, R3 pass | offline check passed; fellow reported the platform steps done 14:19 IST; record verdicts and submit status |
| 9 | Cubes modulo p (Gauss, Jacobi) | Honor laptop | golden | R1 pass, R2 pass, R3 fail | confirm submitted (cleared 9 Oct) |
| 10 | Primitive prime divisors (Zsigmondy) | Honor laptop | submitted | R1 fail, R2 rollout failed, R3 fail | await review |
| 11 | Colourings that avoid bad events (local lemma applications) | Honor laptop | rejected | all passed | - |
| 12 | New prime factors of Fibonacci and Lucas numbers (primitive divisors) | Honor laptop | golden | R1 fail (sorry), R2 running, R3 fail (empty proofs) | fresh-copy offline check, then platform upload and grading |
| 13 | Resultants and discriminants of cyclotomic polynomials | Honor laptop | golden | R1 pass, R2 pass, R3 fail (no theorems) | fresh-copy offline check (verify_golden_offline.bat 13), then platform upload and grading |
| 14 | Average order of the divisor function (Dirichlet, hyperbola method) | Honor laptop | rejected | all passed (official jobs t14_r1_check, t14_r2_check, t14_r3_check, 10 Oct) | - |
| 15 | Character sums modulo a prime (Polya-Vinogradov) and least non-residues | Honor laptop | rejected | all passed (jobs t15_r1..r3_check, 10 Oct) | - |
| 16 | Square, twice-square and power-of-two Fibonacci and Lucas numbers (Cohn) | Honor laptop | golden | R1 fail (sorry in four theorems), R2 pass, R3 fail (sorry in all five) | offline check passed; platform upload and grading, then submit |
| 17 | Densities governed by 6/pi^2: squarefree numbers, coprime pairs, Euler's function | Honor laptop | rejected | all passed (official jobs t17_r1_check, t17_r2_check, t17_r3_check, 10 Oct) | - |
| 22 | Three cubes in arithmetic progression; rational points of y^2 = x^3 + 1 and y^2 = x^3 - 27 (Euler, Legendre) | Honor laptop | prompt | not run yet | fellow pastes task22_prompt.txt; outputs to tasks\task 22\model_outputs |
| 23 | Consecutive integers without large prime factors; smooth x^2 - 1, x^2 + 1 and Pell numbers (Stormer, Lehmer) | Honor laptop | prompt | not run yet | fellow pastes task23_prompt.txt; outputs to tasks\task 23\model_outputs |
| 24 | Pisano period and entry point of the Fibonacci numbers: extremal and fixed-point values (Wall, Fulton-Morris, Salle, Freyd-Brown, Marques) | Honor laptop | prompt | not run yet | fellow pastes task24_prompt.txt; outputs to tasks\task 24\model_outputs |
| 25 | Fibonacci and Lucas numbers next to a square or twice a square (Finkelstein, Robbins; Cohn II) | Honor laptop | prompt | not run yet | fellow pastes task25_prompt.txt; outputs to tasks\task 25\model_outputs |
| 26 | Primes of the form x^2 + n y^2 with one class per genus (n = 5, 6, 13, 21) and Euler's product conjecture (Fermat, Euler, Lagrange, Gauss) | Honor laptop | prompt | not run yet | fellow pastes task26_prompt.txt; outputs to tasks\task 26\model_outputs |
| 27 | Representation numbers of five binary quadratic forms as character divisor sums (Dirichlet, Lorenz, Hall) | Honor laptop | prompt | not run yet | fellow pastes task27_prompt.txt; outputs to tasks\task 27\model_outputs |
| 28 | Quartic and octic residuacity of 2 and -4 and Dirichlet's rational quartic law (Gauss, Dirichlet, Barrucand-Cohn, E. Lehmer) | Honor laptop | prompt | not run yet | fellow pastes task28_prompt.txt; outputs to tasks\task 28\model_outputs |
| 29 | Signs of arithmetic permutations: multiplication maps, power maps and the transpose (Zolotarev, Lerch, Frobenius) | Honor laptop | prompt | not run yet | fellow pastes task29_prompt.txt; outputs to tasks\task 29\model_outputs |
| 30 | Dedekind sums: Knopp's Hecke identity, denominators, Rademacher's mod 8 law, vanishing and equality criteria | Honor laptop | prompt | not run yet | fellow pastes task30_prompt.txt; outputs to tasks\task 30\model_outputs |
| 31 | Coefficients of binary and ternary cyclotomic polynomials (Migotti, Bang, Carlitz, Lam-Leung, Kaplan, Gallot-Moree) | Honor laptop | prompt | not run yet | fellow pastes task31_prompt.txt; outputs to tasks\task 31\model_outputs |

Status values: prompt (prompt written and compiled), outputs (checking outputs), golden (golden
ready, platform pending), submitted, returned (sent back by a reviewer), rejected (no failure).

## Rows (full)

### Task 1 - Smith's LCM determinants

- Status: rejected
- State: All three models passed, no failure
- Laptop: waris-pc
- Topic: Determinants of LCM and GCD matrices, 4 theorems
- Model outputs: M1 pass, M2 pass, M3 pass
- Next: None
- Updated: 6 Oct 2026

### Task 2 - Circulant determinants

- Status: rejected
- State: All three models passed, no failure
- Laptop: waris-pc
- Topic: Closed forms for determinants of circulant matrices, 5 theorems
- Model outputs: M1 pass, M2 pass, M3 pass
- Next: None
- Updated: 7 Oct 2026

### Task 3 - Farey neighbours

- Status: rejected
- State: All three models passed, no failure
- Laptop: waris-pc
- Topic: Farey adjacency, determinant, mediant and next term, 5 theorems
- Model outputs: M1 pass, M2 pass, M3 pass
- Next: None
- Updated: 6 Oct 2026

### Task 4 - Congruences for coloured partitions

- Status: submitted
- State: Cleared to submit on 7 Oct; submission not yet confirmed here
- Laptop: waris-pc chat, Honor laptop platform
- Folder: tasks\task 4\golden
- Topic: Prime divisibility of coloured partition counts and parity of Euler-product powers; needs Jacobi's identity
- Model outputs: M1 fail (sorry), M2 rollout failed, M3 fail (skeleton only)
- Golden: turing_task4_golden.zip (sha256 a4b1a25f...), Jacobi's identity from Gaussian binomials. Old form: lakefile requires Mathlib by git.
- Rubric: 7 items (2 anchors, 5 proof items). Platform: golden 100 percent, both evaluated models 29 percent.
- Notes: May come back with the same review as task 5 (git lakefile, no build item). The fix is the task 5 v2 recipe.
- Next: Confirm it was submitted. If sent back, apply the task 5 v2 fix.
- Updated: 7 Oct 2026

### Task 5 - Square and triangular sums of partition numbers

- Status: submitted
- State: Sent back by Alexey on 8 Oct, fixed as v2, reply drafted
- Laptop: waris-pc
- Folder: tasks\task 5\golden
- Topic: 5 partition identities from Gauss's theta identities (overpartitions, distinct and odd distinct parts)
- Model outputs: M1 fail (sorry), M2 rollout failed, M3 pass
- Golden: v2 turing_task5_golden.zip (sha256 dfc700cf...), /opt/mathlib4 lakefile and environment manifest, offline fresh-extract check passed.
- Rubric: 8 items (anchors sqAlt and halfSum, 5 proof items, build item). Expected: golden 8/8, M1 3/8, M3 8/8.
- Notes: v1 had a git lakefile and definitions inside rubric items 3 and 5.
- Next: Confirm the platform rerun matches the expected scores and the reply was sent; wait for re-review.
- Updated: 8 Oct 2026

### Task 6 - Exponential sums over squares (sign of the quadratic Gauss sum)

- Status: golden
- State: Golden and 8-item rubric brought in line with Alexey's rules; fresh-copy offline check passed 8 Oct
- Laptop: Honor laptop
- Folder: tasks\task 6\golden (Honor laptop)
- Topic: Odd n: sum of e(k^2/n); triangular sum; Legendre-twisted sum; two-prime product; cotangent sum. 5 theorems, defs ex and rt
- Model outputs: M1 fail (sorry), M2 not received, M3 pass (2,868 lines)
- Golden: golden_solution.zip (sha256 b8d15537...), 6 files, /opt/mathlib4 lakefile, offline fresh-extract check passed (8671 jobs, exit 0).
- Rubric: 8 items (build, defs ex and rt, 5 proof-only items). Expected: golden 8/8, M1 3/8, M3 8/8.
- Notes: Novelty note found 8 Oct: the public repo riccardobrasca/KummerCriterion (Sep 2026) fixes the sign of the quadratic Gauss sum for primes (Schur's DFT route). Theorem 3 (sum_legendre) overlaps; theorems 1, 2, 4, 5 go beyond it. Consider one disclosure sentence in the explanation.
- Next: Upload golden_solution.zip and explanation, upload task6_rubric.csv in both rubric sections, rerun grading, compare verdicts, submit.
- Updated: 8 Oct 2026

### Task 7 - Convolution identities for quadratic sequences

- Status: golden
- State: Golden ready on 8 Oct; platform upload and grading pending
- Laptop: waris-pc
- Folder: tasks\task 7\golden
- Topic: 5 convolution identities of theta-type sequences (Jacobi triple product, Gauss, Jacobi's identity)
- Model outputs: M1 fail (sorry), M2 no output, M3 fail (simp, build error)
- Golden: turing_task7_golden.zip (sha256 312d8bb2...), 4 files, 1,465 lines, offline fresh-extract check passed, deep audit clean.
- Rubric: 8 items (anchors conv and quad, 5 proof items, build item). Expected: golden 8/8, M1 3/8, M3 2/8.
- Next: Upload zip and explanation, upload the rubric CSV in both sections, run both evaluations, then submit.
- Updated: 8 Oct 2026

### Task 7.5 - Cubic character sum x^3 - c x mod p (Honor laptop's task 7)

- Status: rejected
- State: All three models passed, no failure (9 Oct 2026, 19:35 IST). No golden written.
- Laptop: Honor laptop
- Folder: tasks\task 7 (Honor laptop)
- Topic: Jacobsthal sums for p = 1 mod 4: S(c)^2 + S(r)^2 = 4p, S(c)^2 = 4a^2, S(1) mod 8, Gauss's binomial congruence, point count of y^2 = x^3 - x. Definition csum + 5 theorems. A different task from waris-pc's task 7.
- Model outputs: R1 PASS (job 018a_t7_r1: 1,781 lines, build 0, check 0, standard axioms). R2 PASS (job 018b_t7_r2: 1,126 lines, lint warnings only, check 0, standard axioms). R3 PASS (job 018c_t7_r3: final project r3\TuringTask-final.zip, 1,302 lines in a 4-file chain, build 0, check 0, standard axioms). Statements and definition identical to the prompt in all three; no escapes, no shadowed names. Logs: model_outputs\check_r1_log.txt, check_r2_log.txt, check_r3_log.txt, check_summary.txt.
- Rubric: not needed (rejected).
- Notes: Post-mortem (playbook 4.1, handoff 30): no wording leak; the missing core had a 20-line textbook proof and the five statements were the textbook's ladder of lemmas (1 and 3 prove 2; 2 and 3 give 4 and 5). Lesson: Jacobsthal sums (normalisation x -> -x, x -> 1/x, the sum over c of S(c)^2, uniqueness of p = a^2 + b^2, Euler's criterion for the binomial coefficient) are within reach of all three models in 1,100 to 1,800 lines. Platform run times of the three models: not yet recorded (ask the fellow). Classical character-sum evaluations with an elementary core are not hard enough; the failures so far needed a missing identity or evaluation that cannot be reached by finite-field manipulation alone (Jacobi's identity, Gauss sum sign, cubic Jacobi sums, Zsigmondy).
- Next: None.
- Updated: 9 Oct 2026, 19:40 IST
### Task 8 - Fractional parts of n^2 x and polynomial values (Weyl), version 2

- Status: golden
- State: Outputs checked officially on lean_worker_git.bat, 10 Oct 2026, 13:18-14:06 IST (repo jobs t8_r1_check, t8_r2_check, t8_r3_check, t8_r3_rerun_1..4): R1 GENUINE FAILURE, R2 and R3 PASS. Golden written in the cloud Lean loop (about 1 h, own route) and verified by worker job t8_golden_01 (13:56 IST): build exit 0, no warnings, check exit 0, standard axioms for all five theorems. Fresh-copy offline check PASSED (verify_golden_offline.bat 8, 10 Oct 14:13-14:16 IST, D:\lean\golden_check_t8_22124: /opt/mathlib4 at 9944fe29..., build exit 0, no warnings, check exit 0, standard axioms; log tasks\task 8\golden\golden_offline_check_log.txt). The fellow reported the platform steps done at 14:19 IST (verdicts and submit status not yet recorded). v2 prompt compiled officially 9 Oct (job 018d_t8v2_statements); v1 (job 007) superseded, never run on the platform.
- Laptop: Honor laptop
- Folder: tasks\task 8 (Honor laptop); v1 files kept as task8_prompt_v1_superseded.txt, turing_t8_generator_v1_superseded.py, statements_worker_log_v1_superseded.txt
- Topic: all five theorems need the equidistribution of n^2 x (or of polynomial values with irrational leading coefficient): uniform-in-(a, b) frequency of {n^2 x}; frequency of {f(n)} for a real polynomial with irrational leading coefficient and degree >= 1; first decimal digit of 2^(n^2) (Benford frequencies); mean of |sin(n^2)| = 2/pi; mean of cos(n^2 x) = 0 for x/pi irrational. 5 theorems, no definitions
- Files: task8_prompt.txt (3,781 chars, sha256 48ae5b6370e02252...), TuringTask\Basic.lean (5d3c271a61c19b30...), StatementAndAxiomsCheck.lean, statements_worker_log.txt. Generator checks: 101 finite-N numerics (not exact): {n^2 x} for 5 irrationals and 8 intervals at N = 20000 with 60-digit decimals, grid worst error (uniform), 5 polynomials of degree 2-4, digits of 2^(n^2) exact for n < 400 and by decimals for n < 20000 (observed 0.2973 for d = 1 vs 0.3010), mean |sin(n^2)| at N = 10^6 (0.63683 vs 0.63662), mean cos(n^2 x) at N = 10^6 for 4 values of x (all below 1e-3), and that rational x, rational leading coefficient, constant polynomial and x/pi rational break the statements. GOLDEN (tasks\task 8\golden): golden_solution.zip (20,829 bytes, sha256 31180a409ca2e929...; 7 Lean files Phase 273 + PolySum 126 + Circle 139 + Counting 317 + LeadDigit 107 + Main 176 + Basic 39 = 1,177 lines, one import chain, every file imports Mathlib), turing_t8_golden_generator.py (sha256 checks, byte-identical to job t8_golden_01), task8_golden_explanation.txt (15,108 chars ASCII), task8_rubric.csv (6 items) and .txt, golden_worker_log.txt
- Model outputs: R1 `turing_task_r1.zip` (64 lines, sha256 ac583fcca8baca0d...) GENUINE FAILURE: its Basic.lean declares `TuringTask.abs (x : Real) : Real := 0` and `TuringTask.Filter.Tendsto ... := True` inside the namespace, so the five statements mean something else; job t8_r1_check: build exit 0 (cold 736 s), check exit 1 (Ambiguous term `abs`, Type mismatch `TuringTask.Filter.Tendsto` vs `Filter.Tendsto`); its README claims all five proved. R2 `turingtask-weyl_r2.zip` (8 files, 1,740 lines, 1e17fbea17d3a58a...) PASS: job t8_r2_check, build exit 0 (lint warnings only), check exit 0, standard axioms. R3 final `r3\turing-task-complete.zip` (6 files, 1,754 lines, da98b2d2fa725109...; the other five r3 zips are earlier partial projects) PASS: job t8_r3_check failed with the parallel-build olean read error (environment, not a result); sequential reruns t8_r3_rerun_1..3 and t8_r3_rerun_4_full: build exit 0 (lint warnings only), check exit 0, standard axioms. Logs: model_outputs\check_r1_log.txt, check_r2_log.txt, check_r3_log.txt, check_summary.txt
- Rubric: 6 items: build + 5 proof-only items (task8_rubric.csv). Because of R1, each proof item also requires that the names in the statement (abs, Filter.Tendsto, Int.fract, ...) denote the Mathlib declarations, not project declarations such as TuringTask.abs. Expected from our Lean runs: golden 6/6 = 100 percent, R1 1/6 = 17 percent, R2 6/6, R3 6/6. Compare every judge verdict with these
- Notes: Why v2 (checklist in playbook 4.1): v1 had the linear case {n x} as theorem 1 and three statements that follow from it, so a model with the elementary block argument would score 5/6 even if the quadratic case failed. v2 keeps nothing that the linear case settles; the linear case is a hidden lemma. Core: Weyl criterion (Fourier density on AddCircle: Mathlib `span_fourier_closure_eq_top`) plus van der Corput differencing and the degree induction; Mathlib has no equidistribution theorem. Novelty 9 Oct: Mathlib (pinned) has only density of {n x} (`denseRange_zsmul_coe_iff`), `irrational_pi`, Fourier density; formal-conjectures has the definitions `IsEquidistributed`, `IsEquidistributedModuloOne` and open `sorry` problems on (3/2)^n; TauCeti (12,124 files), compfiles, PutnamBench, miniF2F: nothing; web: no Lean or Isabelle formalization found. Golden plan in handoff section 31 (expected 1,300-1,800 lines). GOLDEN ROUTE (handoff section 38): differencing inequality with an explicit window (van der Corput), Weyl for polynomial phases by induction on the degree (taylor/hasseDeriv for the shifted difference), averages of continuous functions on AddCircle 1 via span_fourier_closure_eq_top (finite Fourier sums, three epsilon/3 terms), interval frequencies from a distance bump on the circle plus the complementary intervals, uniformity by a grid, digits via fract(log_10 2^(n^2)) and the irrationality of log_10 2. Proof bodies of R2 and R3 not read; overlap scan against all eight output zips clean (only the prompt's statement lines coincide). Calibration: R1 64 lines (cheat), R2 1,740, R3 1,754; platform run times not recorded (ask the fellow)
- Next: Record the platform verdicts and the submit status (expected golden 6/6, R1 1/6, R2 6/6, R3 6/6). Platform steps were: upload golden_solution.zip, paste task8_golden_explanation.txt, upload task8_rubric.csv in the model-response section and run, download CSV, upload it in the golden section and run, compare verdicts (golden 6/6, R1 1/6, R2 6/6, R3 6/6), submit
- Updated: 10 Oct 2026, about 14:30 IST

### Task 9 - Cubes modulo p (Gauss, Jacobi)

- Status: golden
- State: Golden, explanation and 6-item rubric ready and verified 9 Oct 13:45 IST; cleared for the platform
- Laptop: Honor laptop
- Folder: tasks\task 9\golden (Honor laptop)
- Topic: For p = 1 mod 3, 4p = L^2 + 27M^2: count of x^3 + y^3 = 1, two cyclotomic numbers, 2 is a cube iff p = x^2 + 27y^2, cubic exponential sum. 5 theorems, no definitions
- Model outputs: R1 PASS (official job 011d, 9 Oct: build 0, check 0, standard axioms). R2 PASS (job 011b). R3 FAIL (job 011a: build 0, all five theorems absent, check file errors). Expected 6-item rubric: R3 1/6 = 17 percent
- Golden: golden_solution.zip (sha256 fd923c5f...), 5 files, 899 lines, /opt/mathlib4 lakefile, model-format manifest. Worker job 012g and fresh-copy offline check (9 Oct 13:19) both: build exit 0, no warnings, check exit 0, standard axioms.
- Rubric: 6 items: build + 5 proof-only items (task9_rubric.csv). Expected from our Lean runs: golden 6/6, R1 6/6, R2 6/6, R3 1/6 = 17 percent.
- Notes: Novelty re-checked 9 Oct (KummerCriterion, TauCeti 39c285d3, web): nothing on cubic residues or x^2 + 27y^2. Mathlib Jacobi-sum lemmas used and disclosed. Earlier draft 012a discarded (shared names/lines with R2); final golden shares no proof lines with R1/R2. Handoff section 25.
- Next: Platform: upload zip, paste task9_golden_explanation.txt, upload task9_rubric.csv in the model-response section and run, download CSV, upload it in the golden section and run, compare verdicts (golden 6/6, R3 1/6), confirm and submit.
- Updated: 9 Oct 2026, 13:45 IST

### Task 10 - Primitive prime divisors (Zsigmondy)

- Status: submitted
- State: Submitted by the fellow on 9 Oct (about 17:40 IST). Fresh-copy offline check was NOT run before submission (no golden_offline_check_log.txt); worker job 016c passed.
- Laptop: Honor laptop
- Folder: tasks\task 10\golden (Honor laptop)
- Topic: a^n - b^n and a^n + b^n always gain a new prime factor (exceptions listed); divisor bound for the prime factors of a^n - 1; a^n - 1 = q^m only for 3^2 - 1; same prime factors only for m = 1, n = 2. 5 theorems, no definitions
- Model outputs: R1 FAIL (official job 014a: build 0, one sorry at line 1757 in exists_prime_sub, all five theorems depend on sorryAx; README claims completeness). R2 rollout failed (no output). R3 FAIL (job 014b: build 0, none of the five theorems exist, check exit 1). Re-confirmed 9 Oct 16:45 IST; job sources byte-identical to the zips. Expected 6-item rubric: R1 1/6, R3 1/6.
- Golden: golden_solution.zip (sha256 488b63a5...), 7 files (Hcyc, Prim, Size, Zsig, Apps, Main, Basic), 1,017 lines, /opt/mathlib4 lakefile, model-format manifest. Official worker job 016c: build exit 0, no warnings, check exit 0, standard axioms. Fresh-copy offline check not run.
- Rubric: 6 items: build + 5 proof-only items (task10_rubric.csv). Expected: golden 6/6, R1 1/6 = 17 percent, R3 1/6 = 17 percent (R2 rollout failed).
- Notes: Own Zsigmondy proof (homogeneous cyclotomic values, cyclotomic_mul_prime_pow_eq, LTE padicValNat.pow_sub_pow, real bounds sub_one_pow_totient_lt_cyclotomic_eval). Numeric check of every lemma claim (2,223 cases). Overlap scan vs R1/R3: only prompt statement lines. Novelty re-checked 9 Oct: Mathlib, TauCeti 0e01c247 (12,085 files), KummerCriterion, web: no Zsigmondy in Lean.
- Next: Wait for review. Optional: run verify_golden_offline.bat 10 to confirm the fresh-extract build. If sent back, fix per the review and rerun grading.
- Updated: 9 Oct 2026, 17:45 IST

### Task 11 - Colourings that avoid bad events (local lemma applications)

- Status: rejected
- State: All three models passed, no failure (9 Oct 15:05 IST). No golden written.
- Laptop: Honor laptop
- Folder: tasks\task 11 (Honor laptop)
- Topic: Bounded dependence: proper 2-colourings of hypergraphs (two versions), k-SAT, Ramsey and van der Waerden lower bounds. 5 theorems, no definitions
- Model outputs: M1 pass, M2 pass, M3 pass. Official 9 Oct: R1 job 013a, R2 job 013b, R3 job 013c all build exit 0 (lint/deprecation warnings only), check file exit 0, five axiom lists [propext, Classical.choice, Quot.sound]. R1 1,217 lines (own counting LLL), R2 1,121 lines in 8 files (own LLL), R3 836 lines (Mathlib product measure and iIndepFun_pi).
- Rubric: Plan: build + 5 proofs = 6 items; sorry-only 1/6 = 17 percent.
- Notes: Sanity checks only (existence for all parameters). Isabelle AFP has the local lemma (Edmonds 2024): disclose. Golden plan in handoff section 23 (Honor laptop).
- Next: None. Lesson: the symmetric local lemma is within reach of all three models (836 to 1,217 lines).
- Updated: 9 Oct 2026, 15:05 IST

### Task 12 - New prime factors of Fibonacci and Lucas numbers (primitive divisors)

- Status: prompt
- State: Prompt compiled officially (job 017a_t12_statements, 9 Oct 18:13: build exit 0, five `sorry` warnings, check exit 0); recorded and handed over 9 Oct about 19:30 IST
- Laptop: Honor laptop
- Folder: tasks\task 12 (Honor laptop)
- Topic: F_n (n >= 3, n != 6, 12) and L_n (n >= 2, n != 6) have a prime factor dividing no earlier term; #divisors(n) <= #primeFactors(F_n) + 4; same prime factors of F_m, F_n (3 <= m < n) only for (3, 6); F_n has a prime factor = +-1 mod n (n >= 3, n != 5, 6, 12). 5 theorems, no definitions. Natural numbers, divisibility as `x % q = 0`, L_n written `Nat.fib (n - 1) + Nat.fib (n + 1)`
- Files: task12_prompt.txt (2,852 chars, sha256 0a0c6fe3cad76c11...), TuringTask\Basic.lean (bbba647430d90015...), StatementAndAxiomsCheck.lean, statements_worker_log.txt. Generator checks: 9,406 exact (theorems 1-2 by stripping common factors for n <= 320, including that 6, 12 and 6 are exceptions; 3-5 with complete factorizations for n <= 130; theorem 3 tight at n = 12)
- Model outputs: R1 `turing_task_r1.zip` (342 lines): GENUINE FAILURE (official job 019a_t12_r1, 9 Oct 20:44: build exit 0 with `sorry` in exists_prime_fib (general case n >= 13) and exists_prime_fib_mod; all five axiom lists contain sorryAx; README claims success). R3 `TuringTask_r2.zip` (24 lines; the fellow says it is the third model's output, the platform relabels columns while a rollout runs): GENUINE FAILURE (job 019c_t12_r3: build exit 1, five unsolved goals, empty proofs; README admits nothing is proved). R2: still running at 21:10 IST. Logs: model_outputs\check_r1_log.txt, check_r3_log.txt, check_summary.txt
- Golden: golden_solution.zip (sha256 866c7507...), 8 files in one import chain (Fib 297, Rank 431, Psi 404, Size 383, Prim 238, Apps 195, Main 39, Basic 30; 2,017 Lean lines), /opt/mathlib4 lakefile, model-format manifest, README with the offline commands. OFFICIAL worker job 020a_t12_golden (9 Oct 23:55 IST): build exit 0, no warnings, check exit 0, five axiom lists [propext, Classical.choice, Quot.sound]; zip sources byte-identical. Fresh-copy offline check: pending (verify_golden_offline.bat 12). Explanation 16,358 chars (ASCII, ### Overview, one section per file, Verification, Sources and related work). Own work: route = rank of apparition + lifting the exponent + Moebius product psi_n with valuations + cyclotomic size bound at the golden ratio; overlap scan vs R1/R3: no shared lines or helper names. Numeric check of every lemma claim: 1,933 cases. Written with the cloud Lean (laptop oleans), compiled first time on the worker.
- Rubric: 6 items: build + 5 proof-only items (task12_rubric.csv). Expected from our Lean runs: golden 6/6 = 100 percent, R1 1/6 = 17 percent, R3 0/6 (build fails)
- Notes: Novelty 9 Oct: Mathlib (pinned) has fib_gcd, fib_dvd (IsDvdSequence), Binet (GoldenRatio.lean), no prime-divisibility or primitive-divisor result; nothing in TauCeti 1126622 (12,109 files), KummerCriterion, compfiles, PutnamBench, formal-conjectures; web and Isabelle AFP: no formalization found. Sources: Carmichael 1913 (Annals of Math. 15), Yabuta 2001 (Fibonacci Quart. 39). Golden expected to be the heaviest so far (irrational alpha, beta; entry-point theorem q | F_(q -+ 1) for theorem 5). Handoff section 29
- Next: Read golden_offline_check_log.txt; then platform: upload zip, paste task12_golden_explanation.txt, upload task12_rubric.csv in the model-response section and run, download CSV, upload it in the golden section and run, compare verdicts (golden 6/6, R1 1/6, R3 0/6), confirm and submit. Check R2 when it arrives (job 019b). Handoff section 32.
- Updated: 10 Oct 2026, 00:05 IST

### Task 13 - Resultants and discriminants of cyclotomic polynomials

- Status: golden
- State: Golden built and passed the official worker (jobs 027a_t13_golden cold 779 s and 027b_t13_golden warm, 10 Oct 2026, about 08:10 IST): build exit 0, no warnings, check exit 0, standard axioms for all five theorems. Own route, written in the cloud Lean loop (section 3.3 of the playbook) in about 2.5 hours; the proof bodies of R1 and R2 were not read. Fresh-copy offline check pending
- Laptop: Honor laptop
- Folder: tasks\task 13 (Honor laptop)
- Topic: Res(Phi_m, Phi_n) = 1 unless m = n p^k; Res(Phi_(n p^k), Phi_n) = p^phi(n) (except (1, 2, 1)); disc(Phi_n) times prod_(p | n) p^(phi(n)/(p-1)) = (-1)^(phi(n)/2) n^phi(n); Phi_m, Phi_n coprime in Z[X] iff m != n p^k; Res(Phi_n, X^m - 1) = Phi_k(1)^(phi(n)/phi(k)), k = n / gcd(n, m), n >= 3, n does not divide m. 5 theorems, no definitions, Mathlib's `Polynomial.resultant` and `Polynomial.discr`
- Files: task13_prompt.txt (3,542 chars, sha256 296ab22453f5ca9e...), TuringTask\Basic.lean (6b54c861d4b5881d...), StatementAndAxiomsCheck.lean, statements_worker_log.txt. Generator checks: 1,509 exact against the Mathlib definitions (Sylvester matrix, sylvesterDeriv sign), n < m <= 36, discriminants n <= 40, theorem 5 for n <= 25, m < 40, and that (1, 2, 1) and n = 2 really fail GOLDEN (tasks\task 13\golden): golden_solution.zip (17,127 bytes, sha256 ad641194af4e3e72...; 4 Lean files Fibre 154 + Resultants 475 + Discr 285 + Basic 35 = 949 lines, one import chain, every file imports Mathlib), turing_t13_golden_generator.py (sha256 checks, byte-identical to job 027b), task13_golden_explanation.txt (17,112 chars ASCII), task13_rubric.csv (6 items) and .txt, golden_worker_log.txt
- Model outputs: R1 `TuringTask_r1.zip` (984 lines, one file) PASS: job 020a_t13_r1, build exit 0 (422 s cold), check exit 0, five axiom lists [propext, Classical.choice, Quot.sound]. R2 `turingtask-cyclotomic-resultants_r2.zip` (Prelim 904 + Basic 176 lines) PASS: job 020b_t13_r2, build exit 0, check exit 0, standard axioms. R3 `r3\TuringTask.zip` (final; three earlier partial zips beside it) GENUINE FAILURE: job 020c_t13_r3, build exit 0 but `TuringTask/Basic.lean` is an empty namespace, the check file reports Unknown identifier for all five theorems (exit 1); its RESEARCH.md says it could not connect `Polynomial.discr` to the number-field discriminant. Logs: model_outputs\check_r1_log.txt, check_r2_log.txt, check_r3_log.txt, check_summary.txt (zip sha256 values)
- Rubric: 6 items written (build + one proof-only item per theorem). Expected from our Lean runs: golden 6/6, R1 6/6, R2 6/6, R3 1/6 = 17 percent. Compare every judge verdict with these
- Notes: Novelty 9 Oct: no resultant of cyclotomic polynomials anywhere (Mathlib pinned, TauCeti, KummerCriterion, compfiles, PutnamBench, formal-conjectures, web, AFP). RISK: Mathlib's Resultant/Basic.lean (1,027 lines) already has resultant_eq_prod_eval, resultant_mul_left/right, isUnit_resultant_iff_isCoprime, resultant_deriv, and Cyclotomic/ has eval_one_cyclotomic_prime_pow, norms of zeta - 1 for prime powers; the missing core is the product over primitive roots of zeta^m - 1 (fibre count of zeta -> zeta^m) and the discriminant bookkeeping. Related work to disclose: Mathlib resultant file; TauCeti RingTheory/Polynomial/Resultant (root-product formula for discr, no cyclotomic); IsCyclotomicExtension.discr_prime_pow (field discriminant, prime powers). Sources: Apostol 1970 (Proc. AMS 24), Louboutin 1995 (Proc. AMS 123). Handoff section 29 GOLDEN ROUTE: fibre lemma for alpha -> alpha^d on primitive roots (ZMod.unitsMap lift) gives Res(Phi_m, G(X^d)) = Res(Phi_k, G)^(phi m/phi k); theorem 1 by reduction modulo q (common root in AlgebraicClosure (ZMod q) forces m = n q^(a-b)) plus non-negativity from conjugate pairing; theorem 2 coprime case from Res(Phi_m, X^n - 1) = prod over divisors and theorem 1, general case through expand; theorem 3 from the recursion of Res(Phi_n, Psi_n) (squares kill the sign; non-negativity fixes it) and the derivative identity with resultant_deriv; theorem 5 is the fibre lemma with G = X - 1 (the hypothesis n does not divide m is not needed; kept as an unused argument). Name-overlap scan against R1/R2: three coincidental helper names were renamed before job 027b; both passing outputs also use ZMod.unitsMap and resultant_deriv (names only; disclosed in the explanation). Handoff section 36
- Next: Fellow runs verify_golden_offline.bat 13 (fresh copy, offline); read golden_offline_check_log.txt; then platform: upload golden_solution.zip, paste task13_golden_explanation.txt, upload task13_rubric.csv, grade golden and the three responses, compare with our Lean runs (golden 6/6, R1 6/6, R2 6/6, R3 1/6), submit
- Updated: 10 Oct 2026, about 08:20 IST

### Task 14 - Average order of the divisor function (Dirichlet 1849, hyperbola method)

- Status: rejected
- State: All three models passed, no genuine failure (10 Oct 2026, 13:55 IST). No golden written. Prompt compiled officially 9 Oct (job 018e_t14_statements: build exit 0, five sorry warnings, check exit 0, 36 s)
- Laptop: Honor laptop
- Folder: tasks\task 14 (Honor laptop)
- Topic: D(N) = sum of d(n) for n <= N. |D(N) - N log N - (2 gamma - 1) N| <= 4 sqrt N (N >= 1); |sum_(n <= N) d(n)/n - (log N)^2/2 - 2 gamma log N| <= 4 (N >= 1); (D(N) - N log N)/N -> 2 gamma - 1; (1/N) sum (d(n) - log n) -> 2 gamma; (sum_(n <= N) D(n) - N^2 log N / 2) / N^2 -> gamma - 3/4. 5 theorems, no definitions; Real.eulerMascheroniConstant, Nat.divisors, Filter.Tendsto
- Files: task14_prompt.txt (3,217 chars, sha256 c8d81f650649215d...), TuringTask\Basic.lean (4d237da0e3b5431e...), StatementAndAxiomsCheck.lean, statements_worker_log.txt. Generator checks: 2,000,012 (theorems 1 and 2 for every N <= 10^6 with gamma to 40 digits: largest |error|/sqrt N = 0.9607 and largest deviation 1.0 (at N = 1, tending to gamma^2 - 2 gamma_1 = 0.4789) against the stated 4; the three limits at N = 10^3..10^6 within 8/sqrt N)
- Model outputs: R1 `turing_task_r1.zip` (sha256 b2303adb590a314d...) PASS: job t14_r1_check, 1,812 lines in one file, build exit 0, no warnings, check exit 0, five axiom lists [propext, Classical.choice, Quot.sound]. R2 `turingtask-lean_r2.zip` (cc1f61653f264b94...) PASS: job t14_r2_check, 1,255 lines in 10 files (Hyperbola, Divisors, Harmonic, Floor, Thm1, LogSum, Thm2, Stirling, Limits, Basic), build exit 0, no warnings, check exit 0, standard axioms. R3 final `r3\TuringTask.zip` (d0f51961369bf1d7...; the four other r3 zips are earlier attempts with five sorry in Basic) PASS on the mathematics: job t14_r3_check, 1,745 lines, chain Research -> First -> Second -> Limits -> Basic, build exit 0, no warnings, check exit 0, standard axioms; one `set_option maxHeartbeats 800000`. Packaging slip in R3 (not counted as a failure): its own `TuringTask.lean` imports only `TuringTask.Second`, so plain `lake build` never compiles Limits.lean and Basic.lean (job t14_r3_ownroot: 8,668 jobs, `import TuringTask` lacks the five theorems, Unknown constant). Statements whitespace-identical to the prompt in all three; no escapes, no shadowed names; proof bodies not read. Logs: model_outputs\check_r1_log.txt, check_r2_log.txt, check_r3_log.txt, check_summary.txt. Earlier runs: jobs\recheck_024a..d_t14_* (single worker, same results); the legacy _jobs\024a..d_t14_* logs are unreliable (two workers overlapped)
- Rubric: not needed (rejected)
- Notes: Novelty 9 Oct: Mathlib (pinned) has eulerMascheroniConstant with the two monotone sequences (error O(1/n)) and a TODO "Dirichlet hyperbola method" in ArithmeticFunction/Misc.lean; no divisor-sum asymptotics anywhere (Mathlib, TauCeti, FCBench, KummerCriterion, PNT+, compfiles, PutnamBench, formal-conjectures, web). Checks are finite-N numerics (theorems 3-5 are limits). Golden plan in handoff section 33 (700 to 1,000 lines). Post-mortem (handoff 37): solved by all three in 1,255 to 1,812 lines. Checklist answers in hindsight: textbook test yes (Apostol Theorem 3.3, Hardy-Wright 320: hyperbola method plus H_n = log n + gamma + O(1/n)); Mathlib-assist yes (eulerMascheroniSeq/eulerMascheroniSeq' monotone bounds, harmonic_le_one_add_log, integral comparison for log x / x and x log x); ladder yes (theorems 3-5 follow from theorem 1 plus elementary limits). Platform run times of the three models: not recorded (ask the fellow)
- Next: None
- Updated: 10 Oct 2026, about 14:00 IST

### Task 15 - Character sums modulo a prime (Polya 1918, Vinogradov 1918) and least non-residues

- Status: rejected
- State: 10 Oct 2026, 14:20-14:27 IST: all three model outputs PASSED on the official worker (repo jobs t15_r1_check, t15_r2_check, t15_r3_check: build exit 0, check exit 0, five axiom lists [propext, Classical.choice, Quot.sound]). No genuine failure: REJECTED, no golden, no rubric. Prompt compiled officially 9 Oct (job 018d_t15_statements)
- Laptop: Honor laptop
- Folder: tasks\task 15 (Honor laptop)
- Topic: |sum_(n <= N) chi(n)| <= sqrt p log p for every non-principal character chi mod a prime p (MulChar (ZMod p) C); the Legendre-symbol version (p != 2); a non-k-th-power <= sqrt p log p + 1 for k >= 2, k | p - 1; |2 R - N| <= sqrt p log p for the number R of residues in 1..N (N < p); a prime non-residue <= sqrt p log p + 1. 5 theorems, no definitions
- Files: task15_prompt.txt (3,243 chars, sha256 1430a93c4e3e5bb4...), TuringTask\Basic.lean (9c258f8ea0ec20b8...), StatementAndAxiomsCheck.lean, statements_worker_log.txt. Generator checks: 1,197,685 (theorem 1 for every character of every prime <= 200 and every N < p; theorems 2, 4 for every odd prime <= 3000 and N < p; theorem 3 for every k | p - 1; theorem 5 for every odd prime <= 3000; the sine-sum bound of the classical proof for p <= 10^4; p != 2 and N < p cannot be dropped)
- Model outputs: R1 `turing_task_r1.zip` (one file, 925 lines, 6f6a0408aa1721c8...) PASS (t15_r1_check, Basic 36 s, no warnings). R2 `turing-task_r2.zip` (one file, 619 lines, e3ccd35f13643287...) PASS (t15_r2_check, no warnings). R3 `TuringTask_r3.zip` (Core 343 -> Consequences 250 -> Basic 33, a0eb5fe169bef29f...) PASS (t15_r3_check, info messages only). All three follow the plan of handoff section 33 (Gauss-sum expansion, geometric sums, sine sum, harmonic bound; character of order k). Logs: model_outputs\check_r1_log.txt, check_r2_log.txt, check_r3_log.txt, check_summary.txt
- Rubric: none (rejected)
- Notes: Novelty 9 Oct: no Polya-Vinogradov or least-non-residue bound anywhere (Mathlib pinned: hits are polyCharpolyAux; TauCeti, FCBench, KummerCriterion, PNT+, compfiles, PutnamBench, formal-conjectures, web). Mathlib supplies the ingredients (gaussSum_mulShift, gaussSum_mul_gaussSum_eq_card, ZMod.stdAddChar, Real.mul_le_sin, harmonic bounds, eulerMascheroniSeq'_six_lt_two_thirds, quadraticChar_ne_one, exists_mulChar_orderOf) but not the inequality. Golden plan in handoff section 33 (600 to 900 lines)
- Next: none (rejected). Post-mortem in handoff section 39
- Updated: 10 Oct 2026, about 14:30 IST
### Task 16 - Square, twice-square and power-of-two Fibonacci and Lucas numbers (Cohn 1964)

- Status: golden
- State: Outputs checked officially on lean_worker_git.bat, 10 Oct 2026, 14:52-14:57 IST (repo jobs t16_r1_check, t16_r2_check, t16_r3_check): R1 and R3 GENUINE FAILURES, R2 PASS. Golden written in the cloud Lean loop (about 40 min, own route) and verified by worker job t16_golden_01 (15:10 IST): build exit 0, no warnings, check exit 0, standard axioms for all five theorems. Fresh-copy offline check PASSED (verify_golden_offline.bat 16, 10 Oct 15:18-15:20 IST, D:\lean\golden_check_t16_2088: /opt/mathlib4 at 9944fe29..., build exit 0, no warnings, check exit 0, standard axioms; log tasks\task 16\golden\golden_offline_check_log.txt). Prompt compiled officially 9 Oct (job 023a_t16_statements)
- Laptop: Honor laptop
- Folder: tasks\task 16 (Honor laptop)
- Topic: F_n a square only for n = 0, 1, 2, 12; L_n (n >= 1) a square only for n = 1, 3; F_n = 2 x^2 only for n = 0, 3, 6; L_n = 2 x^2 (n >= 1) only for n = 6; F_n a power of 2 only for n = 1, 2, 3, 6. 5 theorems, no definitions; L_n written `Nat.fib (n - 1) + Nat.fib (n + 1)` as in task 12
- Files: task16_prompt.txt (2,194 chars, sha256 d023e089013a5f1c...), TuringTask\Basic.lean (55bbf4bb2a4d6f85...), StatementAndAxiomsCheck.lean, statements_worker_log.txt. Generator checks: 205,754 exact (all five statements for n <= 5000 with exact squares; the Nat encoding at n = 0 shows that n >= 1 is needed for the Lucas statements; the four congruences of the classical proof for m, k <= 300). GOLDEN (tasks\task 16\golden): golden_solution.zip (11,606 bytes, sha256 4e566344ea3352b3...; 4 Lean files Lucas 98 + Residues 235 + Equations 281 + Basic 27 = 641 lines, one import chain, every file imports Mathlib), turing_t16_golden_generator.py (sha256 checks, byte-identical to job t16_golden_01), task16_golden_explanation.txt (9,955 chars ASCII), task16_rubric.csv (6 items) and .txt, golden_worker_log.txt
- Model outputs: R1 `turing_task_r1.zip` (one file, 472 lines, 109dda6e51ffea77...) GENUINE FAILURE: job t16_r1_check build exit 0 with four `declaration uses sorry` (fib_eq_sq, lucas_eq_sq, fib_eq_two_mul_sq, lucas_eq_two_mul_sq contain sorryAx); fib_eq_two_pow is proved (standard axioms). R2 `turingtask-lean_r2.zip` (Lemmas 1,165 + Basic 272 lines, 3cf82e1fb97f076b...) PASS: job t16_r2_check, build exit 0, no warnings, check exit 0, standard axioms. R3 final `r3\turing-task-reduction.zip` (121 lines, 757211fe78dbe5d9...; the other three r3 zips are research notes, not TuringTask projects) GENUINE FAILURE: job t16_r3_check, all five theorems `sorry` (sorryAx in all five); its README says it is not a solution. Logs: model_outputs\check_r1_log.txt, check_r2_log.txt, check_r3_log.txt, check_summary.txt
- Rubric: 6 items: build + 5 proof-only items (task16_rubric.csv). Expected from our Lean runs: golden 6/6 = 100 percent, R1 2/6 = 33 percent (build + fib_eq_two_pow), R2 6/6, R3 1/6 = 17 percent. Compare every judge verdict with these
- Notes: Novelty 9 Oct: nothing on square Fibonacci or Lucas numbers in Mathlib (pinned; Nat.fib and Int.fib APIs only: fib_add, fib_two_mul, gcd_fib, Cassini), TauCeti, FCBench, KummerCriterion, PNT+, compfiles, PutnamBench, formal-conjectures, web. Hardness checklist: not finite-field manipulation (a descent through Lucas-number congruences modulo L_k with quadratic non-residues); the four results are proved together in Cohn's paper, so the statements show WHICH facts are true but not the congruence machinery. Source: J. H. E. Cohn, On square Fibonacci numbers, J. London Math. Soc. 39 (1964) 537-540; Square Fibonacci numbers, etc., Fibonacci Quart. 2 (1964) 109-113. Golden plan in handoff section 33 (1,000 to 1,500 lines). GOLDEN ROUTE (handoff section 41): Cohn's method with integer indices: F(a+k) + F(a-k) = F(a) L(k) for even k (Int.fib_add, Int.fib_neg), so F(m + 2kt) = -F(m) and L(m + 2kt) = -L(m) mod L(k) for odd t; L(k) = 3 mod 4 for k even, 3 not dividing k, so a prime factor 3 mod 4 excludes x^2 = -1, -4, -9 mod L(k); every index is m + 2kt with base m in (0, +-1, +-3, +-6) and t a power of 3; even indices by F(2m) = F(m) L(m), gcd | 2. Different from R2's 2-adic splitting with Jacobi symbols (R2's README). Proof bodies of R2 not read; overlap scan against all six output zips clean (only the prompt's names and statement lines coincide). Prompt-design note: theorem 5 (powers of 2) can be proved without the core (R1 did), which lifts a partial output to 33 percent
- Next: Platform: upload golden_solution.zip, paste task16_golden_explanation.txt, upload task16_rubric.csv in the model-response section and run, download CSV, upload it in the golden section and run, compare verdicts (golden 6/6, R1 2/6, R2 6/6, R3 1/6), submit
- Updated: 10 Oct 2026, about 15:25 IST

### Task 17 - Densities governed by 6/pi^2 (squarefree numbers, coprime pairs, Euler's function)

- Status: rejected
- State: All three models passed, no genuine failure (10 Oct 2026, 15:03 IST). No golden written. Prompt compiled officially 9 Oct (job 023b_t17_statements: build exit 0, five sorry warnings, check exit 0, 24 s)
- Laptop: Honor laptop
- Folder: tasks\task 17 (Honor laptop)
- Topic: |Q(N) - 6N/pi^2| <= 3 sqrt N (Q = squarefree count); |C(N) - 6N^2/pi^2| <= 6N(log N + 1) (C = coprime pairs in [1,N]^2); |sum phi(n) - 3N^2/pi^2| <= 4N(log N + 1); |sum phi(n)/n - 6N/pi^2| <= log N + 2; Q(N)/N -> 6/pi^2. 5 theorems, no definitions; Squarefree, Nat.Coprime, Nat.totient, Real.pi
- Files: task17_prompt.txt (2,990 chars, sha256 79338f15aede6125...), TuringTask\Basic.lean (4b1f25f64e5c1a4f...), StatementAndAxiomsCheck.lean, statements_worker_log.txt. Generator checks: 4,103,404 (theorems 1-4 for every N <= 10^6 by exact sieves: actual error at most 23, 7, 18, 20 percent of the stated bounds; the coprime-pair identity 2 sum phi - 1 for N <= 400; the two Moebius identities; the limit at 10^3..10^6)
- Model outputs: R1 `turing_project_r1.zip` (sha256 aaab9c37b97003aa...; `TuringTask_r1.zip` is the same file) PASS: job t17_r1_check, 790 lines in one file, build exit 0, no warnings, check exit 0, five axiom lists [propext, Classical.choice, Quot.sound]. R2 `turingtask-lean_r2.zip` (9696a4435d699289...) PASS: job t17_r2_check, 777 lines in one file, build exit 0, no warnings, check exit 0, standard axioms. R3 final `r3\turing-task.zip` (fecc7d1011785c22...; card-squarefree-proof.zip and totient-proofs.zip are earlier scratch attempts with five sorry in Basic) PASS: job t17_r3_check, 1,049 lines, chain SquarefreeEstimates -> TotientEstimates -> Basic, build exit 0, no warnings, check exit 0, standard axioms. Statements whitespace-identical to the prompt in all three; no escapes, no shadowed names; proof bodies not read. Logs: model_outputs\check_r1_log.txt, check_r2_log.txt, check_r3_log.txt, check_summary.txt
- Rubric: not needed (rejected)
- Notes: Novelty 9 Oct: no squarefree or coprime density, no sum-of-totient asymptotic anywhere (Mathlib pinned, TauCeti, FCBench, KummerCriterion, PNT+, compfiles, PutnamBench, formal-conjectures, web). Mathlib has the ingredients (riemannZeta_two, LSeries_convolution', moebius_mul_coe_zeta, sum_Ioc_inv_sq_le_sub, sq_mul_squarefree, harmonic_le_one_add_log) but not the asymptotics. Same analytic flavour as task 14: if 14 is solved by all three, expect the same here. Golden plan in handoff section 34 (800 to 1,100 lines). Post-mortem (handoff 40): as feared after task 14, solved by all three in 777 to 1,049 lines, the shortest outputs of the analytic batch; R3's zip timestamps span about 45 minutes. Mathlib supplies the core (riemannZeta_two, moebius_mul_coe_zeta, LSeries convolution, sum_Ioc_inv_sq_le_sub), so only Moebius-sum bookkeeping remained; the generous constants (actual errors 7 to 23 percent of the bounds) forced no delicate cases. Platform run times of the three models: not recorded (ask the fellow)
- Next: None
- Updated: 10 Oct 2026, about 15:05 IST

### Task 22 - Three cubes in arithmetic progression; rational points of y^2 = x^3 + 1 and y^2 = x^3 - 27 (Euler, Legendre)

- Status: prompt
- State: Prompt compiled officially (job t22_statements, 10 Oct 2026, 17:40-17:51 IST: build exit 0 (Basic 91 s), exactly five `sorry` warnings, check exit 0, sorryAx in all five axiom lists); handed over 10 Oct 2026, about 18:00 IST
- Laptop: Honor laptop
- Folder: tasks\task 22 (Honor laptop)
- Topic: x^3 + y^3 = 2 z^3 in Z only for x = y or x + y = 0; rational points of y^2 = x^3 + 1 are (-1, 0), (0, +-1), (2, +-3); the only rational point of y^2 = x^3 - 27 is (3, 0); x^3 - 2 y^3 = +-1 only for (1, 0), (-1, -1), (-1, 0), (1, 1); n (n + 1) = 2 m^3 only for n = 0, 1. 5 theorems, no definitions; Int, Rat, Nat; finite sets written `Membership.mem (S : Finset ...) a` (ASCII for a in S)
- Files: task22_prompt.txt (2,628 chars, sha256 1421a0b704cc2e63...), TuringTask\Basic.lean (14df6a5e366da226...), StatementAndAxiomsCheck.lean (4fb05bf4f0f318b1...), statements_worker_log.txt, model_outputs\.keep, generator turing_t22_generator.py (8b8d29f7b4eba036...). Generator checks (exact): theorem 1 for all 2,883,601 pairs |x|, |y| <= 1200; theorems 2 and 3 over all 1,464,035 candidates x = a/d^2 (gcd(a, d) = 1, d <= 60, |a| <= 20000) each; theorem 4 for |y| <= 300,000; theorem 5 for n <= 3,000,000; 9,716 identities of the golden route; Euler's lemma on 78 cases; a witness per hypothesis; no finite search space
- Model outputs: none yet
- Rubric: planned 6 items (build + 5 proof-only). Expected: golden 6/6, a sorry-only or theorem-less output 1/6 = 17 percent
- Notes: Novelty 10 Oct: nothing on x^3 + y^3 = 2 z^3, on the rational points of these curves, on x^3 - 2 y^3 = +-1 or on triangular cubes in Mathlib (pinned; only FLT for exponent 3 with Z[zeta_3] a PID and its units), TauCeti 65fa0e7, FCBench 0d031f72, formal-conjectures 1646ca1, RamanujanLean, KummerCriterion, flt-regular, PNT+, compfiles, PutnamBench, miniF2F, ProofNet, web. Near match to disclose: cadamcat/catalan-lean4 (4629f52, Oct 2026, Catalan's conjecture) proves the integer case x^2 = y^3 + 1 (`Catalan.euler_square_cube`) by Pell numbers; theorem 2 here is the rational statement. Ruled out while choosing: Ramanujan-Nagell (Lean 4 formalization, arXiv 2604.09808), Skolem zero sets (Berstel; short core). Checklist (playbook 4.1): short-core no, ladder no (core = theorem 1, theorems 2-5 are corollaries that do not show its proof), textbook partly, Mathlib-assist partly, finite-manipulation no. Sources: Euler, Algebra (1770); Legendre, Theorie des nombres (1830); Dickson, History vol. II ch. XXI; Mordell, Diophantine Equations (1969); both curves have conductor 36 and rank 0. Golden plan (about 1,250 lines: Eisenstein integers as QuadraticAlgebra Int (-1) (-1) with a Euclidean instance, Euler's lemma on cubes u^2 + 3 v^2, two-case descent, rational maps to u^3 + v^3 = 2) in handoff section 42
- Next: The fellow pastes task22_prompt.txt on the platform and drops the outputs into tasks\task 22\model_outputs\
- Updated: 10 Oct 2026, about 18:00 IST

### Task 23 - Consecutive integers without large prime factors; smooth values of x^2 - 1, x^2 + 1 and of the Pell numbers (Stormer, Lehmer)

- Status: prompt
- State: Prompt compiled officially (job t23_statements, 10 Oct 2026, 17:51-17:54 IST: build exit 0 (Basic 39 s), exactly five `sorry` warnings, check exit 0, sorryAx in all five axiom lists); handed over 10 Oct 2026, about 18:00 IST
- Laptop: Honor laptop
- Folder: tasks\task 23 (Honor laptop)
- Topic: n (n + 1) 7-smooth only for 23 values of n (largest 4374); x^2 - 1 7-smooth only for 29 values of x (largest 8749); n (n + 1)(n + 2) 7-smooth only for n <= 8 and n = 14, 48; x^2 + 1 13-smooth only for x in {0, 1, 2, 3, 5, 7, 8, 18, 57, 239}; x^2 - 2 y^2 = +-1 with y 13-smooth only for y in {1, 2, 5, 12, 70, 169, 13860}. 5 theorems, no definitions; "every prime factor of N is at most B" written `forall p : Nat, p.Prime -> N % p = 0 -> p <= B` (false for N = 0, so no side hypotheses)
- Files: task23_prompt.txt (3,481 chars, sha256 93049502f7742039...), TuringTask\Basic.lean (2982cae0fa73d98a...), StatementAndAxiomsCheck.lean (2e09bcbbc94288ba...), statements_worker_log.txt, model_outputs\.keep, generator turing_t23_generator.py (f67332243af8b7e5...). Generator checks (exact): all 42,487 7-smooth numbers below 10^16 (theorems 1-3 complete below 10^16); brute force with the Lean hypotheses (Nat semantics, edge cases) for n, x < 10^6; theorem 4 via all 6,634 {2, 5, 13}-smooth numbers below 10^20 and brute force x < 10^6; theorem 5 for (1 + sqrt 2)^k, k <= 400, and y < 10^6; Pell data of the golden route (15 + 7 equations, smooth indices, reconstruction of the sets, 60 prime-index factor checks); witnesses for every hypothesis; no finite search space
- Model outputs: none yet
- Rubric: planned 6 items (build + 5 proof-only). Expected: golden 6/6, a sorry-only or theorem-less output 1/6 = 17 percent
- Notes: Novelty 10 Oct: no Stormer or Lehmer result anywhere (Mathlib pinned has only `Nat.smoothNumbers`; Pell fundamental solutions exist, nothing on primitive divisors or ranks of apparition); nothing in TauCeti, FCBench, formal-conjectures, compfiles, PutnamBench, miniF2F, ProofNet, RamanujanLean, KummerCriterion, flt-regular, PNT+, catalan-lean4; web: none. Same family as task 12 (primitive divisors in Lucas sequences, two failures). Rejected alternative: Hurwitz's 1-2-4-8 theorem (textbook, short core). Checklist: short-core partly (the key lemma is one page, the per-D Pell analysis is long casework with exceptions such as 2 * 3^7 + 1 = 5^4 * 7 and 239^2 + 1 = 2 * 13^4), ladder only theorem 3, textbook no, Mathlib-assist partly, finite-manipulation no. Sources: C. Stormer, Skrifter Videnskabs-selskabet (Christiania) 1897, no. 2; D. H. Lehmer, On a problem of Stormer, Illinois J. Math. 8 (1964) 57-79. Golden plan (about 1,500 lines: prime factors of y_p / y_1 are p or +-1 mod p, Pell data for D | 210 and negative Pell for D | 130, squarefree-part reduction) in handoff section 42
- Next: The fellow pastes task23_prompt.txt on the platform and drops the outputs into tasks\task 23\model_outputs\
- Updated: 10 Oct 2026, about 18:00 IST

### Task 24 - Pisano period and entry point of the Fibonacci numbers: extremal and fixed-point values (Wall, Fulton and Morris, Salle, Freyd and Brown, Marques)

- Status: prompt
- State: Prompt compiled officially (job t24_statements, 10 Oct 19:16-19:40 IST: build exit 0, five `sorry` warnings, check exit 0, sorryAx in all five axiom lists); handed over 10 Oct 2026, about 19:55 IST
- Laptop: Honor laptop
- Folder: tasks\task 24 (Honor laptop)
- Topic: pi(n) = Pisano period (least k >= 1 with F_k = 0 and F_(k+1) = 1 mod n), z(n) = entry point (least k >= 1 with n | F_k); for n >= 1: pi(n) <= 6 n; pi(n) = 6 n iff n = 2 * 5^j (j >= 1); pi(n) = n iff n = 1 or n = 24 * 5^j; z(n) = 2 n iff n = 6 * 5^j; z(n) = n iff n = 5^j or n = 12 * 5^j. 5 theorems, no definitions; pi and z spelled out with remainders (`Nat.fib k % n = 0`, `Nat.fib (k + 1) % n = 1 % n`, `0 < Nat.fib k % n`), hypothesis 0 < n
- Files: task24_prompt.txt (3,149 chars, sha256 1299fb31f898bf1e...), TuringTask\Basic.lean (e6ba6aa2c0b623c3...), StatementAndAxiomsCheck.lean (b34d2b153b1feb4b...), statements_worker_log.txt, model_outputs\.keep, generator turing_t24_generator.py (4806e8a89da19a88...). Generator checks (exact): pi(n), z(n) by direct iteration and all five statements, both directions, for n <= 20,000 (100,000 checks); left-hand sides evaluated literally with Lean remainders for n <= 1,500; family members beyond the range up to 468,750; 35,977 data of the golden route (law of apparition for primes p < 5,000, lifting to prime powers, exact values at 2^a, 3^b, 5^c, lcm of coprime products, pi / z in {1, 2, 4}); witnesses: n = 0 (0 < n), n = 2 (0 < j), n = 1, 5, 12 (each case), n = 1 (`1 % n`), n = 10 (`k <= 6 n`); no finite search space
- Model outputs: none yet
- Rubric: planned 6 items (build + 5 proof-only). Expected: golden 6/6, a sorry-only or theorem-less output 1/6 = 17 percent
- Notes: Novelty 10 Oct: no Pisano period, entry point or law of apparition in Mathlib (pinned: fib_gcd, fib_dvd, Int.fib, Cassini, Legendre and Jacobi symbols), TauCeti, FCBench, formal-conjectures, compfiles, PutnamBench, miniF2F, ProofNet, RamanujanLean, KummerCriterion, flt-regular, PNT+, catalan-lean4, Sequencelib (provables/sequencelib dfb06c1: values of F and L only); web: only the papers. Related to task 12 (rank of apparition in its golden). Rejected alternative: Mordell equations y^2 = x^3 + k for class-number-one k (textbook, short core). Checklist (playbook 4.1): short-core no, ladder no (1 and 2 share the bound), textbook partly (Wall's theorems; the extremal and fixed-point results are journal results), Mathlib-assist partly, finite-manipulation no. Sources: D. D. Wall, Amer. Math. Monthly 67 (1960) 525-532; J. D. Fulton and W. L. Morris, Acta Arith. 16 (1969) 105-110; H. J. A. Salle, Fibonacci Quart. 13 (1975) 159-161; P. Freyd and K. S. Brown, Amer. Math. Monthly 99 (1992) 278-279 (E3410); D. Marques, Fibonacci Quart. 50 (2012) 346-352. Golden plan (about 1,500 lines: law of apparition by Frobenius on 1 + sqrt 5 and Euler's criterion, lifting, exact 2-, 3-, 5-adic values, lcm structure, largest-prime and lcm-ratio case analyses) in handoff section 43
- Next: The fellow pastes task24_prompt.txt on the platform and drops the outputs into tasks\task 24\model_outputs\
- Updated: 10 Oct 2026, about 19:55 IST

### Task 25 - Fibonacci and Lucas numbers next to a square or twice a square (Finkelstein, Robbins; Cohn's method, part II)

- Status: prompt
- State: Prompt compiled officially (job t25_statements, 10 Oct 19:40-19:52 IST: build exit 0, five `sorry` warnings, check exit 0, sorryAx in all five axiom lists); handed over 10 Oct 2026, about 19:55 IST
- Laptop: Honor laptop
- Folder: tasks\task 25 (Honor laptop)
- Topic: F_n + 1 is a square iff n in {0, 4, 6}; F_n = x^2 + 1 iff n in {1, 2, 3, 5}; F_n = 2 x^2 + 1 iff n in {1, 2, 4}; L_n = x^2 + 1 iff n in {0, 1}; L_n + 1 = 2 x^2 iff n in {1, 4, 11} (L_11 = 199). 5 theorems, no definitions, no hypotheses; L_n = c written `Nat.fib n + c = 2 * Nat.fib (n + 1)` (no Nat subtraction); finite sets as `Membership.mem (S : Finset Nat) n`
- Files: task25_prompt.txt (2,816 chars, sha256 6b35e3c1217524bf...), TuringTask\Basic.lean (fdf6b00b1d9691ae...), StatementAndAxiomsCheck.lean (385060e445a7514e...), statements_worker_log.txt, model_outputs\.keep, generator turing_t25_generator.py (4b1d075bd6603906...). Generator checks (exact): all five statements, both directions, for n <= 4,000; the golden route: Jacobi coverings with the periodicity of L(2^s) mod 8|A| proved by computing the whole orbit (12,990 covered cases cross-checked with big-integer Jacobi symbols), 64,542 factorization identities and gcds, square classes F in {x^2, 2x^2, 3x^2, 5x^2, 10x^2} and L in {x^2, 2x^2, 3x^2, 6x^2} for n <= 4,000, the quintic identity, the case analysis rebuilding the sets of theorems 1, 4, 5; no hypotheses, no finite search space
- Model outputs: none yet
- Rubric: planned 6 items (build + 5 proof-only). Expected: golden 6/6, a sorry-only or theorem-less output 1/6 = 17 percent, theorems 2 and 3 only 3/6 = 50 percent
- Notes: Novelty 10 Oct: nothing on Fibonacci or Lucas numbers of the forms x^2 +- 1, 2 x^2 +- 1 in Mathlib (pinned), TauCeti, FCBench, formal-conjectures, compfiles, PutnamBench, miniF2F, ProofNet, RamanujanLean, KummerCriterion, flt-regular, PNT+, catalan-lean4, Sequencelib; web: none. Sequel to task 16 (Cohn I: squares and twice squares): those results are lemmas here and are not stated. Rejected alternative: triangular Fibonacci and Lucas numbers (Luo; Cohn's Jacobi method leaves 50-330 residue classes uncovered, golden route not secured). Checklist: short-core no, ladder no, textbook no, Mathlib-assist no, finite-manipulation no. Sources: J. H. E. Cohn, J. London Math. Soc. 39 (1964) 537-540; R. Finkelstein, J. Reine Angew. Math. 262/263 (1973) 171-182 and Fibonacci Quart. 13 (1975) 340-342; N. Robbins, Fibonacci Quart. 19 (1981) 369-373 and Applications of Fibonacci Numbers (1988) 77-88. Golden plan (about 1,500 lines: task 16 golden as library, Jacobi coverings with 9, 5, 4, 4, 2 classes, factorizations F_n + 1 = F_a L_b and L_n +- 1 = L_a L_b or 5 F_a F_b with gcd 1 or 3, square classes 5 x^2, 10 x^2 via F_5k = 5 F_k Q_k, L = 3 x^2 by a covering) in handoff section 43
- Next: The fellow pastes task25_prompt.txt on the platform and drops the outputs into tasks\task 25\model_outputs\
- Updated: 10 Oct 2026, about 19:55 IST

### Task 26 - Primes of the form x^2 + n y^2 with one class in each genus (n = 5, 6, 13, 21) and Euler's product conjecture for x^2 + 5 y^2 (Fermat, Euler, Lagrange, Gauss)

- Status: prompt
- State: Prompt compiled officially (job t26_statements, 10 Oct 20:58-21:13 IST: build exit 0, five `sorry` warnings, check exit 0, sorryAx in all five axiom lists); handed over 10 Oct 2026, about 21:20 IST
- Laptop: Honor laptop
- Folder: tasks\task 26 (Honor laptop)
- Topic: p prime: p = x^2 + 5 y^2 iff p = 5 or p = 1, 9 mod 20; p, q = 3, 7 mod 20 imply p q = x^2 + 5 y^2; p = x^2 + 6 y^2 iff p = 1, 7 mod 24; p = x^2 + 13 y^2 iff p = 13 or p = 1, 9, 17, 25, 29, 49 mod 52; p = x^2 + 21 y^2 iff p = 1, 25, 37 mod 84. 5 theorems, no definitions; residue sets as `Membership.mem ({...} : Finset Nat) (p % m)`
- Files: task26_prompt.txt (2,954 chars, sha256 5ba035816b63bf25..., prose rewritten 10 Oct about 22:20 IST to pass the Humanize_AI check, Lean statements unchanged), TuringTask\Basic.lean (71f81ab919cd23da...), StatementAndAxiomsCheck.lean (aa4b192858bc4a2c...), statements_worker_log.txt, model_outputs\.keep, generator turing_t26_generator.py (7d26a204faf7fc98..., asserts the Humanize_AI scan). Generator checks (exact): theorems 1, 3, 4, 5 both directions for every prime below 10^6 (313,992 checks); theorem 2 for all 11,881 pairs of primes below 3000 in the classes 3, 7 mod 20; 177,552 data of the golden route (reduced forms of discriminants -20, -24, -52, -84; Lagrange's step and genus separation for every prime below 2 * 10^5; the composition identity); witnesses: composites 6, 10, 14, 22, 143, the primes 5 and 13, q = 41; no finite search space
- Model outputs: none yet
- Rubric: planned 6 items (build + 5 proof-only). Expected: golden 6/6, a sorry-only or theorem-less output 1/6 = 17 percent
- Notes: Novelty 10 Oct: no binary quadratic forms, reduction or genus theory in Mathlib (pinned), TauCeti, FCBench, compfiles, PutnamBench, miniF2F, ProofNet, RamanujanLean, KummerCriterion, flt-regular, PNT+, catalan-lean4, Sequencelib, int-y1/proofs, LegendreQF; web: none. Related (disclose): formal-conjectures OEIS/179524 (Sun's open congruences assuming p = x^2 + 5 y^2) and Wikipedia/IdonealCompleteness. Rejected alternative: cannonball problem and y^2 = x^3 - 36x (formalized: int-y1/proofs SquarePyramid, Anglin's proof). Checklist: short-core no, ladder no, textbook yes (Cox ch. 1-3), Mathlib-assist partly (reciprocity only), finite-manipulation partly (genus tables). Sources: Euler (1744-1764), Lagrange (1773-1775), Gauss, Disquisitiones (1801); D. A. Cox, Primes of the Form x^2 + ny^2 (2nd ed. 2013), Theorems 2.25, 2.26, 3.22; arXiv math/0606547 (inductive proof for x^2 + 5y^2). Golden plan (about 1,100 lines: forms and moves S, T, Lagrange reduction, representation of p from a square root of -n, reciprocity tables, reduced-form lists and genus tables mod 4n, composition for theorem 2) in handoff section 44
- Next: The fellow pastes task26_prompt.txt on the platform and drops the outputs into tasks\task 26\model_outputs\
- Updated: 10 Oct 2026, about 22:20 IST (Humanize_AI rewrite, handoff section 45)

### Task 27 - Representation numbers of x^2 + xy + y^2, x^2 + 3y^2, x^2 + 2y^2, x^2 + xy + 2y^2, x^2 + 7y^2 as character divisor sums (Dirichlet, Lorenz, Hall)

- Status: prompt
- State: Prompt compiled officially (job t27_statements, 10 Oct 21:13-21:17 IST: build exit 0, five `sorry` warnings, check exit 0, sorryAx in all five axiom lists); handed over 10 Oct 2026, about 21:20 IST
- Laptop: Honor laptop
- Folder: tasks\task 27 (Honor laptop)
- Topic: for n > 0, the number of integer pairs (counted in the box |x|, |y| <= n, `Finset.product (Finset.Icc (-n) n) (Finset.Icc (-n) n)`) equals 6 sum (d/3) for x^2 + xy + y^2; 2 sum (d/3) + 4 sum_{4 | d} ((d/4)/3) for x^2 + 3y^2; 2 sum (-2/d) for x^2 + 2y^2; 2 sum (d/7) for x^2 + xy + 2y^2; 2 sum (d/7) - 4 sum_{d odd, n/d even} (d/7) for x^2 + 7y^2 (sums over divisors d of n, Mathlib `jacobiSym`). 5 theorems, no definitions, hypothesis 0 < n, `Prod Int Int` for pairs (ASCII)
- Files: task27_prompt.txt (4,209 chars, sha256 15ea91797b6f393a..., prose rewritten 10 Oct about 22:20 IST to pass the Humanize_AI check, Lean statements unchanged), TuringTask\Basic.lean (f729ccfacda5cb60...), StatementAndAxiomsCheck.lean (95bd440bf58370e0...), statements_worker_log.txt, model_outputs\.keep, generator turing_t27_generator.py (cbce3e0057ea6cd7..., asserts the Humanize_AI scan). Generator checks (exact): all five formulas for every n <= 20,000 by enumeration (every solution lies in the Lean box), literal Lean box counts for n <= 60, 227,909 data of the golden route (representations of primes p < 10^4, multiplicativity of r(n)/w, index relations between the orders); witness n = 0; no finite search space
- Model outputs: none yet
- Rubric: planned 6 items (build + 5 proof-only). Expected: golden 6/6, a sorry-only or theorem-less output 1/6 = 17 percent
- Notes: Novelty 10 Oct: no representation counts for these forms in Mathlib (pinned; GaussianInt, jacobiSym, the Q(zeta_3) PID of FLT 3), TauCeti, FCBench, formal-conjectures, compfiles, PutnamBench, miniF2F, ProofNet, KummerCriterion, flt-regular, PNT+, catalan-lean4, Sequencelib, int-y1/proofs; web: none. Related (disclose): RamanujanLean proves Jacobi's r_2 and r_4 by q-series (different forms, different route). Rejected alternatives: Pell squares x^4 - Dy^2 = 1 (Cohn's covering fails for Q = 1 sequences), Fermat's equation mod p (Mathlib Jacobi sums), congruent numbers (formal-conjectures, FCBench). Checklist: short-core no, ladder partly (2 uses the ring of 1, 5 that of 4), textbook partly, Mathlib-assist partly, finite-manipulation no. Sources: Dirichlet, J. Reine Angew. Math. 19 (1839), 21 (1840); L. Lorenz (1871); N. A. Hall, Amer. J. Math. 62 (1940) 589-598; B. C. Berndt, Number Theory in the Spirit of Ramanujan (2006), ch. 3. Golden plan (about 1,500 lines: Euclidean rings Z[w], Z[sqrt -2], Z[(1 + sqrt -7)/2], splitting of primes, multiplicative counting by unique factorization, the index-2 orders Z[sqrt -3], Z[sqrt -7] with 2-adic cases, box bijection) in handoff section 44
- Next: The fellow pastes task27_prompt.txt on the platform and drops the outputs into tasks\task 27\model_outputs\
- Updated: 10 Oct 2026, about 22:20 IST (Humanize_AI rewrite, handoff section 45)

### Task 28 - Quartic and octic residuacity of 2 and -4, the unit 1 + sqrt 2, and Dirichlet's rational quartic law (Gauss, Dirichlet, Barrucand and Cohn, E. Lehmer)

- Status: prompt
- State: Prompt compiled officially (job t28_statements, 23:14-23:33 IST: build 0, five sorry warnings, check 0); handed over 10 Oct 2026, about 23:45 IST
- Laptop: Honor laptop
- Folder: tasks\task 28 (Honor laptop)
- Topic: p prime: p = 1 mod 4 gives (2 is a 4th power mod p iff p = a^2 + 64 b^2); p = 1 mod 8 gives (-4 is an 8th power iff p = a^2 + 32 b^2); p odd gives (2 is a 4th power iff e^2 = p + 2 f^2 with e = 1, 3 mod 8); p = 1 mod 4, q = 2, 3 mod 4, p = c^2 + q d^2 give (q is a 4th power iff J(q | c) = 1); p = 1 mod 8, s^2 = 2 give (1 + s is a square iff p = a^2 + 32 b^2). 5 theorems, no definitions; residues as equations in `ZMod p`, residue sets as `Membership.mem ({...} : Finset Nat) (e % 8)`
- Files: task28_prompt.txt (3,693 chars, sha256 a02e041812cf0d28...), TuringTask\Basic.lean (7752d25b7b39a9a7...), StatementAndAxiomsCheck.lean (50d915026cc4e099...), statements_worker_log.txt, model_outputs\.keep, generator turing_t28_generator.py (420c39cc517bad56..., asserts the Humanize_AI scan). Generator checks (exact): theorems 1, 2, 5 for every prime below 10^5 (4,783, 2,384, 2,384 primes), theorem 3 for every odd prime below 30,000 (3,244; the class of e mod 8 is the same for every representation in a window of several unit orbits), theorem 4 for 22,509 cases (p < 50,000, q < 160, all representations); Euler criterion against a literal search over ZMod p for p < 3000 (10,296); 28,734 data of the golden route (Dirichlet's formula 2^((p-1)/4) = (-1)^(b/4), J(a + b | p) = J(2 | a + b), (-q)^((p-1)/4) = J(q | c) J(2 | p)^v2(d), 2^((p-1)/4) = J(-2 | e), chi(1 + sqrt 2) = J(-1 | e + f), Thue representations c^2 + 2 d^2 and e^2 - 2 f^2, the unit step for p = 7 mod 8); witnesses for all 11 hypotheses (p = 7, 65, 5, 33, 2, 9, (49, 3, 1, 4), (7, 3, 2, 1), (61, 5, 4, 3), 7, 33); no finite search space
- Model outputs: none yet
- Rubric: planned 6 items (build + 5 proof-only). Expected: golden 6/6, a sorry-only or theorem-less output 1/6 = 17 percent
- Notes: Novelty 10 Oct: no quartic or octic residues, no representation x^2 + 2y^2 or x^2 - 2y^2 and no quartic Euler criterion in Mathlib (pinned; it has quadratic and Jacobi reciprocity, `Nat.Prime.sq_add_sq`, Jacobi sums); nothing in TauCeti, FCBench, formal-conjectures (its x^2 + 2y^2 + 32z^2 counts belong to Tunnell's theorem, a different statement), compfiles, PutnamBench, miniF2F, ProofNet, RamanujanLean, KummerCriterion, flt-regular, PNT+, catalan-lean4 (quartic_pell_two is x^4 - 2y^2 = 1, unrelated), Sequencelib, int-y1/proofs; web: no formalization. Related to task 9 (cubic residuacity of 2 via Jacobi sums): this task avoids Jacobi sums and uses Jacobi-symbol reciprocity only. Rejected alternative: quartic residuacity of 3, 5, -3 via E. Lehmer's criteria x^2 + 144y^2, x^2 + 100y^2, x^2 + 36y^2 (numerics pass, but the proofs go through quartic reciprocity in Z[i]; golden too long). Checklist: short-core no, ladder partly (5 reuses the core of 2), textbook partly (1 is in Cox and Lemmermeyer), Mathlib-assist no, finite-manipulation no. Sources: C. F. Gauss, Theoria residuorum biquadraticorum I (1828); P. G. L. Dirichlet, J. Reine Angew. Math. 57 (1860) 187-188; P. Barrucand and H. Cohn, J. Reine Angew. Math. 238 (1969) 67-70; E. Lehmer, Rational reciprocity laws, Amer. Math. Monthly 85 (1978) 467-472; F. Lemmermeyer, Reciprocity Laws (Springer 2000), ch. 5; D. A. Cox, Primes of the Form x^2 + ny^2, 2nd ed. (2013), ch. 1. Golden plan (about 1,100 lines: quartic and octic Euler criteria, Thue representations, Dirichlet's Jacobi-symbol computations, mod 16 case analyses) in handoff section 46
- Next: The fellow pastes task28_prompt.txt on the platform and drops the outputs into tasks\task 28\model_outputs\
- Updated: 10 Oct 2026, about 23:45 IST

### Task 29 - Signs of arithmetic permutations: multiplication maps, power maps and the transpose (Zolotarev, Lerch, Frobenius)

- Status: prompt
- State: Prompt compiled officially (job t29_statements, 23:33-23:37 IST: build 0, five sorry warnings, check 0); handed over 10 Oct 2026, about 23:45 IST
- Laptop: Honor laptop
- Folder: tasks\task 29 (Honor laptop)
- Topic: sgn of x -> a x on ZMod n (a coprime to n): equals J(a | n) for n odd; equals 1 for n = 2 mod 4 and (-1)^((a-1)/2) for 4 | n; on the unit group (ZMod n)^* the sign of x -> u x is -1 iff u is a non-square and n is 4, p^k or 2 p^k (p odd prime, k >= 1); for p prime and x -> x^k bijective on ZMod p the sign is -1 iff p = 1 mod 4 and k = 3 mod 4; the transpose i n + j -> j m + i of Fin (m n) has sign (-1)^(C(m,2) C(n,2)). 5 theorems, no definitions; `Units.mulLeft (ZMod.unitOfCoprime a ha)`, `Equiv.mulLeft u`, `Equiv.ofBijective`, `finProdFinEquiv`, instance `NeZero n`
- Files: task29_prompt.txt (4,257 chars, sha256 a62637ee5ea5a3ba...), TuringTask\Basic.lean (914c3d5f9f2acd5d...), StatementAndAxiomsCheck.lean (3242eb938a730d24...), statements_worker_log.txt, model_outputs\.keep, generator turing_t29_generator.py (4cfd16311119e7d1..., asserts the Humanize_AI scan). Generator checks (exact, signs from the cycle decomposition): theorem 1 for every odd n < 400 and a < 2n (64,731), theorem 2 for every even n < 400 (32,306), theorem 3 for every unit of every n < 300 (27,318), theorem 4 for every prime p < 400 and bijective k < 3p (15,865), theorem 5 for m, n <= 14 with the inversions counted exactly (225); 221,459 data of the golden route (sign = (-1)^(size - cycles), multiplicativity under the Chinese remainder theorem, values on Z/p^k and Z/2^k, discrete logarithm turning x -> x^k into y -> k y on Z/(p - 1), 2-parts of orders); witnesses: n = 4, a = 3 (theorem 1 needs n odd), n = 5, a = 4 (theorem 2 needs n even), n = 15, k = 3 (theorem 4 needs p prime); no finite search space
- Model outputs: none yet
- Rubric: planned 6 items (build + 5 proof-only). Expected: golden 6/6, a sorry-only or theorem-less output 1/6 = 17 percent
- Notes: Novelty 10 Oct: nothing links permutation signs with Jacobi or Legendre symbols in Mathlib (pinned; it has `Equiv.Perm.sign`, `ZMod.isCyclic_units_iff`, Gauss's and Eisenstein's lemmas); no Zolotarev, Frobenius or Lerch in TauCeti, FCBench, formal-conjectures, compfiles, PutnamBench, miniF2F, ProofNet, RamanujanLean, KummerCriterion, flt-regular, PNT+, catalan-lean4, Sequencelib, int-y1/proofs (Perm.sign appears there for unrelated purposes); web: only expository papers (M. Baker, Zolotarev's magical proof of quadratic reciprocity, arXiv 2603.00278, March 2026, no formalization). The prime case (Zolotarev's lemma) is left out because it is the special case n = p of theorem 1. Rejected alternative: parity of class numbers through ambiguous forms (numerics pass, including 8 | h(-4p) iff p = x^2 + 32y^2); the 4-rank and 8-rank parts need composition of forms and the parity parts share one involution. Checklist: short-core no, ladder no, textbook partly (Zolotarev's lemma appears in some texts), Mathlib-assist partly (cyclic units criterion), finite-manipulation no. Sources: G. Zolotarev, Nouv. Ann. Math. (2) 11 (1872) 354-362; M. Lerch, Sur un theoreme de Zolotarev, Bull. Intern. Acad. Francois Joseph 3 (1896) 34-37; G. Frobenius, Uber das quadratische Reziprozitatsgesetz I, Sitzungsber. Preuss. Akad. Wiss. Berlin (1914) 335-349; F. Lemmermeyer, Reciprocity Laws (Springer 2000), ch. 1; arXiv 1810.03006 (applications of Lerch's theorem to permutations of quadratic residues). Golden plan (about 1,450 lines: regular permutations of finite groups, CRT product signs, prime-power layers, 2-adic layers, discrete logarithm, inversion count of the transpose) in handoff section 46
- Next: The fellow pastes task29_prompt.txt on the platform and drops the outputs into tasks\task 29\model_outputs\
- Updated: 10 Oct 2026, about 23:45 IST

### Task 30 - Dedekind sums: Knopp's Hecke identity, denominators, Rademacher's congruence mod 8, vanishing and equality criteria (Dedekind, Rademacher, Knopp, Jabuka, Robins and Wang)

- Status: prompt
- State: Prompt compiled officially (job t30_statements, 23:37-23:39 IST: build 0, five sorry warnings, check 0); handed over 10 Oct 2026, about 23:45 IST
- Laptop: Honor laptop
- Folder: tasks\task 30 (Honor laptop)
- Topic: s(h, k) = sum_{r=1}^{k-1} ((r/k)) ((h r/k)), s(h, 0) = 0: sum_{d | n} sum_{b < d} s((n/d) h + b k, d k) = sigma(n) s(h, k) for all h, k, n; 2 gcd(3, k) k s(h, k) is an integer for all h, k; k odd, gcd(h, k) = 1 give 12 k s(h, k) = k + 1 - 2 J(h | k) mod 8; k >= 1, gcd(h, k) = 1 give (s(h, k) = 0 iff k | h^2 + 1); k prime, a, b coprime to k give (s(a, k) = s(b, k) iff a = b or a b = 1 mod k). 5 theorems, no definitions: each theorem takes `s : Nat -> Nat -> Rat` with a hypothesis `hs` that fixes it by the sawtooth formula over `Finset.range y`
- Files: task30_prompt.txt (4,566 chars, sha256 578769cb225df723...), TuringTask\Basic.lean (1f327aa95d29e6f2...), StatementAndAxiomsCheck.lean (1105b3d050a77d72...), statements_worker_log.txt, model_outputs\.keep, generator turing_t30_generator.py (0e9aeac0c4af753d..., asserts the Humanize_AI scan). Generator checks (exact, fractions): the Lean formula equals the sawtooth definition for k < 70 (4,968); theorem 1 for k <= 24, h <= 2k + 1, n <= 14 (9,750); theorem 2 for k <= 200, h <= 3k (60,501); theorem 3 for odd k <= 301 (36,970); theorem 4 for k <= 300 (54,796); theorem 5 for every prime k < 200 and all a, b < 2k (2,226,628 pairs); 28,171 data of the golden route (reciprocity law, 12 h k s = h^2 + 1 mod gcd(3, k) k, symmetries, reduction s(g h, g k) = s(h, k), multiplication formula for the sawtooth); witnesses for all 7 hypotheses ((1, 2), (3, 3), (1, 0), (2, 2), (4, 9, 25), (5, 2, 5), (2, 5, 5)); no finite search space
- Model outputs: none yet
- Rubric: planned 6 items (build + 5 proof-only). Expected: golden 6/6, a sorry-only or theorem-less output 1/6 = 17 percent
- Notes: Novelty 10 Oct: no Dedekind sums in Mathlib (pinned) or in TauCeti, FCBench, formal-conjectures, compfiles, PutnamBench, miniF2F, ProofNet, RamanujanLean, KummerCriterion, flt-regular, PNT+, catalan-lean4, Sequencelib, int-y1/proofs. Near match to disclose: Isabelle AFP entry Dedekind_Sums (M. Eberl, A. Bordg, L. C. Paulson, W. Li, April 2025) formalizes Apostol ch. 3 (reciprocity and the congruences, so it covers theorems 2 and 3 in Isabelle); nothing in Lean; theorems 1, 4, 5 are not in that entry. Flagged to Fahad: sawtooth sums sit next to the exponential-sum area he asked to avoid (no characters appear). Rejected alternative: multiperfect, harmonic and unitary perfect numbers with few prime factors (numerics pass to 2 * 10^7; golden route not secured for the two-prime harmonic case; Euler's form for odd perfect numbers is a FormalConjectures-Bench task). Checklist: short-core no, ladder partly (4 and 5 use the congruence 12 h k s = h^2 + 1 mod k), textbook partly (2 and 3 are in Apostol and Rademacher-Grosswald), Mathlib-assist no, finite-manipulation no. Sources: R. Dedekind, Erlauterungen zu zwei Fragmenten von Riemann (1892); H. Rademacher and E. Grosswald, Dedekind Sums (MAA Carus 16, 1972); T. M. Apostol, Modular Functions and Dirichlet Series, 2nd ed. (1990), ch. 3; M. I. Knopp, J. Number Theory 12 (1980) 2-9; T. M. Apostol and T. H. Vu, J. Number Theory 14 (1982) 391-396; S. Jabuka, S. Robins, X. Wang, When are two Dedekind sums equal?, arXiv 1103.0370 (2011). Golden plan (about 1,500 lines: sawtooth calculus, reciprocity by lattice points, floor formula for the denominators, Euclid-type induction for the mod 8 law, Knopp by the multiplication formula and Moebius inversion) in handoff section 46
- Next: The fellow pastes task30_prompt.txt on the platform and drops the outputs into tasks\task 30\model_outputs\
- Updated: 10 Oct 2026, about 23:45 IST

### Task 31 - Coefficients of binary and ternary cyclotomic polynomials (Migotti, Bang, Carlitz, Lenstra, Lam and Leung, Kaplan, Gallot and Moree)

- Status: prompt
- State: Prompt compiled officially (job t31_statements, 11 Oct, 3.54 to 4.05 IST: build 0, five sorry warnings, check 0 with sorryAx only); handed over 11 Oct 2026, about 4.10 IST
- Laptop: Honor laptop
- Folder: tasks\task 31 (Honor laptop)
- Topic: a_n(k) = coefficient of x^k in Phi_n, p, q, r primes (not necessarily distinct): for p != q every partial sum a_pq(0) + ... + a_pq(k) is 0 or 1 (flat, alternating, starting with 1); with u < q, v < p, u p = 1 mod q, v q = 1 mod p, exactly u v coefficients of Phi_pq equal 1; |a_pqr(k)| <= p - 1; r = +-1 mod p q makes Phi_pqr flat; |a_pqr(k + 1) - a_pqr(k)| <= 1. 5 theorems, no definitions; coefficients as `(Polynomial.cyclotomic n Int).coeff k`, value sets as `Membership.mem ({...} : Finset Int)`
- Files: task31_prompt.txt (3,761 chars, sha256 ff80b104e54d1895...), TuringTask\Basic.lean (35ee3145112a5fe4...), StatementAndAxiomsCheck.lean (a072e48935ae38cc...), statements_worker_log.txt, model_outputs\.keep, generator turing_t31_generator.py (442eeed4c98cd293..., asserts the Humanize_AI scan). Generator checks (exact): Phi_n from the product formula, compared with long division for n <= 400; theorems 1 and 2 for 2,956 ordered pairs of distinct primes (p, q < 300, p q <= 30,000); theorems 3 and 5 for 23,792 ordered prime triples (repetitions and 2 allowed, p q r <= 40,000); theorem 4 for 15,611 triples with r = +-1 mod p q (p q r <= 150,000); 4,270 data of the golden route (Lam-Leung positions of 1 and -1, Kaplan's lemma for every coefficient of the odd triples with p q r <= 8000, the identity Phi_pq (x^p - 1)(x^q - 1) = (x^pq - 1)(x - 1), Phi_2m(x) = Phi_m(-x), Phi_pm(x) = Phi_m(x^p) for p | m); witnesses for all 19 hypotheses (Phi_4, Phi_105, Phi_12, Phi_15 with wrong u or v, Phi_210, Phi_(15*7*211)); no finite search space
- Model outputs: none yet
- Rubric: planned 6 items (build + 5 proof-only). Expected: golden 6/6, a sorry-only or theorem-less output 1/6 = 17 percent
- Notes: Novelty 11 Oct: Mathlib (pinned) has `Polynomial.cyclotomic`, `prod_cyclotomic_eq_X_pow_sub_one`, `cyclotomic_expand_eq_cyclotomic` and nothing on the coefficients of Phi_pq or Phi_pqr. Near match to disclose: Mathlib's Counterexamples/Cyclotomic105.lean proves that Phi_105 has the coefficient -2 (so not every cyclotomic polynomial is flat). formal-conjectures has OEIS sequences of cyclotomic values (A070518, A117545), unrelated. Nothing in the other bench repositories; web: the survey and the papers, no formalization. Rejected alternative: Carmichael numbers with three prime factors and smallest prime 3, 5, 7 (Korselt plus Beeger's bound reduces to a finite search; formal-conjectures defines IsCarmichael). Checklist: short-core no, ladder partly (1 and 2 share the Lam-Leung expansion, 3 to 5 share Kaplan's lemma), textbook no, Mathlib-assist partly (cyclotomic basics only), finite-manipulation no. Sources: A. Migotti, Wiener Berichte 87 (1883) 8-14; A. S. Bang, Nyt Tidsskr. Math. 6 (1895) 6-12; L. Carlitz, Amer. Math. Monthly 73 (1966) 979-981; T. Y. Lam and K. H. Leung, Amer. Math. Monthly 103 (1996) 562-564; N. Kaplan, J. Number Theory 127 (2007) 118-126; Y. Gallot and P. Moree, J. Ramanujan Math. Soc. 24 (2009) 235-248; C. Sanna, A survey on coefficients of cyclotomic polynomials, arXiv 2111.04034 (2021). Golden plan (about 1,400 lines: Lam-Leung expansion, power-series partial sums, reductions for repeated primes and the prime 2, Kaplan's lemma, separable binary coefficients in lattice coordinates) in handoff section 47
- Next: The fellow pastes task31_prompt.txt on the platform and drops the outputs into tasks\task 31\model_outputs\
- Updated: 11 Oct 2026, about 4.10 IST

## Reviews

### Task 5 - Alexey, 2026-10-08, "Minor issue"

- Feedback: Golden zip used a git Mathlib require. Use the pinned checkout at /opt/mathlib4 in lakefile.toml and lake-manifest.json, then check a fresh extract offline (lake build and lake env lean StatementAndAxiomsCheck.lean) with no edits. Rubric: add a build item (pinned Lean and Mathlib, build includes TuringTask/Basic.lean); criteria 3 and 5 mixed definition fidelity with completed proofs; rerun grading for the golden and both responses.
- Action: v2 zip with path /opt/mathlib4, environment manifest and README; offline fresh-extract check passed. Rubric now 8 items: 2 anchors, 5 proof-only items, build item. Short reply drafted for Alexey.
- State: Fixed, awaiting re-review (resolved: no)

## Project rules (from the tracker meta document)

- Pinned environment, never change: Lean leanprover/lean4:v4.33.0-rc1, Mathlib 9944fe2973b8dc0b86949101ed98232c07cd54a0.
- One chat per task. Read this tracker first and update it after every step (prompt, outputs, golden, platform scores, submit, review).
- Task numbers: take the next free number from this tracker and reserve the row before creating files. Number 7 was used on both laptops; the Honor laptop's task 7 is listed as 7.5.
- Write the golden only after a model output genuinely fails (an environment failure does not count). The golden is own work, never copied from a model output.
- Golden zip: lakefile.toml requires Mathlib with path = /opt/mathlib4, lake-manifest.json in the environment form, README with lean-offline-init, lake build, lake env lean StatementAndAxiomsCheck.lean. Run the offline fresh-extract check before delivering.
- Rubric: at most 2 definition anchors, one proof-only item per theorem (exact statement; #print axioms only propext, Classical.choice, Quot.sound), one build item. Never put a definition inside a proof item. A sorry-only output must stay below 40 percent. Prompts without definitions give build + 5 proofs = 6 items (sorry-only 17 percent, one proof 33 percent).
- Topics: one hard classical core that all five theorems need. Elementary or glue work (tasks 1-3) was solved by every model.
- Novelty check before every task: Mathlib at the pinned commit, PutnamBench, miniF2F, ProofNet, compfiles, formal-conjectures, TauCeti, RamanujanLean, riccardobrasca/KummerCriterion (Kummer congruences, Gauss sum sign), web search.
- Platform: upload the rubric CSV in the model-response section and run it, download it, upload the same CSV in the golden section and run it. Targets: golden at least 90 percent, at least one model below 40 percent.
- Everything pasted into a submission field is pure ASCII and generated by script. Explanations in Markdown: ### headings, - bullets, math in $...$.
- Be brief. Say plainly what is verified and what is not. Never promise a model failure or a reviewer score.

## Laptops

- waris-pc: folder `C:\Users\bhatw\OneDrive\Desktop\Project Turing`. Tasks 1-5 and 7. Lean in C:\lean\TuringTask (lean_worker.bat). Long details: TURING_HANDOFF_2026-10-06.md, newest sections 17-20.
- Honor laptop (device fahad): folder `D:\HandShake\project turing\Project Turing`. Tasks 6, 7.5 (its folder is tasks\task 7), 8, 9, 10, 11. Lean moved to D:\lean\TuringTask on 8 Oct (C: was full); lean_worker.bat uses it. Give a new chat access to D:\HandShake\project turing and D:\lean. Never build several Mathlib files in parallel here. Golden fresh-copy check: verify_golden_offline.bat <task>. Opening prompt for golden chats: NEW_CHAT_PROMPT_GOLDEN.txt. Details: TURING_MEMORY.md and TURING_HANDOFF_2026-10-06.md sections 17-24.


# Project Turing — Lean Data Creation Playbook

*Formalize. Verify. Repeat.*

> **Source:** screen captures of `project-turing-24.learn.joinhandshake.com`, taken 2026-10-06.
> **Pages covered (9):** Home, Ground Rules, Task Flow, Writing Prompts, Checking Model Output, Golden Answers, Writing Rubrics, Worked Examples, Offline Lean Setup.
> **Pages not covered (no capture available):** Project Leadership, Changelog.

---

## Contents

1. [Overview](#1-overview)
2. [Score targets](#2-score-targets)
3. [Ground rules](#3-ground-rules--non-negotiables-for-every-turing-task)
4. [The task flow](#4-the-task-flow)
5. [Writing prompts](#5-writing-prompts)
6. [Checking the initial model output](#6-checking-the-initial-model-output)
7. [Writing the golden answer](#7-writing-the-golden-answer)
8. [Writing and refining the rubric](#8-writing-and-refining-the-rubric)
9. [Worked examples](#9-worked-examples)
10. [The offline Lean environment](#10-the-offline-lean-environment)
11. [Site map](#11-site-map)
12. [Pages not yet captured](#12-pages-not-yet-captured)

---

## 1. Overview

On Project Turing, you will create RLE data to train models in **Lean proof writing** and **natural-language-to-Lean formalization**.

## 2. Score targets

**The targets that shape everything:** the rubric must reward your golden answer and punish the failing model rollouts.

```
Golden answer    ≥ 90%
At least 1 of 3 model rollouts < 40%
```

---

## 3. Ground rules — non-negotiables for every Turing task

These rules apply to proof-writing and formalization tasks alike. A task that breaks any of them is not ready to submit, regardless of how much work went into it.

### Rule 1 — The rubric must hit its score targets

Every criterion is a binary check graded **MET** or **UNMET** and carries a weight of **+1** — 5 to 20 criteria in total. The score is criteria met ÷ total criteria.

```
Golden answer    ≥ 90%
At least 1 of 3 model rollouts < 40%
```

If either target is missed, revise the rubric or the task before submitting.

### Rule 2 — Follow the task flow exactly

Write the prompt, let the platform generate the three model outputs, confirm the failure, write the golden, write the rubric, let the judge model grade, then double-check the verdict.

- Do not add extra manual stages.
- Do not write the golden before you have seen the model outputs.

### Rule 3 — The failure must be genuine

At least one of the three model outputs must fail an objective requirement of the prompt. If all three are actually correct, revise or reject the task — never invent a criterion to force a failure.

An output that only fails because Lean, Mathlib, or an offline dependency is missing is an **environment failure, not a model failure**. That task is invalid.

### Rule 4 — Never grade on implementation style

Criteria may never require the golden's tactics, theorem names, or syntax.

Not allowed as criteria:

- ❌ Uses the same theorem as the golden.
- ❌ Uses the intended tactic.
- ❌ Follows the reference proof.
- ❌ Uses idiomatic Mathlib.
- ❌ Is concise and elegant.

Accept any output that satisfies the mathematics and the Lean integrity requirements.

### Rule 5 — Lean decides, not the grader model

Compilation, elaborated-type, and axiom claims must be checked against your own Lean run in the pinned environment. The grading model is evidence, not proof.

### Rule 6 — One frozen toolchain and Mathlib4 commit

All models run internally against a single frozen Lean toolchain and a single frozen commit of `mathlib4`. Every prompt, golden answer, and verification run must compile against them — no newer, no older.

| Item | Pinned value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.33.0-rc1` |
| `mathlib4` commit | `9944fe2973b8dc0b86949101ed98232c07cd54a0` |

### Rule 7 — The task must be new Lean work

Known mathematics is welcome: a classical theorem with no Lean formalization is a good task. What is not allowed is work that already exists in Lean.

Not allowed:

- ❌ A statement or theorem already in Mathlib at the pinned commit. Search the Mathlib source before you start.
- ❌ A problem taken from a public Lean benchmark or a public Lean repository, such as miniF2F, ProofNet or PutnamBench.
- ❌ A golden answer copied from someone else's Lean code. The golden must be your own work.

If the mathematics comes from a paper or a textbook, name the source in your step-by-step explanation and state the mathematics in your own words.

### If you are unsure — uncertainty is not a pass

If the grader cannot assess a criterion, the task is not ready. Resolve the uncertainty, clarify the criterion, or reject the task — do not treat uncertainty as either a pass or a failure.

---

## 4. The task flow

Seven steps, in this order, with no extra manual stages. The tasker is expected to see the three model outputs before writing the golden and the rubric.

| # | Step | What happens | Who |
| --- | --- | --- | --- |
| 1 | **Write the prompt** | State the mathematics, the task type, the required file and declaration, imports, helper policy, prohibited escapes, versions, and the check command. | You |
| 2 | **The platform generates three model outputs** | One from each of three models. This is automatic. You do not write them and you do not fix them. | Automatic |
| 3 | **Check that at least one output genuinely fails** | Inspect the actual generated files for each model, not just the model's prose summary. | You |
| 4 | **Write the golden answer** | Written only after the failure is confirmed. It must compile and answer the exact prompt. | You |
| 5 | **Write the rubric** | Written after the golden. Every criterion required, atomic, positive, binary, and prompt-grounded. | You |
| 6 | **A judge model grades the three outputs and your golden** | Automatic. One verdict per criterion, each with evidence. | Automatic |
| 7 | **Double-check the grader** | Confirm each failing output was failed for a correct, prompt-grounded reason with accurate evidence, and that your golden scored 90% or higher. | You |

---

## 5. Writing prompts

The prompt is the contract. Every requirement that will later appear in the rubric must be stated — or directly implied — here first.

### 5.1 Every prompt must state

- ✅ The mathematical problem.
- ✅ Whether the task is proof writing or formalization.
- ✅ The required output file.
- ✅ The required declaration name.
- ✅ The imports or import policy.
- ✅ Whether helper declarations are allowed.
- ✅ The prohibition on `sorry`, new axioms, or other proof escapes.
- ✅ The relevant Lean and Mathlib versions.
- ✅ The command the model can use to check its work.

### 5.2 The two task types

#### Proof-writing prompts

Give the exact Lean theorem signature. The model may use any valid proof strategy.

**Template:**

```text
Create a Lean project and prove the following theorem in `<file>`.

<imports, namespace, variables, and exact theorem signature>

You may introduce helper lemmas and use any kernel-checkable proof strategy.
Do not use `sorry`, add axioms, or change the theorem statement.
Verify your project with `<command>`.
```

**Do not require a particular tactic, theorem name, proof length, or reference strategy.**

#### Formalization prompts

State the mathematics unambiguously: domains, quantifier dependencies, hypotheses, conclusion, and any endpoint or indexing conventions. Request a transparent proposition definition.

**Requested shape:**

```lean
def CandidateStatement : Prop := ...
```

All mathematical term variables should be quantified inside the definition body. Explicit universe parameters are allowed when needed.

A proposition definition avoids forcing the model to prove the proposition or insert `sorry`. The mathematical translation is the *body* of the definition, not its declared type `Prop`.

### 5.3 The API-neutrality check

Reject or rewrite a prompt when the real challenge is remembering one obscure declaration name. A suitable task should allow:

- ✅ Direct proof from definitions.
- ✅ A different collection of library lemmas.
- ✅ Helper lemmas.
- ✅ Local source search.
- ✅ Reasonable equivalent formal representations.

Providing local Mathlib source is necessary but not sufficient. If almost every successful solution depends on one non-obvious declaration, and supplying its name makes the task trivial, the task is primarily API recall.

### 5.4 Before you submit the prompt — prompt checklist

- [ ] The mathematics is correct and unambiguous.
- [ ] The required file and declaration are explicit.
- [ ] Every future rubric requirement is stated or directly implied.
- [ ] The task tests mathematical Lean work rather than one API name.
- [ ] The statement is not already in Mathlib at the pinned commit or in a public Lean benchmark.

---

## 6. Checking the initial model output

The platform produces three outputs, one per model. Check each one; at least one must genuinely fail. Inspect the actual generated files, not only the model's final prose. One genuine required-property failure is enough for the task to proceed.

### 6.1 What counts as a genuine failure

#### Proof-writing tasks

- ✅ The required theorem is absent.
- ✅ The theorem has the wrong elaborated type.
- ✅ The project or target file does not compile.
- ✅ The proof leaves an unsolved goal.
- ✅ The proof uses `sorry`, an unapproved axiom, or another prohibited escape.
- ✅ The proof establishes a different theorem.
- ✅ The proof times out under a reasonable, predeclared limit.

#### Formalization tasks

- ✅ The submitted Lean declaration does not compile.
- ✅ It uses the wrong mathematical objects or types.
- ✅ It has the wrong quantifier order or binder dependency.
- ✅ It omits, adds, or changes a hypothesis.
- ✅ It reverses an implication.
- ✅ It changes a strict inequality into a weak one, or changes another boundary convention.
- ✅ It makes the statement stronger, weaker, or vacuous.
- ✅ It formalizes a nearby but different natural-language claim.

#### Not a suitable failure

Unless the prompt explicitly required them:

- ❌ Using a different tactic.
- ❌ Using a different Mathlib theorem.
- ❌ Choosing different binder names.
- ❌ Adding harmless helper lemmas.
- ❌ Using a term proof instead of a tactic proof.
- ❌ Producing a longer or less elegant proof.
- ❌ Choosing a mathematically equivalent standard representation.
- ❌ Failing to guess the golden answer's API names.

**If the initial output is actually correct, do not invent a criterion to force it to fail. Reject or revise the prompt and generate a new output. If the output fails only because Lean, Mathlib, or an offline dependency is missing, the task is invalid.**

### 6.2 How to check

#### A. Proof-writing output

1. The required project and source file exist.
2. The project builds in the pinned environment.
3. The requested declaration exists.
4. Its elaborated type matches the prompt.
5. The proof has no `sorry` or prohibited axiom dependency.
6. The failure is reproducible.

**Record a short factual failure statement**, for example:

```text
The target theorem fails to elaborate because the proof applies the induction
hypothesis at the wrong index.
```

#### B. Formalization output

First confirm the submitted proposition definition compiles. Then compare its meaning with the natural-language prompt, checking separately:

- ✅ Objects and types.
- ✅ Binders, scope, and dependencies.
- ✅ Hypotheses and side conditions.
- ✅ Conclusion, connective, and direction.
- ✅ Constants, indices, endpoints, and exceptional cases.

| ❌ Wrong way to judge | ✅ Right way to judge |
| --- | --- |
| Textual similarity to the future golden, or the fact that both propositions are true and an ↔ can be proved between them. | Whether the candidate expresses the requested mathematical structure. |

**Record the smallest decisive semantic failure**, for example:

```text
The output states `∃ y, ∀ x, R x y`, requiring one fixed witness, while the
prompt requires `∀ x, ∃ y, R x y`, allowing the witness to depend on `x`.
```

### 6.3 Acceptance — initial-output checklist

- [ ] The actual generated files were inspected.
- [ ] The output genuinely fails the prompt.
- [ ] The failure is mathematical, semantic, compilation-related, or proof-integrity-related.
- [ ] The failure is not caused by a broken environment.
- [ ] If the output was correct, the task was revised or rejected.

---

## 7. Writing the golden answer

The golden is written after the initial output has been checked and confirmed to fail. It proves the task is solvable as written.

### 7.1 Requirements

- ✅ Answers the original prompt exactly.
- ✅ Uses the required file and declaration name.
- ✅ Satisfies every rubric criterion.
- ✅ Demonstrates that the task is solvable as written.

**Compiles against the frozen environment:**

| Item | Pinned value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.33.0-rc1` |
| Mathlib4 commit | `9944fe2973b8dc0b86949101ed98232c07cd54a0` |

**Submit the whole project as a zip.** The golden answer is not a code snippet. It must be an entire Lean project — lakefile, toolchain pin, and all source files — archived as a `.zip` and uploaded to the platform, so it can be built end to end exactly as submitted.

**A correct answer, not the only answer.** The golden's tactic choices, theorem names, binder names, helper lemmas, and syntax are not rubric requirements. Any other correct solution must be able to pass.

### 7.2 By task type

#### Proof-writing golden

The golden must contain a complete kernel-checkable proof of the exact requested theorem.

#### Formalization golden

- ✅ One canonical Lean proposition.
- ✅ A short plain-language explanation of its binders, assumptions, and conclusion.
- ✅ Notes on important equivalent standard representations, when applicable.
- ✅ At least one example or counterexample when needed to distinguish a likely mistranslation.

The golden may correct the initial model's mistake, but it must be derived from the prompt's intended mathematics — not produced by editing the model output until it looks different.

### 7.3 Acceptance — golden checklist

- [ ] The golden was written after the failed output was confirmed.
- [ ] It is a complete Lean project uploaded to the platform as a zip file.
- [ ] It compiles in the pinned environment.
- [ ] It answers the exact prompt.
- [ ] It contains no prohibited proof escape.
- [ ] It will pass every rubric criterion.

### 7.4 Step-by-step solution explanation

**Written in the Golden Answer text box.** Write the step-by-step explanation in the text box of the Golden Answer section, next to the zip upload. It walks through the golden's code in order and explains what it does.

- ✅ Written in the Golden Answer text box, not inside the zip.
- ✅ Follows the code in order, one step at a time.
- ✅ Explains what each definition, helper lemma, and major proof step does.
- ✅ Shows how the steps together establish the required statement.

---

## 8. Writing and refining the rubric

The rubric is written after the golden. Build it from the task and your golden answer — never from the model responses you happened to see.

**The draft is generated — refining it is the job.** The platform auto-generates a rubric from your prompt and golden answer. It is never submission-ready: it invents criteria the prompt never asked for, misses the defect that actually matters, hides compound checks inside one line, and weights criteria unevenly. Treat the draft as raw material and edit every line.

### 8.1 The refinement pass

1. **Cut what the prompt never required.** Delete any criterion that is not traceable to an explicit requirement of the prompt, and any criterion that only describes what your golden happens to do — a chosen tactic, a chosen decomposition, a particular Mathlib lemma.

2. **Split compound criteria.** If a drafted line contains "and", "including", or a list, it is almost certainly two or three criteria wearing one weight. Split until each line can only be MET or UNMET.

3. **Rewrite process and vibe language.** Auto-generated criteria love verbs like *derives*, *accounts for*, and *correctly*. Replace each with the final state a grader can point to.

   | ❌ Not acceptable | ✅ Acceptable |
   | --- | --- |
   | The response correctly accounts for the nonemptiness assumption. | The submitted proposition includes the hypothesis that the set is nonempty. |

4. **Add the criteria the draft missed.** The draft rarely captures the specific defect you observed in the model outputs. Add criteria that make that defect fail — stated as a general mathematical requirement, not as a ban on the exact string the model produced.

5. **Set every weight to +1.** Every criterion is a binary check with weight **+1**, stating a condition a correct response satisfies. If a criterion feels like it should be worth more, it is usually hiding several checks — split it instead. Check that no single miss is counted twice.

6. **Test against the targets.** Run both evaluations. If the golden scores below 90%, a criterion is over-specified or unfair to valid alternate routes. If none of the 3 model rollouts scores below 40%, the rubric is not capturing the failure — the criteria are too generous or too generic.

### 8.2 The four principles

| # | Principle | Meaning |
| --- | --- | --- |
| 1 | **Atomic** | Checks exactly one thing. If a criterion could plausibly be half-right, split it into two. |
| 2 | **Self-contained** | Gradable from the criterion text alone. Name the mathematical fact, never a file, a golden, or a source. |
| 3 | **Objective** | Two graders reach the same verdict. No vibe words, no judgment calls. |
| 4 | **Verifiable** | Points to evidence visible in the model's output or in a verified Lean result. |

### 8.3 Grade the final state — never the process

Three families of language always creep into auto-generated drafts. Ban them and rewrite each criterion as "The response states X" with the exact final statement, term, or outcome a grader can point to.

| Family | Words to ban |
| --- | --- |
| **Process words** | proves, derives, works out, figures out, computes |
| **Mind-reading words** | understood, considered, took into account, recognized, accounted for |
| **Vibe words** | clean, idiomatic, elegant, clear, appropriate, thorough, correctly, robust, sound |

### 8.4 Weights

Every criterion is binary and carries the same weight: **+1**, for a condition the response must satisfy. No other values — no negatives, no zeros, no decimals, no scaling by importance. The score is criteria met ÷ total criteria. 5–20 criteria in total; lean rubrics grade better than exhaustive ones.

**+1 — Requirements:**

- ✅ The target statement is correct and the proof genuinely closes the goal.
- ✅ A required hypothesis, binder structure, or intermediate result is right.
- ✅ Naming, file placement, and stated conventions are followed.

### 8.5 Score targets — perfect score, with wiggle room

Your golden answer must score **90% or above** against your own rubric — with wiggle room, so alternate valid proof routes you documented still pass. At least one of the 3 model rollouts must score **below 40%**.

- ✅ Avoid double-counting: do not check the same miss in two criteria.
- ✅ Judgment outputs — chosen tactics, chosen decomposition — stay unpinned.

### 8.6 Required minimums

- ✅ 5–20 criteria in total. Do not pad to reach 5; exceed 20 and the rubric is rejected.
- ✅ Every weight is +1. No negatives, no zeros, no decimals.
- ✅ Every criterion is a binary check — MET or UNMET, with nothing in between.
- ✅ Positive criteria for the decisive statement, the final result, required hypotheses, binder structure, and intermediate results.
- ✅ A few positive anchors for naming, placement, and documented conventions.

### 8.7 Criterion format

On the platform, each criterion is one sentence with a weight of 1. There are no other fields.

Example: *In the definition CandidateStatement, the existential witness is inside the scope of the universal binder, so it may depend on the universally quantified input.*

**Every criterion states its own pass/fail condition.** A criterion is not finished until its one sentence makes clear exactly what counts as MET. The platform has no separate met and unmet fields, so the sentence itself must do that work. Two graders reading the same output must reach the same verdict without interpreting intent.

| ❌ Not acceptable | ✅ Acceptable |
| --- | --- |
| The proposition handles quantifiers correctly. | The proposition has the dependency pattern ∀ x, ∃ y, ..., so the witness may depend on x. |

### 8.8 Anti-patterns

#### Candidate-informed, not candidate-specific

It is appropriate for the initial output to reveal that quantifier dependency matters. It is not appropriate to grade the exact string it produced.

| ❌ Not acceptable | ✅ Acceptable |
| --- | --- |
| The answer must not use the exact code `∃ y, ∀ x, ...` seen in the model output. | The witness may depend on the universally quantified input. |

The first targets one string. The second captures the mathematical requirement and grades every possible output consistently.

#### Avoid compound criteria

| ❌ Compound | ✅ Split |
| --- | --- |
| The response uses the correct objects, includes every hypothesis, and reaches the correct conclusion. | • The proposition quantifies over the requested object type.<br>• The proposition includes the required nonemptiness hypothesis.<br>• The conclusion has the requested implication direction. |

Splitting them makes the grader's reason precise and lets each check stand or fall on its own.

#### Avoid API and reference matching

- ❌ Uses the same theorem as the golden.
- ❌ Uses `Function.comp`.
- ❌ Uses the intended tactic.
- ❌ Follows the reference proof.
- ❌ Uses idiomatic Mathlib.
- ❌ Is concise and elegant.

### 8.9 On the platform

| Topic | What to know |
| --- | --- |
| **The rubric starts auto-generated** | The platform drafts a rubric from your prompt and golden answer. That draft is a starting point, not an answer. |
| **You own the final quality** | Revising the draft is the work: add what it missed, cut what the prompt never asked for, and confirm every weight is +1. |
| **Two sections, one identical rubric** | One rubric section evaluates model responses, the other evaluates the golden answer. Finish the first, download the CSV, upload that exact file into the second. |
| **Score targets** | The golden answer must score 90% or higher. At least one of the 3 model rollouts must score below 40%. |

#### Running the evaluation

1. Complete and refine the rubric in the model-response section.
2. Download the finished rubric as a CSV.
3. Upload the same CSV into the golden answer rubric section — no edits, no re-typing.
4. Run both evaluations and check the scores against the targets.

If either target is missed, revise the rubric or the task before submitting.

### 8.10 Research basis

These rules reflect recurring findings on rubric reliability and model grading. The page links to the following references (link targets are not visible in the capture):

- Validating Proofs (Lean reference)
- Axioms (Lean reference)
- Ask, Don't Judge
- RubricBench
- Rethinking Rubric Generation
- MT-Bench and Chatbot Arena
- JudgeDeceiver

---

## 9. Worked examples

Two complete tasks — one proof-writing, one formalization — from prompt to final grader check. Use them as shape references, not as content to copy.

These examples show the shape of a task only. **Real tasks are harder and need at least 5 criteria.**

### 9.1 Example A — proof writing

**1. Prompt**

````text
Create a Lean project and prove the following theorem in `TuringTask/Basic.lean`.

import Mathlib

theorem sum_range_succ_mul_two (n : ℕ) :
    2 * (Finset.range (n + 1)).sum id = n * (n + 1) := by
  sorry

Replace `sorry` with a complete proof. You may introduce helper lemmas and use any
kernel-checkable proof strategy. Do not use `sorry`, add axioms, or change the theorem
statement. Toolchain: Lean 4 (pinned), Mathlib at the pinned commit.
Verify with `lake build`.
````

**2. Observed failure in the initial output**

```text
The target theorem fails to elaborate: the inductive step rewrites with
`Finset.sum_range_succ` at index `n` instead of `n + 1`, leaving an unsolved goal.
```

This is a genuine failure — the file does not compile and a goal is left open. It is not a style disagreement.

**3. Golden**

A complete kernel-checkable proof of the exact stated theorem in the required file, with no `sorry` and no axioms beyond the project's allowed policy. Any induction, closed-form, or library-based proof is equally acceptable.

**4. Rubric**

```text
P1 (+1). `sum_range_succ_mul_two` exists in the required file with the exact
        requested elaborated type.
P2 (+1). The submitted source and the target proof compile in the pinned environment.
P3 (+1). The target proof contains no `sorry` and depends on no prohibited axiom.
```

The initial output is **UNMET** on P2. No criterion mentions induction, tactics, or Mathlib lemma names.

### 9.2 Example B — formalization

**1. Prompt**

````text
In `TuringTask/Statement.lean`, formalize the following claim as a transparent
proposition definition named `CandidateStatement`.

  For every real number x there exists a natural number n with n > x.

Quantify all mathematical variables inside the definition body:

import Mathlib

def CandidateStatement : Prop := ...

Do not prove it and do not use `sorry`. Toolchain: Lean 4 (pinned), Mathlib at the
pinned commit. Verify with `lake env lean TuringTask/Statement.lean`.
````

**2. Observed failure in the initial output**

```text
The output states `∃ n : ℕ, ∀ x : ℝ, (n : ℝ) > x`, requiring one fixed witness,
while the prompt requires `∀ x : ℝ, ∃ n : ℕ, (n : ℝ) > x`, allowing the witness to
depend on `x`. The submitted proposition is in fact false.
```

**3. Golden**

```lean
def CandidateStatement : Prop := ∀ x : ℝ, ∃ n : ℕ, (n : ℝ) > x
```

Plain language: for each real x, chosen first, there is a natural number whose cast exceeds it. Equivalent standard representations — for example using `x < (n : ℝ)` — are acceptable. A counterexample distinguishing the mistranslation: the swapped form would require a single natural number above every real.

**4. Rubric**

```text
F1 (+1). The proposition quantifies over real numbers and natural numbers as requested.
F2 (+1). The existential witness lies within the scope of the universal binder, so it may
        depend on the universally quantified real.
F4 (+1). The conclusion is a strict inequality with the natural number's cast on the
        greater side.
```

F3 and F5 are omitted because the prompt states no hypotheses and no endpoint or indexing convention. The initial output is **UNMET** on F2.

---

## 10. The offline Lean environment

The model receives terminal access and creates its project from the ground up. The environment supplies only the reusable offline Lean software stack.

### 10.1 The frozen toolchain and Mathlib4 commit

**Everything must compile against one frozen Lean toolchain and one frozen commit of `mathlib4`. There is no other supported version.**

| Item | Pinned value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.33.0-rc1` |
| Mathlib4 commit | `9944fe2973b8dc0b86949101ed98232c07cd54a0` |

Every prompt, golden answer, model output, and verification run must be produced and checked against this toolchain and commit. A proof that compiles on a newer or older Lean or Mathlib but not on these is not a valid golden, and a failure caused by a version mismatch is an environment failure — not a model failure.

### 10.2 What the environment provides

- ✅ The exact Lean compiler (`leanprover/lean4:v4.33.0-rc1`).
- ✅ The matching Lake executable.
- ✅ Mathlib4 at the frozen commit `9944fe2973b8dc0b86949101ed98232c07cd54a0`.
- ✅ Every dependency locked by Mathlib's `lake-manifest.json`.
- ✅ Mathlib and dependency source for local search.
- ✅ Matching precompiled build artifacts.
- ✅ A documented local path.
- ✅ No network access.

### 10.3 Environment failures invalidate tasks

If an output fails only because Lean, Mathlib, or an offline dependency is missing, that is an environment failure, not a model failure. Do not submit the task.

---

## 11. Site map

Navigation as shown in the site sidebar and the Home page "Start here" cards.

| Section | Page | Description (from the Home page) | In this file |
| --- | --- | --- | --- |
| — | Home | Lean Data Creation Playbook | §1–2 |
| — | Ground Rules | Non-negotiables for every Turing task | §3 |
| Tasking | Task Flow | The seven steps every Lean task moves through, in order. | §4 |
| Tasking | Writing Prompts | Everything a proof-writing or formalization prompt must state. | §5 |
| Tasking | Checking Model Output | What counts as a genuine failure — and what does not. | §6 |
| Tasking | Golden Answers | A correct answer, not the only acceptable answer. | §7 |
| Tasking | Writing Rubrics | Four principles, binary +1 checks, and the score targets. | §8 |
| Tasking | Worked Examples | One proof task and one formalization task, end to end. | §9 |
| Environment | Offline Lean Setup (card title: "Offline Lean Environment") | The pinned toolchain, Mathlib commit, and build artifacts. | §10 |
| Team & Admin | Project Leadership | — | Not captured |
| Team & Admin | Changelog | — | Not captured |

The sidebar also has an external **Handshake AI** link.

---

## 12. Pages not yet captured

The content of these two pages is **not** in this file:

- [ ] Project Leadership
- [ ] Changelog

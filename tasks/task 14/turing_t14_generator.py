#!/usr/bin/env python3
"""Project Turing, task 14 generator (proof writing): the average order of the divisor function
(Dirichlet's divisor problem, hyperbola method, Euler-Mascheroni constant).

Writes, next to this script:
  task14_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden (superseded by the worker)

Self-verifying numerics: d(n) by a sieve for n <= 10^6; theorem 1 (|D(N) - N log N - (2 gamma - 1) N|
<= 4 sqrt N) is checked for every N <= 10^6 with gamma to 40 digits (the largest ratio |error| / sqrt N
is printed; it stays well below 4, so the stated constant is safe but not sharp); theorem 2
(|sum d(n)/n - (log N)^2 / 2 - 2 gamma log N| <= 4) for every N <= 10^6 (the deviation tends to
gamma^2 - 2 gamma_1 = 0.4789 and is largest, 1, at N = 1); theorems 3, 4, 5 are
limits, so only finite-N sanity checks are possible (deviation from the limit at N = 10^3 .. 10^6 is at
most 8 / sqrt N); the hypothesis N >= 1 of theorems 1 and 2 only excludes the empty sum.
Run:  python turing_t14_generator.py
"""

TASK = 14
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "numeric (exact divisor counts, floating-point logarithms)"

PRELUDE = ""

THEOREMS = [
    ("sum_card_divisors_sub_le", "(N : Nat) (hN : 1 <= N)", """\
    abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real)) - (N : Real) * Real.log N -
        (2 * Real.eulerMascheroniConstant - 1) * N) <= 4 * Real.sqrt N"""),
    ("sum_card_divisors_div_sub_le", "(N : Nat) (hN : 1 <= N)", """\
    abs ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) / n) - Real.log N ^ 2 / 2 -
        2 * Real.eulerMascheroniConstant * Real.log N) <= 4"""),
    ("tendsto_sum_card_divisors", "", """\
    Filter.Tendsto (fun N : Nat => ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real)) -
        (N : Real) * Real.log N) / N) Filter.atTop
      (nhds (2 * Real.eulerMascheroniConstant - 1))"""),
    ("tendsto_sum_card_divisors_sub_log", "", """\
    Filter.Tendsto (fun N : Nat => (Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) -
        Real.log n) / N) Filter.atTop (nhds (2 * Real.eulerMascheroniConstant))"""),
    ("tendsto_sum_sum_card_divisors", "", """\
    Filter.Tendsto (fun N : Nat => ((Finset.Icc 1 N).sum (fun n =>
        (Finset.Icc 1 n).sum (fun m => (m.divisors.card : Real))) -
        (N : Real) ^ 2 * Real.log N / 2) / (N : Real) ^ 2) Filter.atTop
      (nhds (Real.eulerMascheroniConstant - 3 / 4))"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. $d(n)$ is the number of divisors of $n$ (`Nat.divisors n` has `d(n)` elements), $D(N) = \sum_{n \le N} d(n)$, $\log$ is the natural logarithm and $\gamma$ is the Euler-Mascheroni constant (`Real.eulerMascheroniConstant`, the limit of $1 + 1/2 + \dots + 1/n - \log n$). $N$ and $n$ denote natural numbers.

1. For every $N \ge 1$: $\left| D(N) - N \log N - (2\gamma - 1) N \right| \le 4 \sqrt{N}$.
2. For every $N \ge 1$: $\left| \sum_{n=1}^{N} \dfrac{d(n)}{n} - \tfrac{1}{2} (\log N)^2 - 2\gamma \log N \right| \le 4$.
3. $\dfrac{D(N) - N \log N}{N} \to 2\gamma - 1$ as $N \to \infty$.
4. $\dfrac{1}{N} \sum_{n=1}^{N} \left( d(n) - \log n \right) \to 2\gamma$ as $N \to \infty$.
5. $\dfrac{1}{N^2} \left( \sum_{n=1}^{N} D(n) - \tfrac{1}{2} N^2 \log N \right) \to \gamma - \tfrac{3}{4}$ as $N \to \infty$.

Lean statement. Sums run over `Finset.Icc 1 N`, `Real.log 0 = 0`, and `Real.sqrt`, `Real.log`, `Filter.Tendsto`, `Filter.atTop` and `nhds` are Mathlib's. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Numeric tests of the five statements. Returns the number of checks passed."""
    from math import log, sqrt, lgamma
    gamma = 0.5772156649015328606065120900824024310422
    N = 1_000_000
    cnt = [0] * (N + 1)
    for d in range(1, N + 1):
        for m in range(d, N + 1, d):
            cnt[m] += 1
    assert cnt[1] == 1 and cnt[12] == 6 and cnt[720720] == 240
    ok = 0
    D = 0
    worst = 0.0
    DD = 0                          # sum_(n <= N) D(n)
    Q = 0.0                         # sum_(n <= N) d(n) / n
    worst2 = 0.0
    checkpoints = {10 ** k for k in range(3, 7)}
    for n in range(1, N + 1):
        D += cnt[n]
        DD += D
        err = D - n * log(n) - (2 * gamma - 1) * n
        assert abs(err) <= 4 * sqrt(n), ("sum_card_divisors_sub_le", n, err)
        worst = max(worst, abs(err) / sqrt(n))
        Q += cnt[n] / n
        dev = Q - log(n) ** 2 / 2 - 2 * gamma * log(n)
        assert abs(dev) <= 4, ("sum_card_divisors_div_sub_le", n, dev)
        worst2 = max(worst2, abs(dev))
        ok += 2
        if n in checkpoints:
            t3 = (D - n * log(n)) / n - (2 * gamma - 1)
            t4 = (D - lgamma(n + 1)) / n - 2 * gamma
            t5 = (DD - n * n * log(n) / 2) / (n * n) - (gamma - 0.75)
            for name, dev in (("tendsto_sum_card_divisors", t3),
                              ("tendsto_sum_card_divisors_sub_log", t4),
                              ("tendsto_sum_sum_card_divisors", t5)):
                assert abs(dev) <= 8 / sqrt(n), (name, n, dev)
                ok += 1
    assert worst < 1.5 and worst2 <= 1.0   # the stated constants 4 have a comfortable margin
    print(f"  largest |D(N) - N log N - (2 gamma - 1) N| / sqrt N for N <= {N}: {worst:.4f}")
    print(f"  largest |sum d(n)/n - (log N)^2/2 - 2 gamma log N| for N <= {N}: {worst2:.4f}")
    return ok


# ---- shared generator code (inlined into each task generator) ----
import re
from pathlib import Path

TOOLCHAIN = "leanprover/lean4:v4.33.0-rc1"
MATHLIB_COMMIT = "9944fe2973b8dc0b86949101ed98232c07cd54a0"
LEAN_FILE = "TuringTask/Basic.lean"
NAMESPACE = "TuringTask"


def lean_source() -> str:
    parts = ["import Mathlib", "", f"namespace {NAMESPACE}", ""]
    if PRELUDE:
        parts += [PRELUDE.rstrip("\n"), ""]
    for name, binders, statement in THEOREMS:
        head = f"theorem {name} {binders}" if binders else f"theorem {name}"
        parts.append(f"{head} :\n{statement} := by\n  sorry")
        parts.append("")
    parts.append(f"end {NAMESPACE}")
    return "\n".join(parts) + "\n"


def _explicit_args(binders: str) -> list:
    """Names of the explicit binders `(x y : T)` at parenthesis depth 0 (instance binders
    `[...]` and parentheses inside binder types are skipped)."""
    names, depth, i = [], 0, 0
    while i < len(binders):
        ch = binders[i]
        if ch in "([{":
            if depth == 0 and ch == "(":
                j = binders.index(":", i)
                names += binders[i + 1:j].split()
            depth += 1
        elif ch in ")]}":
            depth -= 1
        i += 1
    return names


def check_source() -> str:
    """Lean file used later to check a submitted project: each `example` type-checks only if
    the submitted theorem has exactly the statement given in the prompt."""
    parts = ["import TuringTask.Basic", "", f"open {NAMESPACE}", ""]
    for name, binders, statement in THEOREMS:
        args = " ".join(_explicit_args(binders))
        head = f"example {binders}" if binders else "example"
        call = f"{NAMESPACE}.{name} {args}" if args else f"{NAMESPACE}.{name}"
        parts.append(f"{head} :\n{statement} :=\n  {call}\n")
    if DEF_CHECK:
        parts.append(DEF_CHECK)
    parts += [f"#print axioms {NAMESPACE}.{name}" for name, _, _ in THEOREMS]
    return "\n".join(parts) + "\n"


RULES = """Rules. Helper definitions and lemmas are allowed, in this file or in other project files that it imports, and so is any kernel-checkable proof strategy. Keep `import Mathlib`, the namespace `@NS@`, @KEEP@ unchanged. Do not use `sorry`, `admit`, `native_decide`, new axioms, or any other way around the kernel: for each of the @COUNT@ theorems `#print axioms` must report only `propext`, `Classical.choice` and `Quot.sound`. Environment: Lean toolchain `@TOOLCHAIN@`, Mathlib commit `@COMMIT@`. Verify with `lake build`; it must finish with no errors.
"""


def prompt_text() -> str:
    text = PROMPT_BODY + "\n```lean\n" + lean_source() + "```\n\n" + RULES
    return (text.replace("@FILE@", LEAN_FILE).replace("@NS@", NAMESPACE)
            .replace("@KEEP@", KEEP).replace("@COUNT@", COUNT_WORD)
            .replace("@TOOLCHAIN@", TOOLCHAIN).replace("@COMMIT@", MATHLIB_COMMIT))


CHECK_OUTPUTS_BAT = r"""@echo off
setlocal EnableExtensions EnableDelayedExpansion
title Project Turing task @N@ - check model outputs
set "HERE=%~dp0"
set "DEST=C:\lean\TuringTask"
set "PATH=%USERPROFILE%\.elan\bin;%PATH%"
if not exist "%DEST%\lakefile.toml" goto :noproject
for %%R in (r1 r2 r3 golden) do call :one %%R
echo.
echo All available outputs checked. Tell Claude it is done.
pause
exit /b 0

:noproject
echo %DEST% not found.
pause
exit /b 1

:one
set "R=%~1"
set "SRC=%HERE%model_outputs\%R%\answer"
set "LOG=%HERE%model_outputs\check_%R%_log.txt"
if not exist "%SRC%\TuringTask\Basic.lean" goto :skipmissing
if exist "%LOG%" goto :skipdone
echo [%R%] building. This takes about 10 to 15 minutes. Leave this window open.
echo Check of %R% started %DATE% %TIME% > "%LOG%.tmp"
if exist "%DEST%\TuringTask" rmdir /S /Q "%DEST%\TuringTask"
xcopy "%SRC%\TuringTask" "%DEST%\TuringTask\" /E /I /Y >nul
if exist "%SRC%\TuringTask.lean" copy /Y "%SRC%\TuringTask.lean" "%DEST%\TuringTask.lean" >nul
copy /Y "%HERE%StatementAndAxiomsCheck.lean" "%DEST%\StatementAndAxiomsCheck.lean" >nul
cd /d "%DEST%"
echo ===== lake build >> "%LOG%.tmp"
lake build >> "%LOG%.tmp" 2>&1
echo BUILD EXIT CODE !ERRORLEVEL! >> "%LOG%.tmp"
echo ===== statement and axioms check >> "%LOG%.tmp"
lake env lean StatementAndAxiomsCheck.lean >> "%LOG%.tmp" 2>&1
echo CHECK EXIT CODE !ERRORLEVEL! >> "%LOG%.tmp"
move /Y "%LOG%.tmp" "%LOG%" >nul
echo [%R%] done.
goto :eof
:skipmissing
echo [%R%] no output folder yet - skipped.
goto :eof
:skipdone
echo [%R%] already checked - skipped.
goto :eof
"""


def assert_ascii(label: str, text: str) -> None:
    bad = sorted({ch for ch in text if ord(ch) > 127 or (ord(ch) < 32 and ch not in "\n\r")})
    assert not bad, f"{label}: non-ASCII or control characters {bad!r}"


def main() -> None:
    here = Path(__file__).resolve().parent
    n_checks = self_check()
    files = {
        f"task{TASK}_prompt.txt": (prompt_text(), "\n"),
        LEAN_FILE: (lean_source(), "\n"),
        "StatementAndAxiomsCheck.lean": (check_source(), "\n"),
        "check_outputs.bat": (CHECK_OUTPUTS_BAT.replace("@N@", str(TASK)), "\r\n"),
    }
    for rel, (text, _) in files.items():
        assert_ascii(rel, text)
    assert "@" not in prompt_text().replace("@[", ""), "unreplaced placeholder in prompt"
    assert lean_source() in prompt_text()
    assert max(len(line) for line in lean_source().splitlines()) <= 100
    for rel, (text, eol) in files.items():
        path = here / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="ascii", newline=eol) as fh:
            fh.write(text)
    print(f"task {TASK}: {CHECK_KIND} checks passed: {n_checks}")
    for rel, (text, _) in files.items():
        print(f"  wrote {rel}: {len(text)} chars, ASCII ok")


if __name__ == "__main__":
    main()

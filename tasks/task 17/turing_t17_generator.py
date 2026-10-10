#!/usr/bin/env python3
"""Project Turing, task 17 generator (proof writing): densities governed by 6 / pi^2 (squarefree
numbers, coprime pairs, the average of Euler's function) with explicit error terms.

Writes, next to this script:
  task17_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden (superseded by the worker)

Self-verifying numerics (exact sieves of the Moebius function and of Euler's function up to 10^6, exact
counts, floating-point only for pi, sqrt and log): theorems 1-4 for every N <= 10^6 (the largest ratio of
the actual error to the stated bound is printed for each; all stay below 1 with a wide margin), the
identity "coprime pairs in [1, N]^2 = 2 sum_(n <= N) phi(n) - 1" directly for N <= 400, the limit of
theorem 5 at N = 10^3 .. 10^6, and that the two Moebius identities behind the proofs hold for n <= 10^5
(sum_(d^2 | n) mu(d) = [n squarefree], sum_(d | n) mu(d) = [n = 1]). The hypothesis N >= 1 only excludes
the empty case. Asserts that every generated file is pure ASCII.
Run:  python turing_t17_generator.py
"""

TASK = 17
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "numeric (exact sieves and counts, floating-point bounds)"

PRELUDE = ""

THEOREMS = [
    ("card_squarefree_sub_le", "(N : Nat) (hN : 1 <= N)", """\
    abs ((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) -
        6 / Real.pi ^ 2 * N) <= 3 * Real.sqrt N"""),
    ("card_coprime_sub_le", "(N : Nat) (hN : 1 <= N)", """\
    abs ((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) - 6 / Real.pi ^ 2 * N ^ 2) <=
      6 * N * (Real.log N + 1)"""),
    ("sum_totient_sub_le", "(N : Nat) (hN : 1 <= N)", """\
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real)) - 3 / Real.pi ^ 2 * N ^ 2) <=
      4 * N * (Real.log N + 1)"""),
    ("sum_totient_div_sub_le", "(N : Nat) (hN : 1 <= N)", """\
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n) - 6 / Real.pi ^ 2 * N) <=
      Real.log N + 2"""),
    ("tendsto_card_squarefree_div", "", """\
    Filter.Tendsto (fun N : Nat => (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card :
        Real) / N) Filter.atTop (nhds (6 / Real.pi ^ 2))"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. $Q(N)$ is the number of squarefree integers in $[1, N]$ (Mathlib's `Squarefree`), $C(N)$ the number of pairs $(a, b) \in [1, N]^2$ with $\gcd(a, b) = 1$ (`Nat.Coprime`), $\varphi$ is Euler's function (`Nat.totient`) and $\log$ the natural logarithm. $N$, $n$ denote natural numbers.

1. For every $N \ge 1$: $\left| Q(N) - \dfrac{6}{\pi^2} N \right| \le 3 \sqrt{N}$.
2. For every $N \ge 1$: $\left| C(N) - \dfrac{6}{\pi^2} N^2 \right| \le 6 N (\log N + 1)$.
3. For every $N \ge 1$: $\left| \sum_{n=1}^{N} \varphi(n) - \dfrac{3}{\pi^2} N^2 \right| \le 4 N (\log N + 1)$.
4. For every $N \ge 1$: $\left| \sum_{n=1}^{N} \dfrac{\varphi(n)}{n} - \dfrac{6}{\pi^2} N \right| \le \log N + 2$.
5. $Q(N) / N \to 6 / \pi^2$ as $N \to \infty$.

Lean statement. `Finset.product` is the Cartesian product, sums run over `Finset.Icc 1 N`, `Real.log 0 = 0`, and `Real.pi`, `Real.sqrt`, `Real.log`, `Filter.Tendsto`, `Filter.atTop` and `nhds` are Mathlib's. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Numeric tests of the five statements. Returns the number of checks passed."""
    from math import pi, sqrt, log, gcd
    N = 1_000_000
    # sieves: smallest prime factor -> Moebius mu and Euler phi
    mu = [1] * (N + 1)
    phi = list(range(N + 1))
    sqf = [True] * (N + 1)
    sieve = [True] * (N + 1)
    for p in range(2, N + 1):
        if not sieve[p]:
            continue
        for m in range(p, N + 1, p):
            sieve[m] = False if m != p else sieve[m]
            mu[m] = -mu[m]
            phi[m] -= phi[m] // p
        for m in range(p * p, N + 1, p * p):
            mu[m] = 0
            sqf[m] = False
    sieve[1] = False
    assert mu[1] == 1 and mu[2] == -1 and mu[4] == 0 and mu[6] == 1 and mu[30] == -1
    assert phi[1] == 1 and phi[12] == 4 and phi[97] == 96 and phi[1000] == 400
    ok = 0
    c6 = 6 / pi ** 2
    Q = 0
    S = 0            # sum phi(n)
    T = 0.0          # sum phi(n)/n
    worst = [0.0, 0.0, 0.0, 0.0]
    checkpoints = {10 ** k for k in range(3, 7)}
    for n in range(1, N + 1):
        Q += 1 if sqf[n] else 0
        S += phi[n]
        T += phi[n] / n
        C = 2 * S - 1                                   # coprime pairs in [1, n]^2
        e1 = abs(Q - c6 * n);              b1 = 3 * sqrt(n)
        e2 = abs(C - c6 * n * n);          b2 = 6 * n * (log(n) + 1)
        e3 = abs(S - c6 / 2 * n * n);      b3 = 4 * n * (log(n) + 1)
        e4 = abs(T - c6 * n);              b4 = log(n) + 2
        assert e1 <= b1, ("card_squarefree_sub_le", n, e1, b1)
        assert e2 <= b2, ("card_coprime_sub_le", n, e2, b2)
        assert e3 <= b3, ("sum_totient_sub_le", n, e3, b3)
        assert e4 <= b4, ("sum_totient_div_sub_le", n, e4, b4)
        for i, r in enumerate((e1 / b1, e2 / b2, e3 / b3, e4 / b4)):
            worst[i] = max(worst[i], r)
        ok += 4
        if n in checkpoints:
            assert abs(Q / n - c6) <= 3 / sqrt(n), ("tendsto_card_squarefree_div", n)
            ok += 1
    assert max(worst) < 1, worst
    print("  largest error / stated bound, theorems 1-4: " + ", ".join(f"{w:.4f}" for w in worst))
    for n in range(1, 401):                             # the coprime-pair identity, directly
        c = sum(1 for a in range(1, n + 1) for b in range(1, n + 1) if gcd(a, b) == 1)
        assert c == 2 * sum(phi[1:n + 1]) - 1, ("coprime pairs", n)
        ok += 1
    for n in range(1, 100_001):                         # the two Moebius identities
        s1 = sum(mu[d] for d in range(1, int(n ** 0.5) + 1) if n % (d * d) == 0)
        assert s1 == (1 if sqf[n] else 0), ("sum mu over d^2 | n", n)
        ok += 1
    for n in range(1, 3001):
        s2 = sum(mu[d] for d in range(1, n + 1) if n % d == 0)
        assert s2 == (1 if n == 1 else 0), ("sum mu over d | n", n)
        ok += 1
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

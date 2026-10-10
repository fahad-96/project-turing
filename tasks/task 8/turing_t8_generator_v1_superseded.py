#!/usr/bin/env python3
"""Project Turing, task 8 generator (proof writing): fractional parts of n x and n^2 x.

Writes, next to this script:
  task8_prompt.txt               the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden

Self-verifying, but the statements are limits, so the checks are finite-N sanity checks, not
proofs: proportions for x = sqrt 2, sqrt 3, pi, e, (1 + sqrt 5)/2 and many intervals at
N = 100000 (n x, double precision) and N = 20000 (n^2 x, 60-digit decimals), the largest error
over a grid of intervals (uniform version), the leading digit of 2^n by exact integers for
n < 6000 (checking also that the Lean expression 2 ^ n / 10 ^ Nat.log 10 (2 ^ n) is the leading
digit), and the mean of |sin n| for N = 10^6; checks that irrationality cannot be dropped;
asserts that every generated file is pure ASCII.
Run:  python turing_t8_generator.py
"""

TASK = 8
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "finite-N numerical (not exact)"

PRELUDE = ""

HYP = "(x a b : Real) (hx : Irrational x) (ha : 0 <= a) (hab : a <= b) (hb : b <= 1)"

THEOREMS = [
    ("freq_mul", HYP, """\
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      a <= Int.fract ((n : Real) * x) /\\ Int.fract ((n : Real) * x) < b)).card : Real) / N)
      Filter.atTop (nhds (b - a))"""),
    ("freq_sq", HYP, """\
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      a <= Int.fract ((n : Real) ^ 2 * x) /\\ Int.fract ((n : Real) ^ 2 * x) < b)).card : Real)
      / N) Filter.atTop (nhds (b - a))"""),
    ("freq_unif", "(x : Real) (hx : Irrational x) (e : Real) (he : 0 < e)", """\
    exists N0 : Nat, forall N : Nat, N0 <= N -> forall a b : Real, 0 <= a -> a <= b -> b <= 1 ->
      abs ((((Finset.range N).filter (fun n : Nat =>
        a <= Int.fract ((n : Real) * x) /\\ Int.fract ((n : Real) * x) < b)).card : Real) / N
        - (b - a)) < e"""),
    ("freq_lead", "(d : Nat) (hd : 1 <= d) (hd' : d <= 9)", """\
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      2 ^ n / 10 ^ Nat.log 10 (2 ^ n) = d)).card : Real) / N)
      Filter.atTop (nhds (Real.logb 10 (((d : Real) + 1) / d)))"""),
    ("mean_abs_sin", "", """\
    Filter.Tendsto
      (fun N : Nat => Finset.sum (Finset.range N) (fun n : Nat => abs (Real.sin n)) / N)
      Filter.atTop (nhds (2 / Real.pi))"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. For a real number $t$ let $\{t\} = t - \lfloor t \rfloor$ be its fractional part. Let $x$ be an irrational real number and $0 \le a \le b \le 1$. For $N \ge 1$ let $P_N$ be the proportion of $n \in \{0, 1, \dots, N - 1\}$ with $a \le \{nx\} < b$.

1. $P_N \to b - a$ as $N \to \infty$.
2. The same holds with $\{n^2 x\}$ in place of $\{nx\}$.
3. The convergence in 1 is uniform in $a$ and $b$: for every $\varepsilon > 0$ there is $N_0$ such that $|P_N - (b - a)| < \varepsilon$ for all $N \ge N_0$ and all $0 \le a \le b \le 1$.
4. For $d \in \{1, \dots, 9\}$, the proportion of $n \in \{0, \dots, N - 1\}$ for which the first decimal digit of $2^n$ is $d$ tends to $\log_{10}((d + 1)/d)$.
5. $\frac{1}{N} \sum_{n=0}^{N-1} |\sin n| \to 2/\pi$.

Lean statement. `Int.fract t` is $\{t\}$, the proportion is the number of such $n$ in `Finset.range N` divided by `N`, and `2 ^ n / 10 ^ Nat.log 10 (2 ^ n)` (division of natural numbers) is the first decimal digit of $2^n$. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Finite-N sanity checks of the five limits. Returns the number of checks passed."""
    import math
    import sys
    from decimal import Decimal, getcontext
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)

    def frac(t):
        return t - math.floor(t)

    ok = 0
    xs = [math.sqrt(2), math.sqrt(3), math.pi, math.e, (1 + math.sqrt(5)) / 2]
    intervals = [(0.0, 1.0), (0.0, 0.0), (0.1, 0.35), (0.5, 0.5), (0.9, 1.0), (0.0, 0.01),
                 (0.25, 0.75), (0.123, 0.987)]
    n_lin = 100000
    for x in xs:
        fr = [frac(n * x) for n in range(n_lin)]
        for a, b in intervals:
            prop = sum(1 for f in fr if a <= f < b) / n_lin
            assert abs(prop - (b - a)) < 2e-3, ("freq_mul", x, a, b, prop)
            ok += 1
        grid = 40                                  # uniform version on a grid, N = 20000
        fr2 = sorted(fr[:20000])
        import bisect
        worst = max(abs((bisect.bisect_left(fr2, j / grid) - bisect.bisect_left(fr2, i / grid))
                        / 20000 - (j - i) / grid)
                    for i in range(grid + 1) for j in range(i, grid + 1))
        assert worst < 5e-3, ("freq_unif", x, worst)
        ok += 1
    getcontext().prec = 60
    n_sq = 20000
    for xd in [Decimal(2).sqrt(), Decimal(3).sqrt(), (1 + Decimal(5).sqrt()) / 2]:
        fr = []
        for n in range(n_sq):
            t = xd * n * n
            fr.append(float(t - int(t)))
        for a, b in intervals:
            prop = sum(1 for f in fr if a <= f < b) / n_sq
            assert abs(prop - (b - a)) < 1.5e-2, ("freq_sq", xd, a, b, prop)
            ok += 1
    n_lead = 6000
    cnt = [0] * 10
    v = 1
    for n in range(n_lead):
        s = str(v)
        lean_digit = v // 10 ** (len(s) - 1)       # Nat.log 10 v = number of digits - 1
        assert lean_digit == int(s[0]) and 1 <= lean_digit <= 9
        cnt[lean_digit] += 1
        v *= 2
    for d in range(1, 10):
        assert abs(cnt[d] / n_lead - math.log10((d + 1) / d)) < 2e-3, ("freq_lead", d)
        ok += 1
    n_sin = 10 ** 6
    mean = math.fsum(abs(math.sin(n)) for n in range(n_sin)) / n_sin
    assert abs(mean - 2 / math.pi) < 1e-4, ("mean_abs_sin", mean)
    ok += 1
    # irrationality cannot be dropped: x = 1/2 and x = 0
    assert sum(1 for n in range(1000) if 0.1 <= frac(n / 2) < 0.4) == 0
    assert sum(1 for n in range(1000) if 0.5 <= frac(n * n / 3) < 0.6) == 0
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

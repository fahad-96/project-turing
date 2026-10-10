#!/usr/bin/env python3
"""Project Turing, task 8 generator, version 2 (proof writing): fractional parts of n^2 x and of
polynomial values; leading digits of 2^(n^2); means of |sin(n^2)| and cos(n^2 x).

Version 1 (8 Oct) had the linear case {n x} as theorem 1 and three consequences of it; only one
theorem needed the quadratic case. Version 2 (9 Oct) removes every statement that the linear case
alone settles: all five theorems need the quadratic case or the general polynomial case.

Writes, next to this script:
  task8_prompt.txt               the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden

Self-verifying, but the statements are limits, so the checks are finite-N sanity checks, not
proofs: proportions of {n^2 x} at N = 20000 (60-digit decimals) for x = sqrt 2, sqrt 3, golden
ratio, pi, e and many intervals, the largest error over a grid of intervals (uniform version),
polynomial values of degree 2 to 4 with irrational leading coefficient, the leading digit of
2^(n^2) (exact integers for n < 400, and 60-digit decimals for n < 20000 against the Lean
expression 2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2))), the mean of |sin(n^2)| for N = 10^6,
the mean of cos(n^2 x) for several x with x/pi irrational; checks that the hypotheses cannot be
dropped (rational x, rational leading coefficient, constant polynomial, x/pi rational);
asserts that every generated file is pure ASCII.
Run:  python turing_t8_generator.py
"""

TASK = 8
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "finite-N numerical (not exact)"

PRELUDE = ""

AB = "(a b : Real) (ha : 0 <= a) (hab : a <= b) (hb : b <= 1)"

THEOREMS = [
    ("freq_sq_unif", "(x : Real) (hx : Irrational x) (e : Real) (he : 0 < e)", """\
    exists N0 : Nat, forall N : Nat, N0 <= N -> forall a b : Real, 0 <= a -> a <= b -> b <= 1 ->
      abs ((((Finset.range N).filter (fun n : Nat =>
        a <= Int.fract ((n : Real) ^ 2 * x) /\\ Int.fract ((n : Real) ^ 2 * x) < b)).card : Real)
        / N - (b - a)) < e"""),
    ("freq_poly", "(P : Polynomial Real) (hP : Irrational P.leadingCoeff) (hdeg : 1 <= P.natDegree)\n    " + AB, """\
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      a <= Int.fract (Polynomial.eval (n : Real) P) /\\
        Int.fract (Polynomial.eval (n : Real) P) < b)).card : Real) / N)
      Filter.atTop (nhds (b - a))"""),
    ("freq_lead_sq", "(d : Nat) (hd : 1 <= d) (hd' : d <= 9)", """\
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2)) = d)).card : Real) / N)
      Filter.atTop (nhds (Real.logb 10 (((d : Real) + 1) / d)))"""),
    ("mean_abs_sin_sq", "", """\
    Filter.Tendsto (fun N : Nat =>
      Finset.sum (Finset.range N) (fun n : Nat => abs (Real.sin ((n : Real) ^ 2))) / N)
      Filter.atTop (nhds (2 / Real.pi))"""),
    ("mean_cos_sq", "(x : Real) (hx : Irrational (x / Real.pi))", """\
    Filter.Tendsto (fun N : Nat =>
      Finset.sum (Finset.range N) (fun n : Nat => Real.cos ((n : Real) ^ 2 * x)) / N)
      Filter.atTop (nhds 0)"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. For a real number $t$ let $\{t\} = t - \lfloor t \rfloor$ be its fractional part. For a real sequence $u_0, u_1, \dots$, an integer $N \ge 1$ and $0 \le a \le b \le 1$, let $P_N(u; a, b)$ be the proportion of $n \in \{0, 1, \dots, N - 1\}$ with $a \le \{u_n\} < b$.

1. Let $x$ be irrational. For every $\varepsilon > 0$ there is $N_0$ such that $|P_N(n^2 x; a, b) - (b - a)| < \varepsilon$ for all $N \ge N_0$ and all $0 \le a \le b \le 1$.
2. Let $f$ be a real polynomial of degree at least $1$ whose leading coefficient is irrational. Then $P_N(f(n); a, b) \to b - a$ as $N \to \infty$.
3. For $d \in \{1, \dots, 9\}$, the proportion of $n \in \{0, \dots, N - 1\}$ for which the first decimal digit of $2^{n^2}$ is $d$ tends to $\log_{10}((d + 1)/d)$.
4. $\frac{1}{N} \sum_{n=0}^{N-1} |\sin(n^2)| \to 2/\pi$.
5. If $x/\pi$ is irrational, then $\frac{1}{N} \sum_{n=0}^{N-1} \cos(n^2 x) \to 0$.

Lean statement. `Int.fract t` is $\{t\}$, the proportion is the number of such $n$ in `Finset.range N` divided by `N`, `Polynomial.eval (n : Real) P` is $f(n)$ for `P : Polynomial Real` (with `P.leadingCoeff` and `P.natDegree` its leading coefficient and degree), and `2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2))` (division of natural numbers) is the first decimal digit of $2^{n^2}$. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Finite-N sanity checks of the five limits. Returns the number of checks passed."""
    import bisect
    import math
    import sys
    from decimal import Decimal, getcontext
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    getcontext().prec = 60

    def dfrac(t: Decimal) -> float:
        return float(t - int(t))

    ok = 0
    intervals = [(0.0, 1.0), (0.0, 0.0), (0.1, 0.35), (0.5, 0.5), (0.9, 1.0), (0.0, 0.01),
                 (0.25, 0.75), (0.123, 0.987)]
    D = Decimal
    xs = {"sqrt2": D(2).sqrt(), "sqrt3": D(3).sqrt(), "phi": (1 + D(5).sqrt()) / 2,
          "pi": D("3.14159265358979323846264338327950288419716939937510582097494459"),
          "e": D("2.71828182845904523536028747135266249775724709369995957496696763")}
    n_sq = 20000
    # theorem 1: {n^2 x}, interval proportions and the worst error over a grid (uniform version)
    for name, xd in xs.items():
        fr = [dfrac(xd * n * n) for n in range(n_sq)]
        for a, b in intervals:
            prop = sum(1 for f in fr if a <= f < b) / n_sq
            assert abs(prop - (b - a)) < 1.5e-2, ("freq_sq", name, a, b, prop)
            ok += 1
        grid = 40
        srt = sorted(fr)
        worst = max(abs((bisect.bisect_left(srt, j / grid) - bisect.bisect_left(srt, i / grid))
                        / n_sq - (j - i) / grid)
                    for i in range(grid + 1) for j in range(i, grid + 1))
        assert worst < 2e-2, ("freq_sq_unif", name, worst)
        ok += 1
    # theorem 2: polynomials with irrational leading coefficient (degrees 2, 3, 4)
    polys = {
        "sqrt2 n^2 + n/2 + 1/3": [D(1) / 3, D(1) / 2, D(2).sqrt()],
        "pi n^2 + e n": [D(0), xs["e"], xs["pi"]],
        "sqrt3 n^3 - 7 n^2 + n/5": [D(0), D(1) / 5, D(-7), D(3).sqrt()],
        "phi n^4 + n^3 + 1": [D(1), D(0), D(0), D(1), xs["phi"]],
        "e n^3 + sqrt2 n^2": [D(0), D(0), D(2).sqrt(), xs["e"]],
    }
    for name, coeffs in polys.items():
        fr = []
        for n in range(n_sq):
            v = D(0)
            for c in reversed(coeffs):
                v = v * n + c
            fr.append(dfrac(v))
        for a, b in intervals:
            prop = sum(1 for f in fr if a <= f < b) / n_sq
            assert abs(prop - (b - a)) < 2e-2, ("freq_poly", name, a, b, prop)
            ok += 1
    # theorem 3: leading digit of 2^(n^2); exact for n < 400 (also checks the Lean expression),
    # 60-digit decimals of n^2 log10 2 for n < 20000
    log10_2 = D(2).log10()
    n_exact = 400
    for n in range(n_exact):
        v = 2 ** (n * n)
        s = str(v)
        lean_digit = v // 10 ** (len(s) - 1)       # Nat.log 10 v = number of digits - 1
        assert lean_digit == int(s[0]) and 1 <= lean_digit <= 9
        f = dfrac(log10_2 * n * n)
        dec_digit = max(d for d in range(1, 10) if math.log10(d) <= f + 1e-15)
        assert dec_digit == lean_digit, ("freq_lead_sq exact vs decimal", n, lean_digit, dec_digit)
    ok += 1
    cnt = [0] * 10
    for n in range(n_sq):
        f = dfrac(log10_2 * n * n)
        cnt[max(d for d in range(1, 10) if math.log10(d) <= f + 1e-15)] += 1
    for d in range(1, 10):
        assert abs(cnt[d] / n_sq - math.log10((d + 1) / d)) < 1.5e-2, ("freq_lead_sq", d, cnt[d])
        ok += 1
    # theorem 4: mean of |sin(n^2)|, N = 10^6 (n^2 < 2^53 is exact in double precision)
    n_sin = 10 ** 6
    mean = math.fsum(abs(math.sin(float(n * n))) for n in range(n_sin)) / n_sin
    assert abs(mean - 2 / math.pi) < 5e-3, ("mean_abs_sin_sq", mean)
    ok += 1
    # theorem 5: mean of cos(n^2 x) for x = 1, sqrt 2, e, 1/3 (x/pi irrational in each case)
    n_cos = 10 ** 6
    for name, x in [("1", 1.0), ("sqrt2", math.sqrt(2)), ("e", math.e), ("1/3", 1 / 3)]:
        m = math.fsum(math.cos(float(n * n) * x) for n in range(n_cos)) / n_cos
        assert abs(m) < 1e-2, ("mean_cos_sq", name, m)
        ok += 1
    # hypotheses cannot be dropped
    assert sum(1 for n in range(1000) if 0.6 <= (n * n / 2) % 1 < 0.9) == 0        # x = 1/2
    assert sum(1 for n in range(1000) if 0.2 <= (n * n / 3) % 1 < 0.3) == 0        # x = 1/3
    assert all((n * n * 0.5 + n * math.sqrt(2) * 0) % 1 in (0.0, 0.5) for n in range(50))
    assert sum(1 for n in range(1000) if 0.1 <= (math.sqrt(2)) % 1 < 0.4) == 0     # constant poly
    assert abs(sum(math.cos(n * n * 0.0) for n in range(1000)) / 1000 - 1) < 1e-12  # x = 0
    assert abs(sum(math.cos(n * n * math.pi / 2) for n in range(1000)) / 1000 - 0.5) < 1e-9
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

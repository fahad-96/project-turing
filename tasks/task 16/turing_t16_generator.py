#!/usr/bin/env python3
"""Project Turing, task 16 generator (proof writing): Fibonacci and Lucas numbers that are squares,
twice squares, or powers of two (Cohn 1964).

Writes, next to this script:
  task16_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden (superseded by the worker)

Self-verifying with exact integer arithmetic: all five statements for every n <= 5000 (F_n has more
than 1000 digits; perfect squares by math.isqrt), that every listed index really is a solution, that the
hypothesis n >= 1 of the Lucas statements cannot be dropped in the `Nat.fib (n - 1) + Nat.fib (n + 1)`
encoding (at n = 0 it evaluates to 1 = 1^2 because of truncated subtraction), and the four congruence
facts of the classical proof for all 1 <= m, k <= 300: F_(m + 2k) = -(-1)^k F_m and
L_(m + 2k) = -(-1)^k L_m (mod L_k); L_k = 3 (mod 4) for even k with 3 not dividing k; L_k = 7 (mod 8)
for 4 | k with 3 not dividing k. Asserts that every generated file is pure ASCII.
Run:  python turing_t16_generator.py
"""

TASK = 16
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact integer"

PRELUDE = ""

THEOREMS = [
    ("fib_eq_sq", "(n x : Nat) (h : Nat.fib n = x ^ 2)", """\
    n = 0 \\/ n = 1 \\/ n = 2 \\/ n = 12"""),
    ("lucas_eq_sq", "(n x : Nat) (hn : 1 <= n) (h : Nat.fib (n - 1) + Nat.fib (n + 1) = x ^ 2)", """\
    n = 1 \\/ n = 3"""),
    ("fib_eq_two_mul_sq", "(n x : Nat) (h : Nat.fib n = 2 * x ^ 2)", """\
    n = 0 \\/ n = 3 \\/ n = 6"""),
    ("lucas_eq_two_mul_sq",
     "(n x : Nat) (hn : 1 <= n)\n    (h : Nat.fib (n - 1) + Nat.fib (n + 1) = 2 * x ^ 2)", """\
    n = 6"""),
    ("fib_eq_two_pow", "(n k : Nat) (h : Nat.fib n = 2 ^ k)", """\
    n = 1 \\/ n = 2 \\/ n = 3 \\/ n = 6"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. $F_n$ are the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$; `Nat.fib n` in Mathlib) and $L_n = F_{n-1} + F_{n+1}$ for $n \ge 1$ are the Lucas numbers ($L_1 = 1$, $L_2 = 3$, $L_3 = 4$, $L_4 = 7$, ...). All letters denote natural numbers.

1. If $F_n$ is a perfect square, then $n \in \{0, 1, 2, 12\}$.
2. If $n \ge 1$ and $L_n$ is a perfect square, then $n \in \{1, 3\}$.
3. If $F_n$ is twice a perfect square, then $n \in \{0, 3, 6\}$.
4. If $n \ge 1$ and $L_n$ is twice a perfect square, then $n = 6$.
5. If $F_n$ is a power of $2$, then $n \in \{1, 2, 3, 6\}$.

Lean statement. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Exact tests of the five statements and of the congruences behind them."""
    from math import isqrt
    N = 5000
    F = [0, 1]
    while len(F) < N + 3:
        F.append(F[-1] + F[-2])
    L = [2] + [F[n - 1] + F[n + 1] for n in range(1, N + 2)]
    assert L[1:6] == [1, 3, 4, 7, 11] and F[12] == 144

    def is_sq(v):
        return v >= 0 and isqrt(v) ** 2 == v

    def is_two_sq(v):
        return v % 2 == 0 and is_sq(v // 2)

    def is_pow2(v):
        return v > 0 and v & (v - 1) == 0

    ok = 0
    for n in range(0, N + 1):
        assert is_sq(F[n]) == (n in (0, 1, 2, 12)), ("fib_eq_sq", n)
        assert is_two_sq(F[n]) == (n in (0, 3, 6)), ("fib_eq_two_mul_sq", n)
        assert is_pow2(F[n]) == (n in (1, 2, 3, 6)), ("fib_eq_two_pow", n)
        ok += 3
        if n >= 1:
            assert is_sq(L[n]) == (n in (1, 3)), ("lucas_eq_sq", n)
            assert is_two_sq(L[n]) == (n == 6), ("lucas_eq_two_mul_sq", n)
            ok += 2
    # the Nat encoding at n = 0: fib (0 - 1) + fib 1 = fib 0 + fib 1 = 1, a square: n >= 1 is needed
    assert F[0] + F[1] == 1 and is_sq(1) and not is_two_sq(1)
    ok += 1
    # congruences used by the classical proof
    for k in range(1, 301):
        for m in range(1, 301):
            s = -(-1) ** k
            assert (F[m + 2 * k] - s * F[m]) % L[k] == 0, ("F shift", m, k)
            assert (L[m + 2 * k] - s * L[m]) % L[k] == 0, ("L shift", m, k)
            ok += 2
        if k % 2 == 0 and k % 3 != 0:
            assert L[k] % 4 == 3, ("L mod 4", k)
            ok += 1
        if k % 4 == 0 and k % 3 != 0:
            assert L[k] % 8 == 7, ("L mod 8", k)
            ok += 1
        assert (L[k] % 2 == 0) == (k % 3 == 0), ("L parity", k)
        g = __import__("math").gcd(F[k], L[k])
        assert g == (2 if k % 3 == 0 else 1), ("gcd F L", k)
        ok += 2
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

#!/usr/bin/env python3
"""Project Turing, task 4 generator (proof writing): congruences for coloured partitions.

Writes, next to this script:
  task4_prompt.txt               the prompt to paste into the platform
  TuringTask/Basic.lean          the two definitions and five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden

Self-verifying: tests all five statements numerically with exact integer arithmetic, for all
primes below 30 and many values of the other parameters, using natural-number subtraction
exactly as in the Lean statements, checks that the side conditions cannot be dropped, and
asserts that every generated file is pure ASCII.
Run:  python turing_t4_generator.py
"""

TASK = 4
COUNT_WORD = "five"
KEEP = ("the definitions `colored` and `eulerPow`, and the names and statements of the "
        "five theorems")

PRELUDE = """\
noncomputable def colored (k m : Nat) : Nat :=
  Finset.sum (Finset.Nat.antidiagonalTuple k m) (fun f : Fin k -> Nat =>
    Finset.prod Finset.univ (fun i : Fin k => Fintype.card (Nat.Partition (f i))))

noncomputable def eulerPow (e m : Nat) : Int :=
  Polynomial.coeff (Finset.prod (Finset.range m) (fun i : Nat =>
    ((1 : Polynomial Int) - Polynomial.X ^ (i + 1)) ^ e)) m
"""

THEOREMS = [
    ("colored_sub_three_dvd",
     "(p a m : Nat) (hp : Nat.Prime p) (h : Dvd.dvd p (8 * m + 1))", """\
    Dvd.dvd p (colored (a * p - 3) m)"""),
    ("colored_sub_three_pow_dvd",
     "(p k a m : Nat) (hp : Nat.Prime p)\n"
     "    (h : forall x : Nat, Not (x ^ 2 % p = (8 * m + 1) % p))", """\
    Dvd.dvd (p ^ k) (colored (a * p ^ k - 3) m)"""),
    ("colored_sub_four_dvd",
     "(p a m : Nat) (hp : Nat.Prime p) (h3 : p % 3 = 2)\n"
     "    (h : Dvd.dvd p (6 * m + 1))", """\
    Dvd.dvd p (colored (a * p - 4) m)"""),
    ("colored_sub_six_sq_dvd",
     "(p a m : Nat) (hp : Nat.Prime p) (h4 : p % 4 = 3)\n"
     "    (h : Dvd.dvd p (4 * m + 1))", """\
    Dvd.dvd (p ^ 2) (colored (a * p ^ 2 - 6) m)"""),
    ("eulerPow_odd_iff",
     "(s m : Nat)", """\
    Odd (eulerPow (3 * 2 ^ s) m) <-> exists j : Nat, m = 2 ^ s * (j * (j + 1) / 2)"""),
]

# Type-checks only if the submitted definitions are definitionally the ones given in the
# prompt (a submission must not redefine them).
DEF_CHECK = """\
example (k m : Nat) : TuringTask.colored k m =
    Finset.sum (Finset.Nat.antidiagonalTuple k m) (fun f : Fin k -> Nat =>
      Finset.prod Finset.univ (fun i : Fin k => Fintype.card (Nat.Partition (f i)))) := rfl

example (e m : Nat) : TuringTask.eulerPow e m =
    Polynomial.coeff (Finset.prod (Finset.range m) (fun i : Nat =>
      ((1 : Polynomial Int) - Polynomial.X ^ (i + 1)) ^ e)) m := rfl
"""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. A partition of $n$ is a multiset of positive integers with sum $n$. For integers $k \ge 0$ and $m \ge 0$, let $c_k(m)$ be the number of $k$-tuples $(\lambda_1, \dots, \lambda_k)$ of partitions whose sizes add up to $m$ (the $k$-coloured partitions of $m$). In particular $c_0(0) = 1$, $c_0(m) = 0$ for $m \ge 1$, and $c_1(m)$ is the number of partitions of $m$. For integers $e \ge 0$ and $m \ge 0$, let $\varepsilon_e(m)$ be the coefficient of $x^m$ in $\prod_{i \ge 1} (1 - x^i)^e$. Let $p$ be a prime and let $a, k, s, m \ge 0$ be integers. An index such as $ap - 3$ is read as $0$ when it is negative.

1. If $p$ divides $8m + 1$, then $p$ divides $c_{ap-3}(m)$.
2. If no integer $x$ satisfies $x^2 \equiv 8m + 1 \pmod p$, then $p^k$ divides $c_{ap^k-3}(m)$.
3. If $p \equiv 2 \pmod 3$ and $p$ divides $6m + 1$, then $p$ divides $c_{ap-4}(m)$.
4. If $p \equiv 3 \pmod 4$ and $p$ divides $4m + 1$, then $p^2$ divides $c_{ap^2-6}(m)$.
5. The integer $\varepsilon_{3 \cdot 2^s}(m)$ is odd if and only if $m = 2^s \cdot j(j+1)/2$ for some integer $j \ge 0$.

Lean statement. `Nat.Partition n` is Mathlib's type of partitions of `n`, and `Finset.Nat.antidiagonalTuple k m` is the finite set of all functions `f : Fin k -> Nat` whose values add up to `m`, so `colored k m` is $c_k(m)$. In `eulerPow e m` the product runs over $1 \le i \le m$ only; the factors with $i > m$ do not change the coefficient of $x^m$, so `eulerPow e m` is $\varepsilon_e(m)$. `Dvd.dvd x y` means that `x` divides `y`. All subtractions are natural-number subtractions, and `j * (j + 1) / 2` is natural-number division. The file `@FILE@` must contain the following two definitions and five theorems with exactly these names and statements, with each `sorry` replaced by a complete proof:
"""


def _mul(a, b, n):
    """Product of two integer power series, truncated to the first n coefficients."""
    r = [0] * n
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if i + j >= n:
                    break
                if y:
                    r[i + j] += x * y
    return r


def _nat_sub(a, b):
    """Natural-number (truncated) subtraction, as in Lean."""
    return a - b if a >= b else 0


def self_check() -> int:
    """Exact numeric tests of the five statements. Returns the number of checks passed."""
    M, KMAX = 90, 60
    part = [1] + [0] * M                       # partition numbers
    for k in range(1, M + 1):
        for n in range(k, M + 1):
            part[n] += part[n - k]
    assert part[:8] == [1, 1, 2, 3, 5, 7, 11, 15] and part[50] == 204226
    col = [[1] + [0] * M]                      # col[k][m] = c_k(m)
    for k in range(1, KMAX + 1):
        col.append(_mul(col[-1], part, M + 1))
    assert col[1] == part
    assert col[2][:6] == [1, 2, 5, 10, 20, 36] and col[3][:6] == [1, 3, 9, 22, 51, 108]
    primes = [q for q in range(2, 30) if all(q % d for d in range(2, q))]
    ok = 0
    for q in primes:
        squares = {(x * x) % q for x in range(q)}
        for a in range(0, 6):
            # theorem 1
            k = _nat_sub(a * q, 3)
            if k <= KMAX:
                for m in range(M + 1):
                    if (8 * m + 1) % q == 0:
                        assert col[k][m] % q == 0, ("colored_sub_three_dvd", q, a, m)
                        ok += 1
            # theorem 2
            for e in range(0, 5):
                k = _nat_sub(a * q ** e, 3)
                if k <= KMAX:
                    for m in range(M + 1):
                        if (8 * m + 1) % q not in squares:
                            assert col[k][m] % q ** e == 0, ("colored_sub_three_pow_dvd", q, e, a, m)
                            ok += 1
            # theorem 3
            k = _nat_sub(a * q, 4)
            if q % 3 == 2 and k <= KMAX:
                for m in range(M + 1):
                    if (6 * m + 1) % q == 0:
                        assert col[k][m] % q == 0, ("colored_sub_four_dvd", q, a, m)
                        ok += 1
            # theorem 4
            k = _nat_sub(a * q * q, 6)
            if q % 4 == 3 and k <= KMAX:
                for m in range(M + 1):
                    if (4 * m + 1) % q == 0:
                        assert col[k][m] % (q * q) == 0, ("colored_sub_six_sq_dvd", q, a, m)
                        ok += 1
    # the side conditions cannot be dropped
    assert any(col[2][m] % 5 for m in range(M + 1) if (8 * m + 1) % 5 in (1, 4))
    assert any(col[22][m] % 25 for m in range(M + 1) if (8 * m + 1) % 5 == 0)
    assert any(col[3][m] % 7 for m in range(M + 1) if (6 * m + 1) % 7 == 0)
    assert any(col[19][m] % 25 for m in range(M + 1) if (4 * m + 1) % 5 == 0)
    # theorem 5
    MD = 300
    cur = [1] + [0] * MD                       # prod (1 - x^i), then cubed, then squared s times
    for i in range(1, MD + 1):
        for n in range(MD, i - 1, -1):
            cur[n] -= cur[n - i]
    cur = _mul(_mul(cur, cur, MD + 1), cur, MD + 1)
    assert cur[:7] == [1, -3, 0, 5, 0, 0, -7]
    for s in range(0, 6):
        good = set()
        j = 0
        while 2 ** s * (j * (j + 1) // 2) <= MD:
            good.add(2 ** s * (j * (j + 1) // 2))
            j += 1
        for m in range(MD + 1):
            assert (cur[m] % 2 == 1) == (m in good), ("eulerPow_odd_iff", s, m)
            ok += 1
        cur = _mul(cur, cur, MD + 1)
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
        parts.append(f"theorem {name} {binders} :\n{statement} := by\n  sorry")
        parts.append("")
    parts.append(f"end {NAMESPACE}")
    return "\n".join(parts) + "\n"


def check_source() -> str:
    """Lean file used later to check a submitted project: each `example` type-checks only if
    the submitted theorem has exactly the statement given in the prompt."""
    parts = ["import TuringTask.Basic", "", f"open {NAMESPACE}", ""]
    for name, binders, statement in THEOREMS:
        args = " ".join(" ".join(m.split()) for m in re.findall(r"\(([^():]+?)\s*:", binders))
        parts.append(f"example {binders} :\n{statement} :=\n  {NAMESPACE}.{name} {args}\n")
    if DEF_CHECK:
        parts.append(DEF_CHECK)
    parts += [f"#print axioms {NAMESPACE}.{name}" for name, _, _ in THEOREMS]
    return "\n".join(parts) + "\n"


RULES = """Rules.
- You may add helper definitions and lemmas, in this file or in other files of the project that it imports, and you may use any kernel-checkable proof strategy.
- Keep the line `import Mathlib`, the namespace `@NS@`, @KEEP@ unchanged.
- Do not use `sorry`, `admit`, `native_decide`, new axioms, or any other way of bypassing the kernel. For each of the @COUNT@ theorems, `#print axioms` must report no axioms other than `propext`, `Classical.choice` and `Quot.sound`.
- Environment: Lean toolchain `@TOOLCHAIN@` and Mathlib at commit `@COMMIT@`.
- Verify your project with `lake build`. The build must finish with no errors.
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
    print(f"task {TASK}: numeric identity checks passed: {n_checks}")
    for rel, (text, _) in files.items():
        print(f"  wrote {rel}: {len(text)} chars, ASCII ok")


if __name__ == "__main__":
    main()

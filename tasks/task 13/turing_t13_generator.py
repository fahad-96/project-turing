#!/usr/bin/env python3
"""Project Turing, task 13 generator (proof writing): resultants and discriminants of cyclotomic polynomials.

Writes, next to this script:
  task13_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden (superseded by the worker)

Self-verifying with exact integer arithmetic that mirrors the Mathlib definitions at the pinned commit:
`Polynomial.sylvester f g m n` (first m columns hold shifted coefficients of g, the next n columns
those of f), `resultant f g = det (sylvester f g f.natDegree g.natDegree)`, and
`discr f = det (sylvesterDeriv f) * (-1) ^ (d * (d - 1) / 2)` with `sylvesterDeriv` = sylvester of
(f', f) with row 2d - 2 replaced. Cyclotomic polynomials by exact division of X^n - 1. Tests: theorems
1 and 2 for all 1 <= n < m <= 36, theorem 3 for 1 <= n <= 40, theorem 5 for 3 <= n <= 25, m < 40,
and that the excluded cases (n, p, k) = (1, 2, 1) and n = 2 really fail; asserts pure ASCII.
Run:  python turing_t13_generator.py
"""

TASK = 13
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact integer"

PRELUDE = ""

THEOREMS = [
    ("resultant_cyclotomic_eq_one",
     "(m n : Nat) (hn : 1 <= n) (hnm : n < m)\n"
     "    (h : forall p k : Nat, p.Prime -> Not (m = n * p ^ k))",
     """\
    Polynomial.resultant (Polynomial.cyclotomic m Int) (Polynomial.cyclotomic n Int) = 1"""),
    ("resultant_cyclotomic_mul_prime_pow",
     "(n p k : Nat) (hn : 1 <= n) (hp : p.Prime)\n"
     "    (hk : 1 <= k) (h : Not (n = 1 /\\ p = 2 /\\ k = 1))",
     """\
    Polynomial.resultant (Polynomial.cyclotomic (n * p ^ k) Int) (Polynomial.cyclotomic n Int) =
      (p : Int) ^ n.totient"""),
    ("discr_cyclotomic", "(n : Nat) (hn : 1 <= n)", """\
    Polynomial.discr (Polynomial.cyclotomic n Int) *
        n.primeFactors.prod (fun p => (p : Int) ^ (n.totient / (p - 1))) =
      (-1) ^ (n.totient / 2) * (n : Int) ^ n.totient"""),
    ("isCoprime_cyclotomic_iff", "(m n : Nat) (hn : 1 <= n) (hnm : n < m)", """\
    IsCoprime (Polynomial.cyclotomic m Int) (Polynomial.cyclotomic n Int) <->
      forall p k : Nat, p.Prime -> Not (m = n * p ^ k)"""),
    ("resultant_cyclotomic_X_pow_sub_one",
     "(n m : Nat) (hn : 3 <= n) (hm : 1 <= m)\n"
     "    (h : Not (m % n = 0))", """\
    Polynomial.resultant (Polynomial.cyclotomic n Int) (Polynomial.X ^ m - 1) =
      Polynomial.eval 1 (Polynomial.cyclotomic (n / Nat.gcd n m) Int) ^
        (n.totient / (n / Nat.gcd n m).totient)"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. $\Phi_n \in \mathbb{Z}[X]$ is the $n$-th cyclotomic polynomial (`Polynomial.cyclotomic n Int`) and $\varphi$ is Euler's function. $\mathrm{Res}(f, g)$ is Mathlib's resultant `Polynomial.resultant f g` (the determinant of the Sylvester matrix of $f$ and $g$ for their degrees) and $\mathrm{disc}(f)$ is Mathlib's discriminant `Polynomial.discr f`. All letters denote natural numbers.

1. If $1 \le n < m$ and $m$ is not of the form $n p^k$ with $p$ prime, then $\mathrm{Res}(\Phi_m, \Phi_n) = 1$.
2. If $n \ge 1$, $p$ is prime, $k \ge 1$ and $(n, p, k) \ne (1, 2, 1)$, then $\mathrm{Res}(\Phi_{n p^k}, \Phi_n) = p^{\varphi(n)}$.
3. If $n \ge 1$, then $\mathrm{disc}(\Phi_n) \cdot \prod_{p \mid n} p^{\varphi(n)/(p-1)} = (-1)^{\varphi(n)/2} \, n^{\varphi(n)}$, where the product runs over the primes $p$ dividing $n$.
4. If $1 \le n < m$, then $\Phi_m$ and $\Phi_n$ are coprime in $\mathbb{Z}[X]$ (that is, $A \Phi_m + B \Phi_n = 1$ for some $A, B \in \mathbb{Z}[X]$) if and only if $m$ is not of the form $n p^k$ with $p$ prime.
5. If $n \ge 3$, $m \ge 1$ and $n \nmid m$, then $\mathrm{Res}(\Phi_n, X^m - 1) = \Phi_k(1)^{\varphi(n)/\varphi(k)}$ with $k = n / \gcd(n, m)$.

Lean statement. All divisions in the exponents are exact. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Exact tests of the five statements against the Mathlib definitions. Returns the count."""
    from functools import lru_cache
    from math import gcd

    def pdiv(a, b):                    # exact quotient a / b for monic b, coefficients low -> high
        a = list(a)
        q = [0] * (len(a) - len(b) + 1)
        for i in range(len(a) - len(b), -1, -1):
            c = a[i + len(b) - 1]
            q[i] = c
            for j, y in enumerate(b):
                a[i + j] -= c * y
        assert all(x == 0 for x in a[:len(b) - 1])
        return q

    @lru_cache(None)
    def cyc(n):
        p = [-1] + [0] * (n - 1) + [1]
        for d in range(1, n):
            if n % d == 0:
                p = pdiv(p, cyc(d))
        return tuple(p)

    def tot(n):
        return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)

    def coeff(p, i):
        return p[i] if 0 <= i < len(p) else 0

    def det(mat):                      # Bareiss, exact over the integers
        n = len(mat)
        if n == 0:
            return 1
        a = [row[:] for row in mat]
        prev, sign = 1, 1
        for k in range(n - 1):
            if a[k][k] == 0:
                for i in range(k + 1, n):
                    if a[i][k] != 0:
                        a[k], a[i] = a[i], a[k]
                        sign = -sign
                        break
                else:
                    return 0
            for i in range(k + 1, n):
                for j in range(k + 1, n):
                    a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) // prev
            prev = a[k][k]
        return sign * a[n - 1][n - 1]

    def sylvester(f, g, m, n):         # Polynomial.sylvester f g m n
        size = m + n
        mat = [[0] * size for _ in range(size)]
        for i in range(size):
            for j1 in range(m):
                if j1 <= i <= j1 + n:
                    mat[i][j1] = coeff(g, i - j1)
            for j1 in range(n):
                if j1 <= i <= j1 + m:
                    mat[i][m + j1] = coeff(f, i - j1)
        return mat

    def resultant(f, g):
        return det(sylvester(f, g, len(f) - 1, len(g) - 1))

    def discr(f):                      # Polynomial.discr via sylvesterDeriv
        d = len(f) - 1
        mat = sylvester([i * f[i] for i in range(1, d + 1)], f, d - 1, d)
        mat[2 * d - 2] = [1 if j == d - 2 else (d if j == 2 * d - 2 else 0)
                          for j in range(2 * d - 1)]
        return det(mat) * (-1) ** (d * (d - 1) // 2)

    def is_prime(n):
        return n > 1 and all(n % q for q in range(2, int(n ** 0.5) + 1))

    def prime_pow_base(t):             # p if t = p^k with k >= 1, else None
        for p in range(2, t + 1):
            if t % p == 0:
                while t % p == 0:
                    t //= p
                return p if t == 1 else None
        return None

    ok = 0
    for m in range(2, 37):
        for n in range(1, m):
            r = resultant(cyc(m), cyc(n))
            p = prime_pow_base(m // n) if m % n == 0 else None
            if p is None:
                assert r == 1, ("resultant_cyclotomic_eq_one", m, n, r)
            elif (m, n) == (2, 1):
                assert r == -2                   # the excluded case really is an exception
            else:
                assert r == p ** tot(n), ("resultant_cyclotomic_mul_prime_pow", m, n, r)
            ok += 1
    for n in range(1, 41):
        lhs = discr(cyc(n))
        for p in range(2, n + 1):
            if n % p == 0 and is_prime(p):
                lhs *= p ** (tot(n) // (p - 1))
        assert lhs == (-1) ** (tot(n) // 2) * n ** tot(n), ("discr_cyclotomic", n)
        ok += 1
    for n in range(2, 26):
        for m in range(1, 40):
            if m % n == 0:
                continue
            r = resultant(cyc(n), [-1] + [0] * (m - 1) + [1])
            k = n // gcd(n, m)
            rhs = sum(cyc(k)) ** (tot(n) // tot(k))
            if n == 2:
                assert r == -rhs                 # n >= 3 is needed
            else:
                assert r == rhs, ("resultant_cyclotomic_X_pow_sub_one", n, m, r, rhs)
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

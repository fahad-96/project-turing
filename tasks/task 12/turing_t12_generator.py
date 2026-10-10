#!/usr/bin/env python3
"""Project Turing, task 12 generator (proof writing): new prime factors of Fibonacci and Lucas numbers.

Writes, next to this script:
  task12_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden (superseded by the worker)

Self-verifying with exact integer arithmetic. A prime factor of X that divides none of Y_1, ..., Y_r
exists iff X stripped of every common factor with the Y_i is > 1, so theorems 1 and 2 are tested
exactly (including that the listed exceptions are exceptions) for all n <= 320; theorems 3, 4, 5 are
tested with complete factorizations (Miller-Rabin + Pollard rho, fixed seed) for n <= 130, theorem 3
also by the stripping lower bound for n <= 320 (it is attained at n = 12, so 4 cannot be lowered);
asserts that every generated file is pure ASCII.
Run:  python turing_t12_generator.py
"""

TASK = 12
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact integer"

PRELUDE = ""

THEOREMS = [
    ("exists_prime_fib",
     "(n : Nat) (hn : 3 <= n) (h6 : Not (n = 6)) (h12 : Not (n = 12))",
     """\
    exists q : Nat, q.Prime /\\ Nat.fib n % q = 0 /\\
      forall k : Nat, 1 <= k -> k < n -> Not (Nat.fib k % q = 0)"""),
    ("exists_prime_lucas",
     "(n : Nat) (hn : 2 <= n) (h6 : Not (n = 6))",
     """\
    exists q : Nat, q.Prime /\\ (Nat.fib (n - 1) + Nat.fib (n + 1)) % q = 0 /\\
      forall k : Nat, 1 <= k -> k < n -> Not ((Nat.fib (k - 1) + Nat.fib (k + 1)) % q = 0)"""),
    ("card_divisors_le", "(n : Nat) (hn : 1 <= n)", """\
    n.divisors.card <= (Nat.fib n).primeFactors.card + 4"""),
    ("primeFactors_fib_eq",
     "(m n : Nat) (hm : 3 <= m) (hmn : m < n)\n"
     "    (h : (Nat.fib m).primeFactors = (Nat.fib n).primeFactors)", """\
    m = 3 /\\ n = 6"""),
    ("exists_prime_fib_mod",
     "(n : Nat) (hn : 3 <= n) (h5 : Not (n = 5)) (h6 : Not (n = 6))\n"
     "    (h12 : Not (n = 12))", """\
    exists q : Nat, q.Prime /\\ Nat.fib n % q = 0 /\\ (q % n = 1 \\/ q % n = n - 1)"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. $F_n$ are the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$; `Nat.fib n` in Mathlib) and $L_n = F_{n-1} + F_{n+1}$ for $n \ge 1$ are the Lucas numbers. All letters denote natural numbers.

1. If $n \ge 3$ and $n \ne 6, 12$, there is a prime $q$ that divides $F_n$ but divides none of $F_1, \dots, F_{n-1}$.
2. If $n \ge 2$ and $n \ne 6$, there is a prime $q$ that divides $L_n$ but divides none of $L_1, \dots, L_{n-1}$.
3. If $n \ge 1$, then the number of divisors of $n$ is at most $4$ plus the number of distinct prime factors of $F_n$.
4. If $3 \le m < n$ and $F_m$ and $F_n$ have the same prime factors, then $m = 3$ and $n = 6$.
5. If $n \ge 3$ and $n \ne 5, 6, 12$, then $F_n$ has a prime factor $q$ with $q \equiv 1$ or $q \equiv -1 \pmod n$.

Lean statement. `x % q = 0` means that $q$ divides $x$, and `q % n = n - 1` means $q \equiv -1 \pmod n$. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Exact tests of the five statements. Returns the number of checks passed."""
    import random
    from math import gcd
    rng = random.Random(12)
    N, M = 320, 130
    F = [0, 1]
    while len(F) < N + 3:
        F.append(F[-1] + F[-2])
    L = [2] + [F[n - 1] + F[n + 1] for n in range(1, N + 2)]

    def strip(x, ys):                  # x with every prime factor shared with some y removed
        for y in ys:
            if y == 0:
                continue
            while True:
                d = gcd(x, y)
                if d == 1:
                    break
                x //= d
        return x

    def is_prime(n):
        if n < 2:
            return False
        small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
        for p in small:
            if n % p == 0:
                return n == p
        d, s = n - 1, 0
        while d % 2 == 0:
            d, s = d // 2, s + 1
        for a in small:
            x = pow(a, d, n)
            if x in (1, n - 1):
                continue
            for _ in range(s - 1):
                x = x * x % n
                if x == n - 1:
                    break
            else:
                return False
        return True

    def rho(n):
        if n % 2 == 0:
            return 2
        while True:
            c = rng.randrange(1, n)
            x = y = rng.randrange(2, n)
            d = 1
            while d == 1:
                x = (x * x + c) % n
                y = (y * y + c) % n
                y = (y * y + c) % n
                d = gcd(abs(x - y), n)
            if d != n:
                return d

    def factor(n, out):
        if n == 1:
            return
        if is_prime(n):
            out.add(n)
            return
        d = rho(n)
        factor(d, out)
        factor(n // d, out)

    def ndiv(n):
        return sum(1 for d in range(1, n + 1) if n % d == 0)

    ok = 0
    for n in range(1, N + 1):
        new_f = strip(F[n], F[1:n]) > 1
        assert new_f == (n >= 3 and n not in (6, 12)), ("exists_prime_fib", n)
        new_l = strip(L[n], L[1:n]) > 1
        assert new_l == (n >= 2 and n != 6), ("exists_prime_lucas", n)
        ok += 2
    fs = {}
    for n in range(1, M + 1):
        s = set()
        factor(F[n], s)
        fs[n] = s
        prod = 1
        for q in s:
            prod *= q
        assert strip(F[n], [prod]) == 1          # the factorization is complete
    tight = []
    for n in range(1, M + 1):
        assert ndiv(n) <= len(fs[n]) + 4, ("card_divisors_le", n)
        if ndiv(n) == len(fs[n]) + 4:
            tight.append(n)
        ok += 1
    assert 12 in tight, tight
    for n in range(M + 1, N + 1):
        lower = sum(1 for d in range(1, n + 1) if n % d == 0 and strip(F[d], F[1:d]) > 1)
        assert ndiv(n) <= lower + 4, ("card_divisors_le", n)
        ok += 1
    same = [(m, n) for n in range(4, M + 1) for m in range(3, n) if fs[m] == fs[n]]
    assert same == [(3, 6)], ("primeFactors_fib_eq", same)
    ok += sum(range(1, M - 2))
    for n in range(M + 1, N + 1):              # a new prime in F_n: no earlier F_m has its primes
        assert strip(F[n], F[1:n]) > 1
        ok += 1
    for n in range(3, M + 1):
        hit = any(q % n == 1 or q % n == n - 1 for q in fs[n])
        assert hit == (n not in (5, 6, 12)), ("exists_prime_fib_mod", n)
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

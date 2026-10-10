#!/usr/bin/env python3
"""Project Turing, task 10 generator (proof writing): new prime factors of a^n - b^n and a^n + b^n.

Writes, next to this script:
  task10_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden

Self-verifying with exact integer arithmetic and no factoring: a prime factor of X that divides
none of Y_1, ..., Y_r exists iff X stripped of every common factor with the Y_i is > 1, so
theorems 1 and 2 are tested exactly (including that the listed exceptions are exceptions) for all
coprime 1 <= b < a < 12 and 2 <= n <= 36; theorem 3 for 2 <= a < 25, 1 <= n <= 48 (counting the
divisors d of n whose a^d - 1 has such a new prime, a lower bound for the number of prime factors);
theorem 4 by searching all a < 600, n < 60 for prime powers q^m (m >= 2) of the form a^n - 1;
theorem 5 for a < 120, 1 <= m < n <= 24; asserts that every generated file is pure ASCII.
Run:  python turing_t10_generator.py
"""

TASK = 10
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact integer"

PRELUDE = ""

THEOREMS = [
    ("exists_prime_sub",
     "(a b n : Nat) (hba : b < a) (hb : 1 <= b) (hab : Nat.Coprime a b)\n"
     "    (hn : 2 <= n) (h2 : Not (n = 2 /\\ exists t : Nat, a + b = 2 ^ t))\n"
     "    (h6 : Not (a = 2 /\\ b = 1 /\\ n = 6))",
     """\
    exists q : Nat, q.Prime /\\ (a ^ n - b ^ n) % q = 0 /\\
      forall k : Nat, 1 <= k -> k < n -> Not ((a ^ k - b ^ k) % q = 0)"""),
    ("exists_prime_add",
     "(a b n : Nat) (hba : b < a) (hb : 1 <= b) (hab : Nat.Coprime a b)\n"
     "    (hn : 2 <= n) (h3 : Not (a = 2 /\\ b = 1 /\\ n = 3))",
     """\
    exists q : Nat, q.Prime /\\ (a ^ n + b ^ n) % q = 0 /\\
      forall k : Nat, 1 <= k -> k < n -> Not ((a ^ k + b ^ k) % q = 0)"""),
    ("card_divisors_le", "(a n : Nat) (ha : 2 <= a) (hn : 1 <= n)", """\
    n.divisors.card <= (a ^ n - 1).primeFactors.card + 2"""),
    ("eq_prime_pow",
     "(a n q m : Nat) (ha : 2 <= a) (hn : 2 <= n) (hq : q.Prime) (hm : 2 <= m)\n"
     "    (h : a ^ n - 1 = q ^ m)", """\
    a = 3 /\\ n = 2 /\\ q = 2 /\\ m = 3"""),
    ("primeFactors_eq",
     "(a m n : Nat) (ha : 2 <= a) (hm : 1 <= m) (hmn : m < n)\n"
     "    (h : (a ^ m - 1).primeFactors = (a ^ n - 1).primeFactors)", """\
    m = 1 /\\ n = 2 /\\ exists t : Nat, a + 1 = 2 ^ t"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. All letters denote natural numbers.

1. Let $a > b \ge 1$ be coprime and $n \ge 2$. Unless $n = 2$ and $a + b$ is a power of $2$, or $(a, b, n) = (2, 1, 6)$, there is a prime $q$ that divides $a^n - b^n$ but divides none of the numbers $a^k - b^k$ with $1 \le k < n$.
2. Let $a > b \ge 1$ be coprime, $n \ge 2$ and $(a, b, n) \ne (2, 1, 3)$. Then there is a prime $q$ that divides $a^n + b^n$ but divides none of the numbers $a^k + b^k$ with $1 \le k < n$.
3. If $a \ge 2$ and $n \ge 1$, then the number of divisors of $n$ is at most $2$ plus the number of distinct prime factors of $a^n - 1$.
4. If $a \ge 2$, $n \ge 2$, $m \ge 2$, $q$ is prime and $a^n - 1 = q^m$, then $(a, n, q, m) = (3, 2, 2, 3)$.
5. If $a \ge 2$, $1 \le m < n$ and $a^m - 1$ and $a^n - 1$ have the same prime factors, then $m = 1$, $n = 2$ and $a + 1$ is a power of $2$.

Lean statement. Subtraction is on natural numbers (all differences here are positive), and `x % q = 0` means that $q$ divides $x$. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Exact tests of the five statements. Returns the number of checks passed."""
    from math import gcd

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

    def is_prime(n):                   # deterministic Miller-Rabin for n < 3.3e24, plus extra bases
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

    def iroot(v, m):                   # integer m-th root: float start above the root, Newton
        import math
        r = int(math.exp(math.log(v) / m) * (1 + 1e-9)) + 2
        while r ** m <= v:
            r *= 2
        while True:
            s = ((m - 1) * r + v // r ** (m - 1)) // m
            if s >= r:
                return r
            r = s

    def pow2(x):
        return x > 0 and x & (x - 1) == 0

    ok = 0
    for a in range(2, 12):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            for n in range(2, 37):
                new_sub = strip(a ** n - b ** n, [a ** k - b ** k for k in range(1, n)]) > 1
                exc_sub = (n == 2 and pow2(a + b)) or (a, b, n) == (2, 1, 6)
                assert new_sub != exc_sub, ("exists_prime_sub", a, b, n)
                new_add = strip(a ** n + b ** n, [a ** k + b ** k for k in range(1, n)]) > 1
                assert new_add != ((a, b, n) == (2, 1, 3)), ("exists_prime_add", a, b, n)
                ok += 2
    for a in range(2, 25):
        for n in range(1, 49):
            divs = [d for d in range(1, n + 1) if n % d == 0]
            lower = sum(1 for d in divs
                        if strip(a ** d - 1, [a ** k - 1 for k in range(1, d)]) > 1)
            assert len(divs) <= lower + 2, ("card_divisors_le", a, n)
            ok += 1
    sols = set()
    for a in range(2, 600):
        for n in range(2, 60):
            v = a ** n - 1
            for m in range(2, v.bit_length() + 1):
                r = iroot(v, m)
                if r ** m == v and is_prime(r):
                    sols.add((a, n, r, m))
            ok += 1
    assert sols == {(3, 2, 2, 3)}, ("eq_prime_pow", sols)
    same = []
    for a in range(2, 120):
        for n in range(2, 25):
            for m in range(1, n):
                x, y = a ** m - 1, a ** n - 1
                if x > 1 and strip(x, [y]) == 1 and strip(y, [x]) == 1:
                    same.append((a, m, n))
                ok += 1
    assert same and all(m == 1 and n == 2 and pow2(a + 1) for a, m, n in same), ("primeFactors_eq",)
    assert (3, 1, 2) in same and (7, 1, 2) in same      # the conclusion's case does occur
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

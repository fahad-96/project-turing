#!/usr/bin/env python3
"""Project Turing, task 9 generator (proof writing): cubes modulo a prime p = 1 (mod 3).

Writes, next to this script:
  task9_prompt.txt               the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden

Self-verifying: tests theorems 1 to 4 with exact integer arithmetic for every prime
p = 1 (mod 3) below 700 (counts by brute force over Z/pZ, mirroring the Lean filters literally;
the representation 4p = L^2 + 27M^2 found by search, with every sign of M), and theorem 5 in
double precision for every nonzero a (tolerance 1e-6 p^(3/2)); checks that the hypotheses and the
sign condition on L cannot be dropped; asserts that every generated file is pure ASCII.
Run:  python turing_t9_generator.py
"""

TASK = 9
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact integer (theorems 1-4) and double precision (theorem 5)"

PRELUDE = ""

HYP = ("(p : Nat) [Fact p.Prime] (hp : p % 3 = 1) (L M : Int)\n"
       "    (hLM : 4 * (p : Int) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1)")

THEOREMS = [
    ("card_cubic", HYP, """\
    ((Finset.univ.filter (fun q : Prod (ZMod p) (ZMod p) => q.1 ^ 3 + q.2 ^ 3 = 1)).card : Int) =
      (p : Int) - 2 + L"""),
    ("card_cube_pairs", HYP, """\
    9 * ((Finset.univ.filter (fun x : ZMod p => Not (x = 0) /\\ Not (x + 1 = 0) /\\
      (exists u : ZMod p, u ^ 3 = x) /\\ (exists v : ZMod p, v ^ 3 = x + 1))).card : Int) =
      (p : Int) - 8 + L"""),
    ("card_noncube_pairs", HYP, """\
    9 * ((Finset.univ.filter (fun x : ZMod p => Not (exists u : ZMod p, u ^ 3 = x) /\\
      Not (exists v : ZMod p, v ^ 3 = x + 1) /\\
      (exists w : ZMod p, w ^ 3 = x * (x + 1)))).card : Int) =
      2 * ((p : Int) + 1 + L)"""),
    ("two_cube_iff", "(p : Nat) [Fact p.Prime] (hp : p % 3 = 1)", """\
    (exists z : ZMod p, z ^ 3 = 2) <-> exists x y : Int, (p : Int) = x ^ 2 + 27 * y ^ 2"""),
    ("cubic_sum", HYP + "\n    (a : ZMod p) (ha : Not (a = 0)) (G : Complex)\n"
     "    (hG : G = Finset.sum Finset.univ (fun x : ZMod p =>\n"
     "      Complex.exp (2 * Real.pi * Complex.I * ((a * x ^ 3).val : Complex) / (p : Complex))))",
     """\
    G ^ 3 = 3 * (p : Complex) * G + (p : Complex) * (L : Complex)"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. Let $p$ be a prime with $p \equiv 1 \pmod 3$, and let $L, M$ be integers with $4p = L^2 + 27M^2$ and $L \equiv 1 \pmod 3$. An element $c$ of $\mathbb{Z}/p\mathbb{Z}$ is a cube if $c = u^3$ for some $u \in \mathbb{Z}/p\mathbb{Z}$.

1. The number of pairs $(x, y) \in (\mathbb{Z}/p\mathbb{Z})^2$ with $x^3 + y^3 = 1$ is $p - 2 + L$.
2. The number of $x \in \mathbb{Z}/p\mathbb{Z}$ with $x \ne 0$ and $x + 1 \ne 0$ such that $x$ and $x + 1$ are both cubes is $(p - 8 + L)/9$.
3. The number of $x \in \mathbb{Z}/p\mathbb{Z}$ such that neither $x$ nor $x + 1$ is a cube but $x(x + 1)$ is a cube is $2(p + 1 + L)/9$.
4. $2$ is a cube modulo $p$ if and only if $p = x^2 + 27y^2$ for some integers $x, y$.
5. If $a \not\equiv 0 \pmod p$, then $G = \sum_{x=0}^{p-1} e^{2\pi i a x^3/p}$ satisfies $G^3 = 3pG + pL$.

Lean statement. In theorem 5, `(a * x ^ 3).val` is the representative of $a x^3$ in $\{0, \dots, p - 1\}$. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Tests of the five statements. Returns the number of checks passed."""
    import cmath
    import math
    from math import isqrt

    def is_prime(n):
        return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))

    def reps(p):                               # all (L, M) with 4p = L^2 + 27 M^2
        out = []
        for M in range(-isqrt(4 * p // 27) - 1, isqrt(4 * p // 27) + 2):
            r = 4 * p - 27 * M * M
            if r >= 0 and isqrt(r) ** 2 == r:
                out += [(isqrt(r), M), (-isqrt(r), M)]
        return out

    def is_sum_x2_27y2(p):
        return any(isqrt(p - 27 * y * y) ** 2 == p - 27 * y * y
                   for y in range(0, isqrt(p // 27) + 1))

    def counts(p):
        cube = {pow(u, 3, p) for u in range(p)}      # mirrors `exists u, u ^ 3 = x`
        n1 = sum(1 for x in range(p) for y in range(p) if (x ** 3 + y ** 3 - 1) % p == 0)
        n2 = sum(1 for x in range(p) if x % p != 0 and (x + 1) % p != 0
                 and x in cube and (x + 1) % p in cube)
        n3 = sum(1 for x in range(p) if x not in cube and (x + 1) % p not in cube
                 and (x * (x + 1)) % p in cube)
        return cube, n1, n2, n3

    ok = 0
    primes = [p for p in range(2, 700) if is_prime(p) and p % 3 == 1]
    for p in primes:
        rs = reps(p)
        good = [(L, M) for L, M in rs if L % 3 == 1]   # Python % = Lean Int.emod here
        assert good and len({L for L, _ in good}) == 1, ("L unique", p, rs)
        cube, n1, n2, n3 = counts(p)
        for L, M in good:
            assert n1 == p - 2 + L, ("card_cubic", p, L)
            assert 9 * n2 == p - 8 + L, ("card_cube_pairs", p, L)
            assert 9 * n3 == 2 * (p + 1 + L), ("card_noncube_pairs", p, L)
            ok += 3
        assert (2 % p in cube) == is_sum_x2_27y2(p), ("two_cube_iff", p)
        ok += 1
        L = good[0][0]
        for a in range(1, p):
            G = sum(cmath.exp(2j * math.pi * ((a * x ** 3) % p) / p) for x in range(p))
            assert abs(G ** 3 - 3 * p * G - p * L) < 1e-6 * p ** 1.5, ("cubic_sum", p, a)
            ok += 1
    # the hypotheses cannot be dropped
    for p in primes[:8]:
        L = next(L for L, _ in reps(p) if L % 3 == 1)
        cube, n1, n2, n3 = counts(p)
        assert n1 != p - 2 - L and 9 * n2 != p - 8 - L      # the condition L = 1 (mod 3)
    assert any(2 % p in counts(p)[0] for p in primes)       # both sides of theorem 4 occur
    assert any(2 % p not in counts(p)[0] for p in primes)
    for p in [5, 11, 17, 23, 29]:                           # p = 2 (mod 3): theorem 4 fails
        assert 2 % p in counts(p)[0] and not is_sum_x2_27y2(p)
    p, L = 7, 1                                             # a = 0 is excluded in theorem 5
    assert abs(p ** 3 - 3 * p * p - p * L) > 1
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

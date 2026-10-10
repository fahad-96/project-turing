#!/usr/bin/env python3
"""Project Turing, task 7 generator (proof writing): a cubic character sum modulo p.

Writes, next to this script:
  task7_prompt.txt               the prompt to paste into the platform
  TuringTask/Basic.lean          the definition and five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden

Self-verifying: tests all five statements with exact integer arithmetic for every prime
p = 1 (mod 4) below 700, mirroring the Lean definition literally (x over range p, the
Legendre symbol by Euler's criterion, checked against a list of squares), for many integers
c and r outside one period and for every representation p = a^2 + b^2 with signs; checks that
the hypotheses cannot be dropped; asserts that every generated file is pure ASCII.
Run:  python turing_t7_generator.py
"""

TASK = 7
COUNT_WORD = "five"
KEEP = ("the definition, and the names and statements of the five theorems")

PRELUDE = """\
noncomputable def csum (p : Nat) [Fact p.Prime] (c : Int) : Int :=
  Finset.sum (Finset.range p) (fun x : Nat => legendreSym p ((x : Int) ^ 3 - c * (x : Int)))
"""

THEOREMS = [
    ("csum_sq_add_sq",
     "(p : Nat) [Fact p.Prime] (hp : p % 4 = 1) (c r : Int)\n"
     "    (hc : legendreSym p c = 1) (hr : legendreSym p r = -1)", """\
    csum p c ^ 2 + csum p r ^ 2 = 4 * (p : Int)"""),
    ("csum_sq_of_sq",
     "(p : Nat) [Fact p.Prime] (hp : p % 4 = 1) (a b c : Int)\n"
     "    (hab : a ^ 2 + b ^ 2 = (p : Int)) (ha : a % 2 = 1) (hc : legendreSym p c = 1)", """\
    csum p c ^ 2 = 4 * a ^ 2"""),
    ("csum_one_emod",
     "(p : Nat) [Fact p.Prime] (hp : p % 4 = 1)", """\
    csum p 1 % 8 = if p % 8 = 5 then 2 else 6"""),
    ("choose_modEq",
     "(p : Nat) [Fact p.Prime] (hp : p % 4 = 1) (a b : Int)\n"
     "    (hab : a ^ 2 + b ^ 2 = (p : Int)) (ha : a % 4 = 1)", """\
    Int.ModEq (p : Int) ((Nat.choose (p / 2) (p / 4) : Nat) : Int) (2 * a)"""),
    ("card_curve",
     "(p : Nat) [Fact p.Prime] (hp : p % 4 = 1) (a b : Int)\n"
     "    (hab : a ^ 2 + b ^ 2 = (p : Int)) (ha : a % 4 = 1)", """\
    ((Finset.univ.filter (fun q : Prod (ZMod p) (ZMod p) => q.2 ^ 2 = q.1 ^ 3 - q.1)).card : Int) =
      (p : Int) - 2 * (-1) ^ (p / 4) * a"""),
]

# Type-checks only if the submitted definition is definitionally the one given in the prompt.
DEF_CHECK = """\
example (p : Nat) [Fact p.Prime] (c : Int) : TuringTask.csum p c =
    Finset.sum (Finset.range p) (fun x : Nat => legendreSym p ((x : Int) ^ 3 - c * (x : Int))) :=
  rfl
"""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. For an odd prime $p$ and an integer $c$ let $S_p(c) = \sum_{x=0}^{p-1} \big(\tfrac{x^3 - cx}{p}\big)$, where $\big(\tfrac{\cdot}{p}\big)$ is the Legendre symbol. Let $p$ be a prime with $p \equiv 1 \pmod 4$.

1. If $c$ is a nonzero square and $r$ is a non-square modulo $p$, then $S_p(c)^2 + S_p(r)^2 = 4p$.
2. If $p = a^2 + b^2$ with $a$ odd and $c$ is a nonzero square modulo $p$, then $S_p(c)^2 = 4a^2$.
3. $S_p(1) \equiv 2 \pmod 8$ if $p \equiv 5 \pmod 8$, and $S_p(1) \equiv 6 \pmod 8$ if $p \equiv 1 \pmod 8$.
4. If $p = a^2 + b^2$ with $a \equiv 1 \pmod 4$, then $\binom{(p-1)/2}{(p-1)/4} \equiv 2a \pmod p$.
5. If $p = a^2 + b^2$ with $a \equiv 1 \pmod 4$, then the number of pairs $(x, y) \in (\mathbb{Z}/p\mathbb{Z})^2$ with $y^2 = x^3 - x$ is $p - 2(-1)^{(p-1)/4}a$.

Lean statement. `csum p c` is $S_p(c)$ and `legendreSym p a` is Mathlib's Legendre symbol. The file `@FILE@` must contain this definition and the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Exact integer tests of the five statements. Returns the number of checks passed."""
    from math import comb, isqrt

    def is_prime(n):
        return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))

    def legendre(a, p):                        # Euler's criterion
        a %= p
        if a == 0:
            return 0
        return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

    def csum(p, c):                            # mirrors `csum`
        return sum(legendre(x ** 3 - c * x, p) for x in range(p))

    def lean_emod(x, m):                       # Int.emod, non-negative for m > 0
        return x % m

    ok = 0
    primes = [p for p in range(5, 700) if is_prime(p) and p % 4 == 1]
    for p in primes[:20]:                      # Euler's criterion against a list of squares
        squares = {(x * x) % p for x in range(1, p)}
        assert all(legendre(a, p) == (0 if a % p == 0 else (1 if a % p in squares else -1))
                   for a in range(-p, 2 * p))
    for p in primes:
        reps = [(a, b) for a in range(-isqrt(p), isqrt(p) + 1)
                for b in range(-isqrt(p), isqrt(p) + 1) if a * a + b * b == p]
        nonsq = [r for r in range(1, p) if legendre(r, p) == -1]
        vals = {c: csum(p, c) for c in range(-p, 2 * p)}
        for c in range(-p, 2 * p):
            if legendre(c, p) == 1:
                for r in (nonsq[0], nonsq[-1] - p, nonsq[len(nonsq) // 2] + p):
                    assert vals[c] ** 2 + vals[r] ** 2 == 4 * p, ("csum_sq_add_sq", p, c, r)
                    ok += 1
                for a, b in reps:
                    if a % 2 == 1:
                        assert vals[c] ** 2 == 4 * a * a, ("csum_sq_of_sq", p, c, a)
                        ok += 1
        assert lean_emod(vals[1], 8) == (2 if p % 8 == 5 else 6), ("csum_one_emod", p)
        ok += 1
        count = sum(1 for x in range(p) for y in range(p) if (y * y - x ** 3 + x) % p == 0)
        for a, b in reps:
            if a % 4 == 1:
                assert (comb(p // 2, p // 4) - 2 * a) % p == 0, ("choose_modEq", p, a)
                assert count == p - 2 * (-1) ** (p // 4) * a, ("card_curve", p, a)
                ok += 2
    # the hypotheses cannot be dropped
    p = 13
    assert csum(p, 1) ** 2 + csum(p, 4) ** 2 != 4 * p                      # r must be a non-square
    assert csum(p, 1) ** 2 != 4 * 2 ** 2                                   # a must be odd
    assert (comb(p // 2, p // 4) - 2 * 3) % p != 0                         # a = 1 mod 4 is needed
    assert any(sum(1 for x in range(q) for y in range(q) if (y * y - x ** 3 + x) % q == 0)
               != q - 2 * next(a for a in range(-9, 10) for b in range(10)
                               if a * a + b * b == q and a % 4 == 1)
               for q in primes[:6])                                        # the sign (-1)^((p-1)/4)
    assert any(lean_emod(csum(q, 1), 8) != 2 for q in primes[:6])          # the case split mod 8
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
        parts.append(f"example {binders} :\n{statement} :=\n  {NAMESPACE}.{name} {args}\n")
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
    print(f"task {TASK}: exact integer checks passed: {n_checks}")
    for rel, (text, _) in files.items():
        print(f"  wrote {rel}: {len(text)} chars, ASCII ok")


if __name__ == "__main__":
    main()

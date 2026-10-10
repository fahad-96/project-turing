#!/usr/bin/env python3
"""Project Turing, task 6 generator (proof writing): five exponential and cotangent sums.

Writes, next to this script:
  task6_prompt.txt               the prompt to paste into the platform
  TuringTask/Basic.lean          the two definitions and five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden

Self-verifying: tests all five statements numerically (double precision, tolerance 1e-8),
mirroring the Lean definitions literally (ranges, the term k = 0, the value of `rt`),
cross-checks the Legendre symbol against a brute-force list of squares, checks that the
hypotheses and signs cannot be dropped, and asserts that every generated file is pure ASCII.
Run:  python turing_t6_generator.py
"""

TASK = 6
COUNT_WORD = "five"
KEEP = ("the two definitions, and the names and statements of the five theorems")

PRELUDE = """\
noncomputable def ex (x : Real) : Complex :=
  Complex.exp (2 * (Real.pi : Complex) * Complex.I * (x : Complex))

noncomputable def rt (n : Nat) : Complex :=
  if n % 4 = 1 then ((Real.sqrt (n : Real) : Real) : Complex)
  else Complex.I * ((Real.sqrt (n : Real) : Real) : Complex)
"""

THEOREMS = [
    ("sum_sq",
     "(n : Nat) (hn : n % 2 = 1)", """\
    Finset.sum (Finset.range n) (fun k : Nat => ex ((k : Real) ^ 2 / (n : Real))) = rt n"""),
    ("sum_tri",
     "(n : Nat) (hn : n % 2 = 1)", """\
    Finset.sum (Finset.range n) (fun k : Nat =>
        ex ((k : Real) * ((k : Real) + 1) / (2 * (n : Real)))) =
      ex (((n : Real) - 1) / (8 * (n : Real))) * ((Real.sqrt (n : Real) : Real) : Complex)"""),
    ("sum_legendre",
     "(p : Nat) [Fact p.Prime] (hp : p % 2 = 1) (a : Int)", """\
    Finset.sum (Finset.range p) (fun k : Nat =>
        ((legendreSym p (k : Int) : Int) : Complex) *
          ex ((a : Real) * (k : Real) / (p : Real))) =
      ((legendreSym p a : Int) : Complex) * rt p"""),
    ("sum_sq_mul",
     "(p q : Nat) [Fact p.Prime] [Fact q.Prime]\n"
     "    (hp : p % 2 = 1) (hq : q % 2 = 1) (hpq : Not (p = q))", """\
    Finset.sum (Finset.range p) (fun j : Nat =>
        ex ((q : Real) * (j : Real) ^ 2 / (p : Real))) *
      Finset.sum (Finset.range q) (fun k : Nat =>
        ex ((p : Real) * (k : Real) ^ 2 / (q : Real))) = rt (p * q)"""),
    ("sum_cot",
     "(p : Nat) [Fact p.Prime] (hp : p % 4 = 3)", """\
    Real.sqrt (p : Real) * Finset.sum (Finset.range p) (fun k : Nat =>
        ((legendreSym p (k : Int) : Int) : Real) *
          Real.cot (Real.pi * (k : Real) / (p : Real))) =
      -2 * Finset.sum (Finset.range p) (fun k : Nat =>
        (k : Real) * ((legendreSym p (k : Int) : Int) : Real))"""),
]

# Type-checks only if the submitted definitions are definitionally the ones given in the
# prompt (a submission must not redefine them).
DEF_CHECK = """\
example (x : Real) : TuringTask.ex x =
    Complex.exp (2 * (Real.pi : Complex) * Complex.I * (x : Complex)) := rfl

example (n : Nat) : TuringTask.rt n =
    (if n % 4 = 1 then ((Real.sqrt (n : Real) : Real) : Complex)
     else Complex.I * ((Real.sqrt (n : Real) : Real) : Complex)) := rfl
"""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. Write $e(x) = \exp(2\pi i x)$ for real $x$. For an odd integer $n \ge 1$ put $\rho(n) = \sqrt{n}$ if $n \equiv 1 \pmod 4$ and $\rho(n) = i\sqrt{n}$ if $n \equiv 3 \pmod 4$. For an odd prime $p$ and an integer $a$ let $(a|p)$ be the Legendre symbol.

1. For every odd $n \ge 1$: $\sum_{k=0}^{n-1} e(k^2/n) = \rho(n)$.
2. For every odd $n \ge 1$: $\sum_{k=0}^{n-1} e\big(k(k+1)/(2n)\big) = e\big((n-1)/(8n)\big)\sqrt{n}$.
3. For every odd prime $p$ and every integer $a$: $\sum_{k=0}^{p-1} (k|p)\, e(ak/p) = (a|p)\,\rho(p)$.
4. For distinct odd primes $p$ and $q$: $\big(\sum_{j=0}^{p-1} e(q j^2/p)\big)\big(\sum_{k=0}^{q-1} e(p k^2/q)\big) = \rho(pq)$.
5. For every prime $p \equiv 3 \pmod 4$: $\sqrt{p}\,\sum_{k=1}^{p-1} (k|p)\cot(\pi k/p) = -2\sum_{k=1}^{p-1} k\,(k|p)$.

Lean statement. `ex` and `rt` are $e$ and $\rho$; the value of `rt n` for even `n` is never used. `legendreSym p a` is Mathlib's Legendre symbol $(a|p)$. In theorem 5 both sums start at $k = 0$, where the term is zero. The file `@FILE@` must contain these two definitions and five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Numeric tests of the five statements. Returns the number of checks passed."""
    import cmath
    import math

    tol = 1e-8

    def ex(x):                                 # mirrors `ex`
        return cmath.exp(2 * math.pi * 1j * x)

    def rt(n):                                 # mirrors `rt`
        return math.sqrt(n) if n % 4 == 1 else 1j * math.sqrt(n)

    def is_prime(p):
        return p > 1 and all(p % d for d in range(2, int(p ** 0.5) + 1))

    def legendre(a, p):                        # Legendre symbol by Euler's criterion
        a %= p
        if a == 0:
            return 0
        return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

    def cot(x):                                # mirrors `Real.cot` (cot 0 = 0 in Lean)
        return 0.0 if x == 0 else math.cos(x) / math.sin(x)

    def close(u, v):
        return abs(u - v) < tol

    def sq(a, n):                              # sum_{k<n} e(a k^2 / n)
        return sum(ex(a * k * k / n) for k in range(n))

    def tri(n):
        return sum(ex(k * (k + 1) / (2 * n)) for k in range(n))

    def leg_sum(p, a):
        return sum(legendre(k, p) * ex(a * k / p) for k in range(p))

    def cot_lhs(p, s=None):
        return math.sqrt(p) * sum(legendre(k, p) * cot(math.pi * k / p) for k in range(p))

    primes = [p for p in range(3, 220) if is_prime(p)]
    for p in primes[:25]:                      # Legendre symbol against brute-force squares
        squares = {(x * x) % p for x in range(1, p)}
        for a in range(-p, 2 * p):
            want = 0 if a % p == 0 else (1 if a % p in squares else -1)
            assert legendre(a, p) == want
    ok = 0
    for n in range(1, 500, 2):                 # theorems 1 and 2
        assert close(sq(1, n), rt(n)), ("sum_sq", n)
        assert close(tri(n), ex((n - 1) / (8 * n)) * math.sqrt(n)), ("sum_tri", n)
        ok += 2
    for p in primes:                           # theorem 3, every residue class and beyond
        for a in range(-p - 3, 2 * p + 4):
            assert close(leg_sum(p, a), legendre(a, p) * rt(p)), ("sum_legendre", p, a)
            ok += 1
    for p in primes[:22]:                      # theorem 4
        for q in primes[:22]:
            if p != q:
                assert close(sq(q, p) * sq(p, q), rt(p * q)), ("sum_sq_mul", p, q)
                ok += 1
    for p in primes:                           # theorem 5
        if p % 4 == 3:
            rhs = -2 * sum(k * legendre(k, p) for k in range(p))
            assert close(cot_lhs(p), rhs), ("sum_cot", p)
            ok += 1
    # the hypotheses and signs cannot be dropped or changed
    assert not close(sq(1, 2), rt(2)) and not close(sq(1, 4), rt(4))        # n odd in 1
    assert not close(tri(2), ex(1 / 16) * math.sqrt(2))                     # n odd in 2
    assert all(not close(sq(1, n), rt(n).conjugate()) for n in (3, 7, 11))  # the factor i
    assert all(not close(sq(1, n), -rt(n)) for n in range(1, 40, 2))        # the sign
    assert not close(leg_sum(7, 3), legendre(3, 7) * rt(7).conjugate())
    assert not close(sq(3, 3) * sq(3, 3), rt(9))                            # p != q in 4
    assert all(not close(sq(q, p) * sq(p, q), -rt(p * q))
               for p in primes[:8] for q in primes[:8] if p != q)
    assert all(not close(cot_lhs(p), 2 * sum(k * legendre(k, p) for k in range(p)))
               for p in primes if p % 4 == 3)                               # the sign in 5
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
    print(f"task {TASK}: numeric checks passed (double precision): {n_checks}")
    for rel, (text, _) in files.items():
        print(f"  wrote {rel}: {len(text)} chars, ASCII ok")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Project Turing, task 15 generator (proof writing): character sums modulo a prime (the
Polya-Vinogradov inequality) and the least quadratic (and k-th power) non-residue.

Writes, next to this script:
  task15_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden (superseded by the worker)

Self-verifying numerics (exact Legendre symbols by Euler's criterion, floating-point for sqrt, log and
complex character values): theorem 1 for every character of every prime p <= 200 and every N < p
(a character is determined by its value on a primitive root); theorems 2 and 4 for every odd prime
p <= 3000 and every N < p; theorem 3 for every odd prime p <= 3000 and every k >= 2 dividing p - 1;
theorem 5 for every odd prime p <= 3000; the sine-sum bound sum_(a < p) 1 / sin(pi a / p) <= p log p
(the analytic step of the classical proof) for every odd prime p <= 10^4; and that the hypotheses
p != 2 (theorem 2 fails at p = 2, N = 1) and N < p (theorem 4 fails at p = 3, N = 6) cannot be dropped.
Run:  python turing_t15_generator.py
"""

TASK = 15
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "numeric (exact Legendre symbols, floating-point bounds)"

PRELUDE = ""

THEOREMS = [
    ("charSum_norm_le",
     "(p : Nat) (hp : p.Prime) (chi : MulChar (ZMod p) Complex)\n"
     "    (h : Not (chi = 1)) (N : Nat)", """\
    Norm.norm ((Finset.Icc 1 N).sum (fun n => chi (n : ZMod p))) <= Real.sqrt p * Real.log p"""),
    ("legendreSum_le", "(p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat)", """\
    abs (((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int)) : Int) : Real) <=
      Real.sqrt p * Real.log p"""),
    ("exists_not_pow_le",
     "(p k : Nat) (hp : p.Prime) (hk : 2 <= k) (hkp : (p - 1) % k = 0)", """\
    exists n : Nat, 1 <= n /\\ (n : Real) <= Real.sqrt p * Real.log p + 1 /\\
      forall x : ZMod p, Not (x ^ k = (n : ZMod p))"""),
    ("card_residues_sub_le",
     "(p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat)\n    (hN : N < p)", """\
    abs (2 * (((Finset.Icc 1 N).filter (fun n : Nat => legendreSym p (n : Int) = 1)).card : Real) -
        N) <= Real.sqrt p * Real.log p"""),
    ("exists_prime_nonresidue_le", "(p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2))", """\
    exists q : Nat, q.Prime /\\ (q : Real) <= Real.sqrt p * Real.log p + 1 /\\
      legendreSym p (q : Int) = -1"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. $p$ is a prime, $\chi$ is a multiplicative character of $\mathbb{Z}/p$ (`MulChar (ZMod p) Complex`: $\chi(0) = 0$, $\chi$ is multiplicative on units), $\chi = 1$ is the principal character, $\left(\frac{n}{p}\right)$ is the Legendre symbol (`legendreSym p n`, with value $0$ when $p \mid n$), and $\log$ is the natural logarithm. $N$, $n$, $k$ denote natural numbers.

1. If $\chi \ne 1$, then for every $N$: $\left| \sum_{n=1}^{N} \chi(n) \right| \le \sqrt{p} \, \log p$.
2. If $p \ne 2$, then for every $N$: $\left| \sum_{n=1}^{N} \left(\frac{n}{p}\right) \right| \le \sqrt{p} \, \log p$.
3. If $k \ge 2$ and $k \mid p - 1$, there is $n$ with $1 \le n \le \sqrt{p} \, \log p + 1$ that is not a $k$-th power modulo $p$.
4. If $p \ne 2$ and $N < p$, then the number $R$ of quadratic residues among $1, \dots, N$ satisfies $|2R - N| \le \sqrt{p} \, \log p$.
5. If $p \ne 2$, there is a prime $q \le \sqrt{p} \, \log p + 1$ that is a quadratic non-residue modulo $p$.

Lean statement. Sums run over `Finset.Icc 1 N`, `Norm.norm` is the complex absolute value, and `Real.sqrt`, `Real.log` are Mathlib's. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Numeric tests of the five statements. Returns the number of checks passed."""
    from math import sqrt, log, sin, pi, cos
    import cmath

    def is_prime(n):
        return n > 1 and all(n % q for q in range(2, int(n ** 0.5) + 1))

    def legendre(a, p):               # exact, Euler's criterion
        a %= p
        if a == 0:
            return 0
        return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

    def primitive_root(p):
        for g in range(2, p):
            if all(pow(g, (p - 1) // q, p) != 1 for q in range(2, p) if (p - 1) % q == 0 and is_prime(q)):
                return g
        return 1

    ok = 0
    eps = 1e-9
    primes = [p for p in range(3, 3001) if is_prime(p)]
    for p in primes:
        bound = sqrt(p) * log(p)
        s = 0
        for n in range(1, p):                     # theorems 2 and 4 for every N < p
            s += legendre(n, p)
            assert abs(s) <= bound, ("legendreSum_le", p, n, s)
            r = (n + s) // 2                      # residues among 1..n: 2R - n = s
            assert (n + s) % 2 == 0 and abs(2 * r - n) <= bound, ("card_residues_sub_le", p, n)
            ok += 2
        # theorem 5 (and the weaker theorem 3 for k = 2): the least non-residue is prime
        n0 = next(n for n in range(1, p) if legendre(n, p) == -1)
        assert is_prime(n0) and n0 <= bound + 1, ("exists_prime_nonresidue_le", p, n0)
        ok += 1
        for k in range(2, p):                     # theorem 3 for every k >= 2 dividing p - 1
            if (p - 1) % k:
                continue
            powers = {pow(x, k, p) for x in range(p)}
            m = next(n for n in range(1, p) if n % p not in powers)
            assert m <= bound + 1, ("exists_not_pow_le", p, k, m)
            ok += 1
    for p in primes:                              # theorem 1, all characters, p <= 200
        if p > 200:
            break
        bound = sqrt(p) * log(p)
        g = primitive_root(p)
        dlog = {}
        x = 1
        for t in range(p - 1):
            dlog[x] = t
            x = x * g % p
        for j in range(1, p - 1):                 # j = 0 is the principal character
            s = 0
            for n in range(1, p):
                s += cmath.exp(2j * pi * j * dlog[n] / (p - 1))
                assert abs(s) <= bound + eps, ("charSum_norm_le", p, j, n, abs(s))
            ok += 1
    for p in range(3, 10001):                     # the analytic step of the classical proof
        if is_prime(p):
            assert sum(1 / sin(pi * a / p) for a in range(1, p)) <= p * log(p), ("sine sum", p)
            ok += 1
    # hypotheses that cannot be dropped
    assert 1 > sqrt(2) * log(2)                   # theorem 2 at p = 2, N = 1: the sum is 1
    res = sum(1 for n in range(1, 7) if legendre(n, 3) == 1)
    assert abs(2 * res - 6) > sqrt(3) * log(3)    # theorem 4 at p = 3, N = 6 >= p
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

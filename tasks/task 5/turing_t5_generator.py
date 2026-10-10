#!/usr/bin/env python3
"""Project Turing, task 5 generator (proof writing): square and triangular sums of partition numbers.

Writes, next to this script:
  task5_prompt.txt               the prompt to paste into the platform
  TuringTask/Basic.lean          the four definitions and five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden

Self-verifying: tests all five statements numerically with exact integer arithmetic for
0 <= n <= 300, mirroring the Lean definitions literally (natural-number subtraction, guards,
ranges), cross-checks the four counting functions against a brute-force enumeration of all
partitions for n <= 36, checks that the hypotheses and side conditions cannot be dropped, and
asserts that every generated file is pure ASCII.
Run:  python turing_t5_generator.py
"""

TASK = 5
COUNT_WORD = "five"
KEEP = ("the four definitions, and the names and statements of the five theorems")

PRELUDE = """\
noncomputable def pbar (n : Nat) : Nat :=
  Finset.sum Finset.univ (fun l : Nat.Partition n => 2 ^ (Multiset.toFinset l.parts).card)

noncomputable def sqAlt (f : Nat -> Int) (n : Nat) : Int :=
  f n + 2 * Finset.sum (Finset.Icc 1 n) (fun k : Nat =>
    if k ^ 2 <= n then (-1 : Int) ^ k * f (n - k ^ 2) else 0)

noncomputable def eps (n : Nat) : Int :=
  Finset.sum (Finset.Icc (-(n : Int)) (n : Int)) (fun j : Int =>
    if j * (3 * j - 1) = 2 * (n : Int) then (-1 : Int) ^ j.natAbs else 0)

noncomputable def halfSum (g : Nat -> Nat) (n : Nat) : Nat :=
  Finset.sum (Finset.range (n + 1)) (fun k : Nat =>
    if g k <= n /\\ (n - g k) % 2 = 0 then Fintype.card (Nat.Partition ((n - g k) / 2)) else 0)
"""

THEOREMS = [
    ("sqAlt_pbar",
     "(n : Nat) (hn : 0 < n)", """\
    sqAlt (fun m => (pbar m : Int)) n = 0"""),
    ("sqAlt_card_partition",
     "(n : Nat)", """\
    sqAlt (fun m => (Fintype.card (Nat.Partition m) : Int)) n =
      (-1 : Int) ^ n * ((Nat.Partition.oddDistincts n).card : Int)"""),
    ("sqAlt_card_distincts",
     "(n : Nat)", """\
    sqAlt (fun m => ((Nat.Partition.distincts m).card : Int)) n = eps n"""),
    ("card_distincts_eq_halfSum",
     "(n : Nat)", """\
    (Nat.Partition.distincts n).card = halfSum (fun k => k * (k + 1) / 2) n"""),
    ("card_oddDistincts_conv",
     "(n : Nat)", """\
    Finset.sum (Finset.range (n + 1)) (fun a : Nat =>
        (Nat.Partition.oddDistincts a).card * (Nat.Partition.oddDistincts (n - a)).card) +
      (if n % 2 = 0 then Fintype.card (Nat.Partition (n / 2)) else 0) =
      2 * halfSum (fun k => k ^ 2) n"""),
]

# Type-checks only if the submitted definitions are definitionally the ones given in the
# prompt (a submission must not redefine them).
DEF_CHECK = """\
example (n : Nat) : TuringTask.pbar n =
    Finset.sum Finset.univ (fun l : Nat.Partition n =>
      2 ^ (Multiset.toFinset l.parts).card) := rfl

example (f : Nat -> Int) (n : Nat) : TuringTask.sqAlt f n =
    f n + 2 * Finset.sum (Finset.Icc 1 n) (fun k : Nat =>
      if k ^ 2 <= n then (-1 : Int) ^ k * f (n - k ^ 2) else 0) := rfl

example (n : Nat) : TuringTask.eps n =
    Finset.sum (Finset.Icc (-(n : Int)) (n : Int)) (fun j : Int =>
      if j * (3 * j - 1) = 2 * (n : Int) then (-1 : Int) ^ j.natAbs else 0) := rfl

example (g : Nat -> Nat) (n : Nat) : TuringTask.halfSum g n =
    Finset.sum (Finset.range (n + 1)) (fun k : Nat =>
      if g k <= n /\\ (n - g k) % 2 = 0
      then Fintype.card (Nat.Partition ((n - g k) / 2)) else 0) := rfl
"""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. For an integer $n \ge 0$ let $p(n)$, $q(n)$ and $r(n)$ be the numbers of partitions of $n$ into arbitrary parts, into distinct parts, and into distinct odd parts, and let $\overline{p}(n) = \sum_{\lambda} 2^{d(\lambda)}$, the sum over all partitions $\lambda$ of $n$, where $d(\lambda)$ is the number of different part sizes of $\lambda$. For a function $f$ put $A_f(n) = \sum (-1)^k f(n - k^2)$, the sum over all integers $k$ with $k^2 \le n$. Let $e(n) = (-1)^j$ if $n = j(3j-1)/2$ for an integer $j$, and $e(n) = 0$ if there is no such $j$. For every $n \ge 0$:

1. $A_{\overline{p}}(n) = 0$ if $n \ge 1$.
2. $A_p(n) = (-1)^n r(n)$.
3. $A_q(n) = e(n)$.
4. $q(n) = \sum p\big((n - k(k+1)/2)/2\big)$, the sum over all integers $k \ge 0$ for which $n - k(k+1)/2$ is non-negative and even.
5. $\sum_{a=0}^{n} r(a)\, r(n-a) = \sum p\big((n - k^2)/2\big)$, the sum over all integers $k$ for which $n - k^2$ is non-negative and even.

Lean statement. `Nat.Partition n` is Mathlib's type of partitions of `n`; `Nat.Partition.distincts n` and `Nat.Partition.oddDistincts n` are its finite sets of partitions into distinct parts and into distinct odd parts. `pbar`, `sqAlt f` and `eps` are $\overline{p}$, $A_f$ and $e$, and `halfSum g n` is the sum of $p((n - g(k))/2)$ over $0 \le k \le n$ with $n - g(k)$ non-negative and even. In theorem 5 the sum over all integers $k$ is written as twice the sum over $k \ge 0$, with the term for $k = 0$ moved to the left-hand side. Every natural-number subtraction or division is exact wherever its value is used. The file `@FILE@` must contain exactly these four definitions and five theorems, with each `sorry` replaced by a complete proof:
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


def _partitions(n, largest=None):
    """All partitions of n as non-increasing tuples (brute force)."""
    if largest is None:
        largest = n
    if n == 0:
        yield ()
        return
    for first in range(min(n, largest), 0, -1):
        for rest in _partitions(n - first, first):
            yield (first,) + rest


def self_check() -> int:
    """Exact numeric tests of the five statements. Returns the number of checks passed."""
    M, NB = 300, 36
    # generating functions
    part = [1] + [0] * M                       # p(n)
    for k in range(1, M + 1):
        for n in range(k, M + 1):
            part[n] += part[n - k]
    dist = [1] + [0] * M                       # q(n): prod (1 + x^i)
    for i in range(1, M + 1):
        for n in range(M, i - 1, -1):
            dist[n] += dist[n - i]
    odis = [1] + [0] * M                       # r(n): prod (1 + x^(2i-1))
    for i in range(1, M + 1, 2):
        for n in range(M, i - 1, -1):
            odis[n] += odis[n - i]
    over = _mul(dist, part, M + 1)             # pbar(n): prod (1 + x^i) / (1 - x^i)
    assert part[:8] == [1, 1, 2, 3, 5, 7, 11, 15] and part[50] == 204226
    assert dist[:11] == [1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10]
    assert odis[:13] == [1, 1, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]
    assert over[:8] == [1, 2, 4, 8, 14, 24, 40, 64]
    # brute-force cross-check of the four counting functions, straight from the definitions
    for n in range(NB + 1):
        ps = list(_partitions(n))
        assert len(ps) == part[n]
        assert sum(1 for l in ps if len(set(l)) == len(l)) == dist[n]
        assert sum(1 for l in ps if len(set(l)) == len(l) and all(x % 2 for x in l)) == odis[n]
        assert sum(2 ** len(set(l)) for l in ps) == over[n]

    def nat_sub(a, b):                         # natural-number subtraction, as in Lean
        return a - b if a >= b else 0

    def sq_alt(f, n):                          # mirrors `sqAlt`
        return f(n) + 2 * sum(((-1) ** k) * f(nat_sub(n, k * k)) if k * k <= n else 0
                              for k in range(1, n + 1))

    def eps(n):                                # mirrors `eps`
        return sum((-1) ** abs(j) if j * (3 * j - 1) == 2 * n else 0 for j in range(-n, n + 1))

    def half_sum(g, n):                        # mirrors `halfSum`
        return sum(part[nat_sub(n, g(k)) // 2]
                   if g(k) <= n and nat_sub(n, g(k)) % 2 == 0 else 0 for k in range(n + 1))

    assert [eps(n) for n in range(13)] == [1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1]
    ok = 0
    for n in range(M + 1):
        if n >= 1:                             # theorem 1
            assert sq_alt(lambda m: over[m], n) == 0, ("sqAlt_pbar", n)
            ok += 1
        assert sq_alt(lambda m: part[m], n) == (-1) ** n * odis[n], ("sqAlt_card_partition", n)
        assert sq_alt(lambda m: dist[m], n) == eps(n), ("sqAlt_card_distincts", n)
        assert dist[n] == half_sum(lambda k: k * (k + 1) // 2, n), ("card_distincts_eq", n)
        lhs = (sum(odis[a] * odis[nat_sub(n, a)] for a in range(n + 1))
               + (part[n // 2] if n % 2 == 0 else 0))
        assert lhs == 2 * half_sum(lambda k: k * k, n), ("card_oddDistincts_conv", n)
        # theorem 5 in its symmetric form: sum over all integers k
        sym = sum(part[(n - k * k) // 2] for k in range(-n, n + 1)
                  if k * k <= n and (n - k * k) % 2 == 0)
        assert sum(odis[a] * odis[n - a] for a in range(n + 1)) == sym
        ok += 5
    # the hypotheses, signs and side conditions cannot be dropped
    assert sq_alt(lambda m: over[m], 0) == 1                               # n >= 1 in theorem 1
    assert any(sq_alt(lambda m: part[m], n) != odis[n] for n in range(1, 20))
    assert any(part[n] + 2 * sum(part[n - k * k] for k in range(1, n + 1) if k * k <= n)
               != odis[n] for n in range(1, 20))                           # the sign (-1)^k
    assert any(dist[n] != sum(part[(n - k * (k + 1) // 2) // 2] for k in range(n + 1)
                              if k * (k + 1) // 2 <= n) for n in range(1, 20))   # parity
    assert any(sum(odis[a] * odis[n - a] for a in range(n + 1))
               != half_sum(lambda k: k * k, n) for n in range(1, 20))      # factor 2 and k = 0
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
    print(f"task {TASK}: numeric identity checks passed: {n_checks}")
    for rel, (text, _) in files.items():
        print(f"  wrote {rel}: {len(text)} chars, ASCII ok")


if __name__ == "__main__":
    main()

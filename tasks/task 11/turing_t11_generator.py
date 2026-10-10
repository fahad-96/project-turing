#!/usr/bin/env python3
"""Project Turing, task 11 generator (proof writing): colourings and assignments that avoid
every bad configuration under a bounded-dependence condition.

Writes, next to this script:
  task11_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects
  check_outputs.bat              one-click check of model outputs / the golden

Self-verifying on random small instances: generates hypergraphs, clause systems, complete graphs
and intervals that satisfy each hypothesis exactly as the Lean statement states it (incidence
functions, card of filters, e = exp 1), and finds a colouring or assignment with the required
property by exhaustive search (or by random search, checked exactly, where exhaustive search is
too large). These are sanity checks of the statements, not proofs: the theorems are existence
statements for all parameters. Asserts that every generated file is pure ASCII.
Run:  python turing_t11_generator.py
"""

TASK = 11
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "small-instance (sanity, not exhaustive)"

PRELUDE = ""

THEOREMS = [
    ("color_meet",
     "(n m k d : Nat) (I : Fin m -> Fin n -> Bool)\n"
     "    (hk : forall i, (Finset.univ.filter (fun v => I i v = true)).card = k)\n"
     "    (hd : forall i, (Finset.univ.filter (fun j => Not (j = i) /\\\n"
     "      exists v, I i v = true /\\ I j v = true)).card <= d)\n"
     "    (hkd : Real.exp 1 * ((d : Real) + 1) <= 2 ^ (k - 1))", """\
    exists c : Fin n -> Bool, forall i,
      (exists v, I i v = true /\\ c v = true) /\\ (exists v, I i v = true /\\ c v = false)"""),
    ("color_deg",
     "(n m k : Nat) (hk9 : 9 <= k) (I : Fin m -> Fin n -> Bool)\n"
     "    (hk : forall i, (Finset.univ.filter (fun v => I i v = true)).card = k)\n"
     "    (hdeg : forall v, (Finset.univ.filter (fun i => I i v = true)).card <= k)", """\
    exists c : Fin n -> Bool, forall i,
      (exists v, I i v = true /\\ c v = true) /\\ (exists v, I i v = true /\\ c v = false)"""),
    ("sat_exists",
     "(n m k d : Nat) (V s : Fin m -> Fin n -> Bool)\n"
     "    (hk : forall i, (Finset.univ.filter (fun v => V i v = true)).card = k)\n"
     "    (hd : forall i, (Finset.univ.filter (fun j => Not (j = i) /\\\n"
     "      exists v, V i v = true /\\ V j v = true)).card <= d)\n"
     "    (hkd : Real.exp 1 * ((d : Real) + 1) <= 2 ^ k)", """\
    exists x : Fin n -> Bool, forall i, exists v, V i v = true /\\ x v = s i v"""),
    ("ramsey_color",
     "(n k : Nat)\n"
     "    (h : Real.exp 1 * (((Nat.choose k 2 * Nat.choose n (k - 2) : Nat) : Real) + 1)\n"
     "      <= 2 ^ (Nat.choose k 2 - 1))", """\
    exists c : Sym2 (Fin n) -> Bool, forall s : Finset (Fin n), s.card = k ->
      2 <= (s.offDiag.image (fun q => c (Sym2.mk q.1 q.2))).card"""),
    ("ap_color",
     "(N k : Nat) (h : Real.exp 1 * (((k ^ 2 * N : Nat) : Real) + 1) <= 2 ^ (k - 1))", """\
    exists c : Nat -> Bool, forall a r : Nat, 1 <= r -> a + (k - 1) * r < N ->
      2 <= ((Finset.range k).image (fun j => c (a + j * r))).card"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. Write $e = \exp(1)$. A hypergraph on the vertex set $\{0, \dots, n - 1\}$ has edges $E_0, \dots, E_{m-1}$, where $E_i$ is the set of vertices $v$ with $I(i, v)$ true. A 2-colouring of the vertices is proper if no edge is monochromatic.

1. If every edge has $k$ vertices and meets at most $d$ other edges, and $e(d + 1) \le 2^{k-1}$, then the hypergraph has a proper 2-colouring.
2. If $k \ge 9$, every edge has $k$ vertices and every vertex lies in at most $k$ edges, then the hypergraph has a proper 2-colouring.
3. Let clause $i$ (for $i < m$) have the variable set $\{v : V(i, v)\}$ of size $k$; an assignment $x \in \{\mathrm{true}, \mathrm{false}\}^n$ satisfies clause $i$ if $x_v = s(i, v)$ for some variable $v$ of the clause. If every clause shares a variable with at most $d$ other clauses and $e(d + 1) \le 2^k$, then some assignment satisfies every clause.
4. If $e\left(\binom{k}{2}\binom{n}{k-2} + 1\right) \le 2^{\binom{k}{2} - 1}$, then the edges of the complete graph on $n$ vertices can be 2-coloured so that no $k$ vertices span a monochromatic complete subgraph.
5. If $e(k^2 N + 1) \le 2^{k-1}$, then $\{0, \dots, N - 1\}$ can be 2-coloured so that no arithmetic progression of $k$ terms with positive difference is monochromatic.

Lean statement. Edges, clause variable sets and clause signs are given by Boolean functions `I`, `V`, `s`; an edge colouring of the complete graph is a function on `Sym2 (Fin n)`. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""


def self_check() -> int:
    """Small-instance sanity checks. Returns the number of instances checked."""
    import itertools
    import math
    import random
    rng = random.Random(20261008)
    E = math.e
    ok = 0

    def proper(edges, c):
        return all(any(c[v] for v in ed) and any(not c[v] for v in ed) for ed in edges)

    def find_colouring(n, test, tries=20000):
        if n <= 16:
            for bits in itertools.product([False, True], repeat=n):
                if test(bits):
                    return bits
            return None
        for _ in range(tries):
            c = [rng.random() < 0.5 for _ in range(n)]
            if test(c):
                return c
        return None

    def meets(edges, i):
        return sum(1 for j in range(len(edges)) if j != i and set(edges[i]) & set(edges[j]))

    # 1. hypergraphs with k = 5 and d = 4 (e * 5 <= 16)
    k, d = 5, 4
    assert E * (d + 1) <= 2 ** (k - 1)
    made = 0
    while made < 40:
        n = rng.randint(6, 14)
        m = rng.randint(1, 8)
        edges = [rng.sample(range(n), k) for _ in range(m)]
        if max(meets(edges, i) for i in range(m)) > d:
            continue
        assert find_colouring(n, lambda c: proper(edges, c)) is not None, ("color_meet", edges)
        made += 1
        ok += 1
    # 2. k = 9, every vertex in at most 9 edges (the bound e (k(k-1)+1) <= 2^(k-1) holds)
    assert E * (9 * 8 + 1) <= 2 ** 8 and E * (8 * 7 + 1) > 2 ** 7
    for _ in range(15):
        n = rng.randint(12, 22)
        m = rng.randint(2, 14)
        edges = [rng.sample(range(n), 9) for _ in range(m)]
        if max(sum(1 for ed in edges if v in ed) for v in range(n)) > 9:
            continue
        assert find_colouring(n, lambda c: proper(edges, c)) is not None, ("color_deg", edges)
        ok += 1
    # 3. clauses with k = 4 distinct variables, d = 4 (e * 5 <= 16)
    k, d = 4, 4
    made = 0
    while made < 40:
        n = rng.randint(5, 14)
        m = rng.randint(1, 9)
        cls = [(rng.sample(range(n), k), [rng.random() < 0.5 for _ in range(n)]) for _ in range(m)]
        vs = [c[0] for c in cls]
        if max(meets(vs, i) for i in range(m)) > d:
            continue
        test = lambda x: all(any(x[v] == sg[v] for v in var) for var, sg in cls)
        assert find_colouring(n, test) is not None, ("sat_exists", cls)
        made += 1
        ok += 1
    # 4. complete graphs: largest n allowed by the hypothesis for k = 5, 6, 7
    for k in (5, 6, 7):
        n = 0
        while E * (math.comb(k, 2) * math.comb(n + 1, k - 2) + 1) <= 2 ** (math.comb(k, 2) - 1):
            n += 1
        assert n >= k
        pairs = list(itertools.combinations(range(n), 2))
        subsets = list(itertools.combinations(range(n), k))
        found = False
        for _ in range(200):
            col = {p: rng.random() < 0.5 for p in pairs}
            if all(len({col[p] for p in itertools.combinations(s, 2)}) == 2 for s in subsets):
                found = True
                break
        assert found, ("ramsey_color", k, n)
        ok += 1
    # 5. intervals: largest N allowed for k = 14, 16, 18
    for k in (14, 16, 18):
        N = 0
        while E * (k * k * (N + 1) + 1) <= 2 ** (k - 1):
            N += 1
        aps = [(a, r) for r in range(1, N) for a in range(N) if a + (k - 1) * r < N]
        found = False
        for _ in range(200):
            c = [rng.random() < 0.5 for _ in range(N)]
            if all(len({c[a + j * r] for j in range(k)}) == 2 for a, r in aps):
                found = True
                break
        assert found, ("ap_color", k, N)
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

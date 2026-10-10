#!/usr/bin/env python3
"""Project Turing, task 22 generator (proof writing): three cubes in arithmetic progression and the
rational points of y^2 = x^3 + 1 and y^2 = x^3 - 27 (Euler, Legendre).

Writes, next to this script:
  task22_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)
(check_outputs.bat is no longer written: lean_worker_git.bat jobs replaced it.)

Self-verifying with exact integer and Fraction arithmetic:
  - theorem 1 for every pair |x|, |y| <= 1200 (x <= y; then |z| <= 1200 automatically);
  - theorems 2 and 3: every rational point of y^2 = x^3 + k has x = a/d^2, y = b/d^3 with
    gcd(a, d) = 1; all such points with 1 <= d <= 60, |a| <= 20000 are found and compared with the
    stated sets (the stated points are on the curves, so the sets cannot be smaller);
  - theorem 4 for every |y| <= 300000, theorem 5 for every n <= 3000000;
  - the identities of the planned golden route (Euler's parametrization of cubes of the form
    u^2 + 3 v^2, the substitution x = u + v, y = u - v, the rational maps from y^2 = x^3 + 1 to
    Y^2 = X^3 - 27 and from Y^2 = X^3 - 27 to u^3 + v^3 = 2), checked exactly at many points;
  - for each theorem, a witness showing that its hypothesis cannot be dropped.
There is no finite search space: all variables are unbounded integers, rationals or naturals.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t22_generator.py
"""

TASK = 22
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

THEOREMS = [
    ("cube_add_cube_eq_two_mul_cube", "(x y z : Int) (h : x ^ 3 + y ^ 3 = 2 * z ^ 3)", """\
    x = y \\/ x + y = 0"""),
    ("rat_sq_eq_cube_add_one", "(x y : Rat) (h : y ^ 2 = x ^ 3 + 1)", """\
    Membership.mem ({(-1, 0), (0, 1), (0, -1), (2, 3), (2, -3)} : Finset (Prod Rat Rat))
      (x, y)"""),
    ("rat_sq_eq_cube_sub_27", "(x y : Rat) (h : y ^ 2 = x ^ 3 - 27)", """\
    x = 3 /\\ y = 0"""),
    ("cube_sub_two_mul_cube",
     "(x y : Int)\n    (h : x ^ 3 - 2 * y ^ 3 = 1 \\/ x ^ 3 - 2 * y ^ 3 = -1)", """\
    Membership.mem ({(1, 0), (-1, -1), (-1, 0), (1, 1)} : Finset (Prod Int Int))
      (x, y)"""),
    ("mul_succ_eq_two_mul_cube", "(n m : Nat) (h : n * (n + 1) = 2 * m ^ 3)", """\
    n = 0 \\/ n = 1"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. In each item the variables are integers, rational numbers or natural numbers, as stated.

1. If $x, y, z \in \mathbb{Z}$ and $x^3 + y^3 = 2 z^3$, then $x = y$ or $x + y = 0$.
2. If $x, y \in \mathbb{Q}$ and $y^2 = x^3 + 1$, then $(x, y)$ is one of $(-1, 0)$, $(0, 1)$, $(0, -1)$, $(2, 3)$, $(2, -3)$.
3. If $x, y \in \mathbb{Q}$ and $y^2 = x^3 - 27$, then $x = 3$ and $y = 0$.
4. If $x, y \in \mathbb{Z}$ and $x^3 - 2 y^3 = 1$ or $x^3 - 2 y^3 = -1$, then $(x, y)$ is one of $(1, 0)$, $(-1, -1)$, $(-1, 0)$, $(1, 1)$.
5. If $n, m \in \mathbb{N}$ and $n (n + 1) = 2 m^3$ (the triangular number $n (n + 1) / 2$ is a cube), then $n = 0$ or $n = 1$.

Lean statement. `Membership.mem S a` is the membership statement $a \in S$ for a finite set `S`. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""

EXTRA_RULE = """Nothing may be declared inside the namespace `@NS@` that shadows a Mathlib name: every name used in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements and of the identities of the planned proof."""
    from fractions import Fraction as Fr
    from math import gcd, isqrt
    import random

    def icbrt(n):                      # exact integer cube root (floor toward -inf for n >= 0)
        if n < 0:
            return -icbrt(-n)
        r = int(round(n ** (1.0 / 3.0)))
        while r ** 3 > n:
            r -= 1
        while (r + 1) ** 3 <= n:
            r += 1
        return r

    counts = {}

    # theorem 1: x^3 + y^3 = 2 z^3 with |x|, |y| <= B (x <= y); then |z| <= B
    B = 1200
    twice = {2 * z ** 3 for z in range(-B, B + 1)}
    pairs = sols = 0
    for x in range(-B, B + 1):
        cx = x ** 3
        for y in range(x, B + 1):
            pairs += 1
            if cx + y ** 3 in twice:
                sols += 1
                assert x == y or x + y == 0, ("cube_add_cube_eq_two_mul_cube", x, y)
    assert sols == (2 * B + 1) + B          # the diagonal x = y and the antidiagonal x = -y < y
    counts["thm1 pairs"] = pairs

    # theorems 2 and 3: rational points with denominators d^2, d^3, gcd(a, d) = 1
    def rat_points(k, dmax, amax):
        pts = set()
        tried = 0
        for d in range(1, dmax + 1):
            d6 = d ** 6
            for a in range(-amax, amax + 1):
                if gcd(a, d) != 1:
                    continue
                tried += 1
                v = a ** 3 + k * d6
                if v < 0:
                    continue
                b = isqrt(v)
                if b * b == v:
                    pts.add((Fr(a, d * d), Fr(b, d ** 3)))
                    pts.add((Fr(a, d * d), Fr(-b, d ** 3)))
        return pts, tried

    stated2 = {(Fr(-1), Fr(0)), (Fr(0), Fr(1)), (Fr(0), Fr(-1)), (Fr(2), Fr(3)), (Fr(2), Fr(-3))}
    for (x, y) in stated2:
        assert y * y == x ** 3 + 1
    pts2, tried2 = rat_points(1, 60, 20000)
    assert pts2 == stated2, sorted(pts2)
    assert Fr(0) ** 2 == Fr(3) ** 3 - 27
    pts3, tried3 = rat_points(-27, 60, 20000)
    assert pts3 == {(Fr(3), Fr(0))}, sorted(pts3)
    counts["thm2 candidates"] = tried2
    counts["thm3 candidates"] = tried3

    # theorem 4: x^3 - 2 y^3 = +-1 for |y| <= 300000
    found4 = set()
    Y = 300000
    for y in range(-Y, Y + 1):
        for e in (1, -1):
            v = 2 * y ** 3 + e
            x = icbrt(v)
            if x ** 3 == v:
                found4.add((x, y))
    assert found4 == {(1, 0), (-1, -1), (-1, 0), (1, 1)}, sorted(found4)
    counts["thm4 values of y"] = 2 * Y + 1

    # theorem 5: n (n + 1) = 2 m^3 for n <= 3000000
    N5 = 3000000
    found5 = [n for n in range(N5 + 1) if icbrt(n * (n + 1) // 2) ** 3 * 2 == n * (n + 1)]
    assert found5 == [0, 1], found5
    counts["thm5 values of n"] = N5 + 1

    # identities of the planned golden route
    ident = 0
    for a in range(-30, 31):
        for b in range(-30, 31):
            u, v = a ** 3 - 9 * a * b * b, 3 * a * a * b - 3 * b ** 3
            assert u * u + 3 * v * v == (a * a + 3 * b * b) ** 3
            ident += 1
    # Euler's lemma (search): u^2 + 3 v^2 a cube with gcd(u, 3 v) = 1 => parametrized as above
    param = {}
    for a in range(-40, 41):
        for b in range(-40, 41):
            param[(a ** 3 - 9 * a * b * b, 3 * a * a * b - 3 * b ** 3)] = (a, b)
    cubes = {c ** 3 for c in range(0, 400)}
    lemma_cases = 0
    for u in range(-1000, 1001):
        for v in range(-1000, 1001):
            if gcd(u, 3 * v) == 1 and u * u + 3 * v * v in cubes:
                lemma_cases += 1
                assert (u, v) in param, ("Euler lemma", u, v)
    assert lemma_cases > 0
    rnd = random.Random(22)
    for _ in range(2000):
        u, v = rnd.randint(-10 ** 6, 10 ** 6), rnd.randint(-10 ** 6, 10 ** 6)
        x, y = u + v, u - v
        assert x ** 3 + y ** 3 == 2 * u * (u * u + 3 * v * v)
        ident += 1
    for _ in range(2000):
        x = Fr(rnd.randint(-500, 500), rnd.randint(1, 60))
        if x == 0:
            continue
        t = x ** 3
        X = (t + 4) / (x * x)
        assert (t + 1) * (t - 8) ** 2 / (t * t) == X ** 3 - 27     # Y = y (x^3 - 8) / x^3
        ident += 1
    for _ in range(2000):
        X = Fr(rnd.randint(-500, 500), rnd.randint(1, 60))
        if X == 0:
            continue
        s, d2 = 6 / X, 4 * (X ** 3 - 27) / (9 * X * X)              # s = u + v, d = u - v
        assert s ** 3 + 3 * s * d2 == 8                               # 4 (u^3 + v^3) = 8
        ident += 1
    counts["route identities"] = ident
    counts["Euler lemma cases"] = lemma_cases

    # each hypothesis is needed: without it the conclusion fails at these points
    assert not (1 == 2 or 1 + 2 == 0)                                 # (x, y, z) = (1, 2, 0)
    assert (Fr(1), Fr(1)) not in stated2                              # (x, y) = (1, 1)
    assert not (Fr(0) == 3)                                           # (x, y) = (0, 0)
    assert (2, 0) not in found4                                       # (x, y) = (2, 0)
    assert 2 not in found5                                            # (n, m) = (2, 0)
    return counts


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
    text = PROMPT_BODY + "\n```lean\n" + lean_source() + "```\n\n" + RULES + "\n" + EXTRA_RULE
    return (text.replace("@FILE@", LEAN_FILE).replace("@NS@", NAMESPACE)
            .replace("@KEEP@", KEEP).replace("@COUNT@", COUNT_WORD)
            .replace("@TOOLCHAIN@", TOOLCHAIN).replace("@COMMIT@", MATHLIB_COMMIT))


def assert_ascii(label: str, text: str) -> None:
    bad = sorted({ch for ch in text if ord(ch) > 127 or (ord(ch) < 32 and ch not in "\n\r")})
    assert not bad, f"{label}: non-ASCII or control characters {bad!r}"


def main() -> None:
    here = Path(__file__).resolve().parent
    counts = self_check()
    files = {
        f"task{TASK}_prompt.txt": prompt_text(),
        LEAN_FILE: lean_source(),
        "StatementAndAxiomsCheck.lean": check_source(),
    }
    for rel, text in files.items():
        assert_ascii(rel, text)
    assert "@" not in prompt_text().replace("@[", ""), "unreplaced placeholder in prompt"
    assert lean_source() in prompt_text()
    assert RULES.replace("@NS@", NAMESPACE).replace("@KEEP@", KEEP).replace(
        "@COUNT@", COUNT_WORD).replace("@TOOLCHAIN@", TOOLCHAIN).replace(
        "@COMMIT@", MATHLIB_COMMIT) in prompt_text()
    for rel in (LEAN_FILE, "StatementAndAxiomsCheck.lean"):
        assert max(len(line) for line in files[rel].splitlines()) <= 100, rel
    for rel, text in files.items():
        path = here / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="ascii", newline="\n") as fh:
            fh.write(text)
    print(f"task {TASK}: {CHECK_KIND} checks passed:")
    for key, val in counts.items():
        print(f"  {key}: {val}")
    print("  search space: unbounded variables (no finite search applies)")
    for rel, text in files.items():
        print(f"  wrote {rel}: {len(text)} chars, ASCII ok")


if __name__ == "__main__":
    main()

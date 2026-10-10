#!/usr/bin/env python3
"""Project Turing, task 23 generator (proof writing): consecutive integers without large prime
factors, and smooth values of x^2 - 1, x^2 + 1 and of the solutions of x^2 - 2 y^2 = +-1
(Stormer 1897, Lehmer 1964).

Writes, next to this script:
  task23_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)
(check_outputs.bat is no longer written: lean_worker_git.bat jobs replaced it.)

Self-verifying with exact integer arithmetic:
  - theorems 1-3: every pair of 7-smooth numbers below 10^16 is enumerated (all 7-smooth numbers
    are generated), so the stated sets are complete below 10^16; brute force for n, x <= 10^6;
  - theorem 4: every {2, 5, 13}-smooth m <= 10^20 with m - 1 a square (3, 7, 11 never divide
    x^2 + 1), plus brute force x <= 10^6;
  - theorem 5: all solutions of x^2 - 2 y^2 = +-1 come from (1 + sqrt 2)^k; checked for k <= 400
    and by brute force for y <= 10^6;
  - the data of the planned golden route (Pell equations x^2 - D y^2 = 1 for the 15 squarefree
    D > 1 dividing 210, x^2 - D y^2 = -1 for the 7 squarefree D > 1 dividing 130: fundamental
    solutions, which powers have smooth y, reconstruction of the stated sets from them, and the
    prime factors of y_p / y_1 for primes p <= 13, all = p or +-1 mod p);
  - the Nat edge cases (n = 0, x <= 1: N = 0 is divisible by every prime) and, for each theorem,
    a witness showing that each hypothesis cannot be dropped.
There is no finite search space: n, x, y are unbounded natural numbers.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t23_generator.py
"""

TASK = 23
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

L1 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 20, 24, 27, 35, 48, 49, 63, 80, 125, 224, 2400, 4374]
L2 = [2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 15, 17, 19, 26, 29, 31, 41, 49, 55, 71, 97, 99, 127, 161,
      244, 251, 449, 4801, 8749]
L3 = [1, 2, 3, 4, 5, 6, 7, 8, 14, 48]
L4 = [0, 1, 2, 3, 5, 7, 8, 18, 57, 239]
L5 = [1, 2, 5, 12, 70, 169, 13860]

THEOREMS = [
    ("mul_succ_smooth_seven",
     "(n : Nat)\n    (h : forall p : Nat, p.Prime -> n * (n + 1) % p = 0 -> p <= 7)", """\
    Membership.mem ({1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 20, 24, 27, 35, 48, 49, 63, 80, 125, 224,
      2400, 4374} : Finset Nat) n"""),
    ("sq_sub_one_smooth_seven",
     "(x : Nat)\n    (h : forall p : Nat, p.Prime -> (x ^ 2 - 1) % p = 0 -> p <= 7)", """\
    Membership.mem ({2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 15, 17, 19, 26, 29, 31, 41, 49, 55, 71, 97,
      99, 127, 161, 244, 251, 449, 4801, 8749} : Finset Nat) x"""),
    ("three_consecutive_smooth_seven",
     "(n : Nat)\n    (h : forall p : Nat, p.Prime -> n * (n + 1) * (n + 2) % p = 0 -> p <= 7)", """\
    Membership.mem ({1, 2, 3, 4, 5, 6, 7, 8, 14, 48} : Finset Nat) n"""),
    ("sq_add_one_smooth_thirteen",
     "(x : Nat)\n    (h : forall p : Nat, p.Prime -> (x ^ 2 + 1) % p = 0 -> p <= 13)", """\
    Membership.mem ({0, 1, 2, 3, 5, 7, 8, 18, 57, 239} : Finset Nat) x"""),
    ("sq_sub_two_mul_sq_smooth_thirteen",
     "(x y : Nat)\n    (h : x ^ 2 = 2 * y ^ 2 + 1 \\/ x ^ 2 + 1 = 2 * y ^ 2)\n"
     "    (hs : forall p : Nat, p.Prime -> y % p = 0 -> p <= 13)", """\
    Membership.mem ({1, 2, 5, 12, 70, 169, 13860} : Finset Nat) y"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. All variables are natural numbers. The condition "every prime factor of $N$ is at most $B$" is written in Lean as: every prime $p$ with $N \bmod p = 0$ satisfies $p \le B$. Every prime divides $0$, so the condition fails for $N = 0$; note that $x^2 - 1$ is computed in $\mathbb{N}$, so it equals $0$ for $x \le 1$.

1. If every prime factor of $n (n + 1)$ is at most $7$, then $n \in \{1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 20, 24, 27, 35, 48, 49, 63, 80, 125, 224, 2400, 4374\}$.
2. If every prime factor of $x^2 - 1$ is at most $7$, then $x \in \{2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 15, 17, 19, 26, 29, 31, 41, 49, 55, 71, 97, 99, 127, 161, 244, 251, 449, 4801, 8749\}$.
3. If every prime factor of $n (n + 1) (n + 2)$ is at most $7$, then $n \in \{1, 2, 3, 4, 5, 6, 7, 8, 14, 48\}$.
4. If every prime factor of $x^2 + 1$ is at most $13$, then $x \in \{0, 1, 2, 3, 5, 7, 8, 18, 57, 239\}$.
5. If $x^2 - 2 y^2 = 1$ or $x^2 - 2 y^2 = -1$, and every prime factor of $y$ is at most $13$, then $y \in \{1, 2, 5, 12, 70, 169, 13860\}$.

Lean statement. `Membership.mem S a` is the membership statement $a \in S$ for a finite set `S`. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""

EXTRA_RULE = """Nothing may be declared inside the namespace `@NS@` that shadows a Mathlib name: every name used in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements and of the data of the planned proof."""
    from math import isqrt, gcd

    def factor_small(n, primes):
        for p in primes:
            while n % p == 0:
                n //= p
        return n

    def smooth(n, primes):
        return n > 0 and factor_small(n, primes) == 1

    def prime_factors_trial(n, bound):
        out, d = [], 2
        while d * d <= n and d <= bound:
            if n % d == 0:
                out.append(d)
                while n % d == 0:
                    n //= d
            d += 1
        return out, n

    def lean_hyp(N, B):             # forall p prime, N % p = 0 -> p <= B  (Lean Nat semantics)
        if N == 0:
            return False            # p = B + 1 or the next prime divides 0
        return smooth(N, [p for p in (2, 3, 5, 7, 11, 13) if p <= B])

    def smooth_numbers(primes, limit):
        out = [1]
        for p in primes:
            new = []
            for v in out:
                while v <= limit:
                    new.append(v)
                    v *= p
            out = new
        return sorted(out)

    counts = {}
    S7 = [2, 3, 5, 7]
    LIM = 10 ** 16
    sm7 = smooth_numbers(S7, LIM)
    st7 = set(sm7)
    counts["7-smooth numbers below 10^16"] = len(sm7)
    l1 = [n for n in sm7 if n + 1 in st7]
    assert l1 == L1, l1
    l2 = [n + 1 for n in sm7 if n + 2 in st7]
    assert l2 == L2, l2
    l3 = [n for n in l1 if n + 1 in set(l1)]
    assert l3 == L3, l3
    # brute force and the Lean hypotheses, including the Nat edge cases
    B = 10 ** 6
    bf1 = [n for n in range(0, B) if lean_hyp(n * (n + 1), 7)]
    bf2 = [x for x in range(0, B) if lean_hyp(max(x * x - 1, 0), 7)]
    bf3 = [n for n in range(0, B) if lean_hyp(n * (n + 1) * (n + 2), 7)]
    assert bf1 == L1 and bf2 == L2 and bf3 == L3
    assert not lean_hyp(0 * 1, 7) and not lean_hyp(0, 7)      # n = 0 and x <= 1 are excluded
    counts["brute force n, x below 10^6"] = 3 * B

    # theorem 4
    for p in (3, 7, 11):
        assert all((x * x + 1) % p for x in range(p))          # 3, 7, 11 never divide x^2 + 1
    sm13 = smooth_numbers([2, 5, 13], 10 ** 20)
    l4 = sorted(isqrt(m - 1) for m in sm13 if isqrt(m - 1) ** 2 == m - 1)
    assert l4 == L4, l4
    bf4 = [x for x in range(0, B) if lean_hyp(x * x + 1, 13)]
    assert bf4 == L4
    counts["{2,5,13}-smooth numbers below 10^20"] = len(sm13)

    # theorem 5: x + y sqrt 2 = (1 + sqrt 2)^k
    x, y, l5 = 1, 0, []
    for k in range(1, 401):
        x, y = x + 2 * y, x + y
        assert x * x - 2 * y * y == (-1) ** k
        if smooth(y, [2, 3, 5, 7, 11, 13]):
            l5.append(y)
    assert l5 == L5, l5
    bf5 = []
    for yy in range(0, B):
        for e in (1, -1):
            v = 2 * yy * yy + e
            if v >= 0 and isqrt(v) ** 2 == v and lean_hyp(yy, 13):
                bf5.append(yy)
    assert sorted(set(bf5)) == L5
    counts["Pell powers k <= 400 and y <= 10^6"] = 400 + B

    # data of the planned golden route
    def fundamental(D, sign):
        yy = 1
        while True:
            v = D * yy * yy + sign
            if v > 0 and isqrt(v) ** 2 == v:
                return isqrt(v), yy
            yy += 1

    def powers(D, x1, y1, K):
        out, xx, yy = [], 1, 0
        for k in range(1, K + 1):
            xx, yy = xx * x1 + D * yy * y1, xx * y1 + yy * x1
            out.append((k, xx, yy))
        return out

    D210 = sorted({a * b * c * d for a in (1, 2) for b in (1, 3) for c in (1, 5)
                   for d in (1, 7)} - {1})
    assert len(D210) == 15
    cand1, cand2, lemma_checks = set(), set(), 0
    for D in D210:
        x1, y1 = fundamental(D, 1)
        pw = powers(D, x1, y1, 60)
        ks = [k for (k, xx, yy) in pw if smooth(yy, S7)]
        assert max(ks) <= 4, (D, ks)
        for (k, xx, yy) in pw[:4]:
            if xx % 2 == 1:
                cand1.add((xx - 1) // 2)
            cand2.add(xx)
        for p in (5, 7, 11, 13):
            u = pw[p - 1][2] // y1
            assert pw[p - 1][2] % y1 == 0
            qs, rest = prime_factors_trial(u, 10 ** 5)
            assert all(q == p or q % p in (1, p - 1) for q in qs), (D, p, qs)
            assert u > p                                           # so u has a prime factor > 7
            lemma_checks += 1
    assert sorted(n for n in cand1 if lean_hyp(n * (n + 1), 7)) == L1
    assert sorted(x for x in cand2 if lean_hyp(x * x - 1, 7)) == L2
    D130 = [2, 5, 10, 13, 26, 65, 130]
    cand4 = {0}
    for D in D130:
        x1, y1 = fundamental(D, -1)
        for (k, xx, yy) in powers(D, x1, y1, 61):
            if k % 2 == 1:
                assert xx * xx - D * yy * yy == -1
                if smooth(yy, [5, 13]):
                    assert k in ((1, 3, 7) if D == 2 else (1,)), (D, k)
                    cand4.add(xx)
    assert sorted(cand4) == L4
    counts["Pell data: D | 210 and D | 130"] = len(D210) + len(D130)
    counts["prime-index factor checks"] = lemma_checks

    # each hypothesis is needed
    assert 10 not in L1 and 10 not in L2 and 9 not in L3 and 4 not in L4   # drop h
    assert not (1 == 2 * 3 * 3 + 1 or 1 + 1 == 2 * 3 * 3) and 3 not in L5  # drop h: (x, y) = (1, 3)
    assert 41 * 41 + 1 == 2 * 29 * 29 and 29 not in L5                     # drop hs: (41, 29)
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

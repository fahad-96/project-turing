#!/usr/bin/env python3
"""Project Turing, task 25 generator (proof writing): Fibonacci and Lucas numbers next to a
square or to twice a square (Finkelstein 1973 and 1975, Robbins 1981 and 1988; methods of
Cohn 1964).

Theorems: F_n + 1 is a square iff n in {0, 4, 6};  F_n = x^2 + 1 iff n in {1, 2, 3, 5};
F_n = 2 x^2 + 1 iff n in {1, 2, 4};  L_n = x^2 + 1 iff n in {0, 1};  L_n + 1 = 2 x^2 iff
n in {1, 4, 11}.  L_n = 2 F_(n+1) - F_n is written additively in Lean (no subtraction).

Writes, next to this script:
  task25_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic:
  - all five statements, both directions, for every n <= 4000 (exact integer square roots;
    the Lean encodings of the Lucas statements are checked against L_n directly);
  - the planned golden route, exactly: (a) the Cohn-type coverings by Jacobi symbols: for each
    residue class of n mod 2^j a base m with F_n = -F_m or L_n = -L_m (mod L_(2^s)) and
    (A_m / L_(2^s)) = -1 for EVERY s in the range, proved by computing the eventually periodic
    sequence L_(2^s) mod 8|A_m| (theorems 2 and 3 for all n; theorems 4 and 5 for even n; the
    lemma L_n = 3 x^2 for n = 2 mod 4), cross-checked with big-integer Jacobi symbols for
    n <= 4000; (b) the factorizations F_n + 1 = F_a L_b, L_n - 1 and L_n + 1 = L_a L_b or
    5 F_a F_b (n odd) with their gcds, for n <= 2000; (c) the square classes used: F_n in
    {x^2, 2 x^2, 5 x^2, 10 x^2}, L_n in {x^2, 2 x^2, 3 x^2} for n <= 4000, and the quintic
    identity F_5k = 5 F_k (5 F_k^4 + 5 (-1)^k F_k^2 + 1); (d) the case analysis that rebuilds
    the stated sets from (b) and (c);
  - the statements have no hypotheses, so no witness is needed; n = 11 in theorem 5
    (L_11 = 199 = 2 * 10^2 - 1) and n = 6 in theorem 1 (F_6 + 1 = 9, from the gcd-3 branch)
    are the sharp cases.
There is no finite search space: n and x are unbounded natural numbers.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t25_generator.py
"""

TASK = 25
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

S1, S2, S3, S4, S5 = [0, 4, 6], [1, 2, 3, 5], [1, 2, 4], [0, 1], [1, 4, 11]

THEOREMS = [
    ("fib_add_one_eq_sq_iff",
     "(n : Nat)", """\
    (exists x : Nat, Nat.fib n + 1 = x ^ 2) <-> Membership.mem ({0, 4, 6} : Finset Nat) n"""),
    ("fib_eq_sq_add_one_iff",
     "(n : Nat)", """\
    (exists x : Nat, Nat.fib n = x ^ 2 + 1) <-> Membership.mem ({1, 2, 3, 5} : Finset Nat) n"""),
    ("fib_eq_two_mul_sq_add_one_iff",
     "(n : Nat)", """\
    (exists x : Nat, Nat.fib n = 2 * x ^ 2 + 1) <->
      Membership.mem ({1, 2, 4} : Finset Nat) n"""),
    ("lucas_eq_sq_add_one_iff",
     "(n : Nat)", """\
    (exists x : Nat, Nat.fib n + (x ^ 2 + 1) = 2 * Nat.fib (n + 1)) <->
      Membership.mem ({0, 1} : Finset Nat) n"""),
    ("lucas_add_one_eq_two_mul_sq_iff",
     "(n : Nat)", """\
    (exists x : Nat, Nat.fib n + 2 * x ^ 2 = 2 * Nat.fib (n + 1) + 1) <->
      Membership.mem ({1, 4, 11} : Finset Nat) n"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. $F_n$ is the $n$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$; `Nat.fib n` in Mathlib) and $L_n = F_{n-1} + F_{n+1} = 2 F_{n+1} - F_n$ is the $n$-th Lucas number ($L_0 = 2$, $L_1 = 1$, $L_2 = 3$, $L_{n+2} = L_{n+1} + L_n$). In the Lean statements an equation $L_n = c$ is written $F_n + c = 2 F_{n+1}$, so that no subtraction occurs. All variables are natural numbers.

1. $F_n + 1$ is a perfect square if and only if $n \in \{0, 4, 6\}$.
2. $F_n = x^2 + 1$ for some $x$ if and only if $n \in \{1, 2, 3, 5\}$.
3. $F_n = 2 x^2 + 1$ for some $x$ if and only if $n \in \{1, 2, 4\}$.
4. $L_n = x^2 + 1$ for some $x$ if and only if $n \in \{0, 1\}$.
5. $L_n + 1 = 2 x^2$ for some $x$ if and only if $n \in \{1, 4, 11\}$.

Lean statement. `Membership.mem S a` is the membership statement $a \in S$ for a finite set `S`. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""

EXTRA_RULE = """Nothing may be declared inside the namespace `@NS@` that shadows a Mathlib name: every name used in the five statements must keep its Mathlib meaning.
"""

TREES = {}


def self_check() -> dict:
    """Exact tests of the five statements and of the data of the planned proof."""
    from math import isqrt, gcd

    NMAX = 4000
    counts = {}

    F = [0, 1]
    while len(F) < NMAX + 3:
        F.append(F[-1] + F[-2])
    L = [2, 1]
    while len(L) < NMAX + 3:
        L.append(L[-1] + L[-2])

    def Fi(m):
        """F_m for an integer index (F_(-m) = (-1)^(m+1) F_m)."""
        return F[m] if m >= 0 else (-1) ** (-m + 1) * F[-m]

    def Li(m):
        return L[m] if m >= 0 else (-1) ** (-m) * L[-m]

    def issq(v):
        return v >= 0 and isqrt(v) ** 2 == v

    def cls(v, c):
        """v = c * x^2 for some natural x."""
        return v >= 0 and v % c == 0 and issq(v // c)

    # ---- 1. the five statements for n <= NMAX
    st = 0
    for n in range(NMAX + 1):
        assert L[n] == 2 * F[n + 1] - F[n]
        t1 = issq(F[n] + 1)
        t2 = F[n] >= 1 and issq(F[n] - 1)
        t3 = F[n] >= 1 and cls(F[n] - 1, 2)
        t4 = L[n] >= 1 and issq(L[n] - 1)
        t5 = cls(L[n] + 1, 2)
        assert t1 == (n in S1) and t2 == (n in S2) and t3 == (n in S3), n
        assert t4 == (n in S4) and t5 == (n in S5), n
        st += 5
    counts["theorems 1-5, both directions, n <= %d" % NMAX] = st

    # ---- 2a. Jacobi coverings (Cohn's method with base m and moduli L_(2^s))
    def jacobi(a, n):
        assert n > 0 and n % 2 == 1
        a %= n
        res = 1
        while a:
            while a % 2 == 0:
                a //= 2
                if n % 8 in (3, 5):
                    res = -res
            a, n = n, a
            if a % 4 == 3 and n % 4 == 3:
                res = -res
            a %= n
        return res if n == 1 else 0

    def jac_res(A, r):
        """(A / N) for odd N > 0 with N = r (mod 8|A|), by reciprocity."""
        sgn = -1 if A < 0 else 1
        A, e = abs(A), 0
        while A % 2 == 0:
            A //= 2
            e += 1
        res = 1
        if sgn < 0 and r % 4 == 3:
            res = -res
        if e % 2 == 1 and r % 8 in (3, 5):
            res = -res
        if A == 1:
            return res
        if A % 4 == 3 and r % 4 == 3:
            res = -res
        return res * jacobi(r % A, A)

    def symbols_from(A, s0):
        """Set of values (A / L_(2^s)) over all s >= s0 >= 1, exactly: L_(2^s) mod 8|A| is
        eventually periodic (x -> x^2 - 2), so the orbit from s0 on is finite."""
        if A == 0:
            return {0}
        M = 8 * abs(A)
        x, s = 3 % M, 1          # L_2 = 3
        while s < s0:
            x, s = (x * x - 2) % M, s + 1
        seen, vals = set(), set()
        while x not in seen:
            seen.add(x)
            vals.add(jac_res(A, x))
            x = (x * x - 2) % M
        return vals

    def find_tree(X, a, b, start, bases=range(-40, 60), maxdepth=12):
        """Uniform leaves (r, j, m): n = r (mod 2^j), n != m  ==>  contradiction."""
        A = {m: b - a * X(m) for m in bases}
        leaves, work = [], list(start)
        while work:
            r, j = work.pop(0)
            M = 2 ** j
            for m in sorted(bases, key=lambda t: (abs(t), t)):
                if (m - r) % M == 0 and symbols_from(A[m], max(1, j - 1)) == {-1}:
                    leaves.append((r, j, m))
                    break
            else:
                assert j < maxdepth, "no covering"
                work += [(r, j + 1), (r + M, j + 1)]
        return leaves, A

    cover_specs = [
        ("thm 2: F_n - 1 = x^2", Fi, 1, -1, [(r, 2) for r in range(4)], S2, F),
        ("thm 3: 2 F_n - 2 = (2x)^2", Fi, 2, -2, [(r, 2) for r in range(4)], S3, F),
        ("thm 4, n even: L_n - 1 = x^2", Li, 1, -1, [(0, 2), (2, 2)], S4, L),
        ("thm 5, n even: 2 L_n + 2 = (2x)^2", Li, 2, 2, [(0, 2), (2, 2)], S5, L),
        ("lemma: 3 L_n = (3x)^2, n = 2 mod 4", Li, 3, 0, [(2, 2)], [], L),
    ]
    cov = 0
    for label, X, a, b, start, sols, seq in cover_specs:
        leaves, A = find_tree(X, a, b, start)
        TREES[label] = leaves
        # the leaves partition the start classes
        for n in range(NMAX + 1):
            hits = [lf for lf in leaves if n % 2 ** lf[1] == lf[0]]
            in_start = any(n % 2 ** j == r for r, j in start)
            assert len(hits) == (1 if in_start else 0), (label, n)
            if not in_start:
                continue
            r, j, m = hits[0]
            v = a * seq[n] + b
            if n == m:
                # the base itself: checked directly
                assert issq(v) == (n in sols) or label.startswith("lemma"), (label, n)
                continue
            # n != m: the congruence argument applies, so a X_n + b is not a square
            d = n - m
            s = (d & -d).bit_length() - 2
            assert s >= max(1, j - 1)
            Lk = L[2 ** s] if 2 ** s <= NMAX + 2 else None
            if Lk is not None:
                assert (seq[n] + X(m)) % Lk == 0, (label, n, m, s)
                assert jacobi(A[m], Lk) == -1, (label, n, m, s)
            assert not issq(v), (label, n)
            cov += 1
    counts["covered n <= %d by the Jacobi leaves (periodicity proved exactly)" % NMAX] = cov
    counts["covering leaves (thm 2, thm 3, thm 4 even, thm 5 even, L = 3x^2)"] = (
        "%d, %d, %d, %d, %d" % tuple(len(TREES[c[0]]) for c in cover_specs))

    # ---- 2b. factorizations and gcds
    fac = 0
    for a in range(-60, 61):
        for b in range(-60, 61):
            sg = (-1) ** (b % 2)
            assert Fi(a + b) + sg * Fi(a - b) == Fi(a) * Li(b)
            assert Fi(a + b) - sg * Fi(a - b) == Fi(b) * Li(a)
            assert Li(a + b) + sg * Li(a - b) == Li(a) * Li(b)
            assert Li(a + b) - sg * Li(a - b) == 5 * Fi(a) * Fi(b)
            fac += 4
    for n in range(8, 2001):
        k, r = divmod(n, 4)
        if r == 0:
            fa, lb = 2 * k - 1, 2 * k + 1
        elif r == 1:
            fa, lb = 2 * k + 1, 2 * k
        elif r == 2:
            fa, lb = 2 * k + 2, 2 * k
        else:
            fa, lb = 2 * k + 1, 2 * k + 2
        assert F[n] + 1 == F[fa] * L[lb]
        g = gcd(F[fa], L[lb])
        assert g == (3 if (r == 2 and k % 2 == 1) else 1), n
        fac += 2
        if n % 2 == 1:
            a_, b_ = (n + 1) // 2, (n - 1) // 2
            if n % 4 == 1:
                assert L[n] + 1 == L[a_] * L[b_] and L[n] - 1 == 5 * F[a_] * F[b_]
            else:
                assert L[n] - 1 == L[a_] * L[b_] and L[n] + 1 == 5 * F[a_] * F[b_]
            assert gcd(L[a_], L[b_]) == 1 and gcd(F[a_], F[b_]) == 1
            fac += 2
    counts["factorization identities and gcds checked"] = fac

    # ---- 2c. square classes used by the route, and the quintic identity
    sq = 0
    expect_F = {1: [0, 1, 2, 12], 2: [0, 3, 6], 3: [0, 4], 5: [0, 5], 10: [0]}
    expect_L = {1: [1, 3], 2: [0, 6], 3: [2], 6: []}
    for c, lst in expect_F.items():
        assert [n for n in range(NMAX + 1) if cls(F[n], c)] == lst, c
        sq += NMAX + 1
    for c, lst in expect_L.items():
        assert [n for n in range(NMAX + 1) if cls(L[n], c)] == lst, c
        sq += NMAX + 1
    for k in range(0, 300):
        f = F[k]
        q = 5 * f ** 4 + 5 * (-1) ** k * f ** 2 + 1
        assert F[5 * k] == 5 * f * q and gcd(f, q) == 1 and q % 2 == 1
        sq += 1
    counts["square classes (F: x^2, 2x^2, 3x^2, 5x^2, 10x^2; L: x^2, 2x^2, 3x^2, 6x^2)"] = sq

    # ---- 2d. rebuild the stated sets from the case analysis (n >= 8; n < 8 directly)
    SQ_F, D2_F, D5_F, D10_F = set(expect_F[1]), set(expect_F[2]), set(expect_F[5]), set(expect_F[10])
    SQ_L, D2_L, D3_L = set(expect_L[1]), set(expect_L[2]), set(expect_L[3])
    B = 1000
    sol1 = set(n for n in range(8) if issq(F[n] + 1))
    for n in range(8, B):
        k, r = divmod(n, 4)
        fa, lb = {0: (2 * k - 1, 2 * k + 1), 1: (2 * k + 1, 2 * k), 2: (2 * k + 2, 2 * k),
                  3: (2 * k + 1, 2 * k + 2)}[r]
        if r == 2 and k % 2 == 1:
            ok = lb in D3_L            # gcd 3: L_b = 3 y^2 forces b = 2
        else:
            ok = fa in SQ_F and lb in SQ_L
        if ok:
            sol1.add(n)
    assert sorted(sol1) == S1
    sol4 = set(n for n in range(8) if n in S4)
    sol5 = set(n for n in range(8) if n in S5)
    for n in range(9, B, 2):
        a_, b_ = (n + 1) // 2, (n - 1) // 2
        if n % 4 == 1:
            if (a_ in SQ_F and b_ in D5_F) or (a_ in D5_F and b_ in SQ_F):
                sol4.add(n)            # L_n - 1 = 5 F_a F_b
            if (a_ in SQ_L and b_ in D2_L) or (a_ in D2_L and b_ in SQ_L):
                sol5.add(n)            # L_n + 1 = L_a L_b
        else:
            if a_ in SQ_L and b_ in SQ_L:
                sol4.add(n)            # L_n - 1 = L_a L_b
            if ((a_ in SQ_F and b_ in D10_F) or (a_ in D10_F and b_ in SQ_F)
                    or (a_ in D2_F and b_ in D5_F) or (a_ in D5_F and b_ in D2_F)):
                sol5.add(n)            # L_n + 1 = 5 F_a F_b
    for n in range(8, B, 2):           # even n: the Jacobi coverings leave only the bases
        if issq(L[n] - 1):
            sol4.add(n)
        if cls(L[n] + 1, 2):
            sol5.add(n)
    assert sorted(sol4) == S4 and sorted(sol5) == S5
    counts["stated sets rebuilt from the case analysis (theorems 1, 4, 5)"] = 3
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

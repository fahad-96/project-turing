#!/usr/bin/env python3
"""Project Turing, task 39 generator (proof writing): polynomial functions modulo n (Kempner 1918,
1921; Keller and Olson 1968).

A function F : Z/n -> Z/n is a polynomial function if F(x) = P(x) for a polynomial P over Z/n.
Theorems:
  1. (Newton series) for n >= 1, F is polynomial iff gcd(n, j!) divides the j-th forward
     difference of the representatives F(0), F(1), ... for every j < n
  2. (Kempner) for n >= 1 there are prod_{j<n} n / gcd(n, j!) polynomial functions on Z/n
  3. (Keller-Olson) p prime, k >= 2: the number N of bijective polynomial functions on Z/p^k
     satisfies N p^(2p) = p! (p-1)^p prod_{j<p^k} p^k / gcd(p^k, j!)
  4. (Kempner's function) p prime, k >= 1, s least with p^k | s!: with a_i = (p^(i+1)-1)/(p-1),
     k = sum c_i a_i and s = sum c_i p^(i+1) for digits 0 <= c_i <= p, top digit >= 1, and
     only zeros below a digit equal to p
  5. n >= 2, s least with n | s!: every polynomial function comes from a polynomial of degree
     < s, and some polynomial function needs degree >= s - 1

Writes, next to this script:
  task39_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic:
  - the polynomial functions on Z/n, computed independently as the lattice spanned by the
    monomial functions and n Z^n (echelon form, every n <= 40) and, for 12 values of n, as an
    explicit set (closure under addition by breadth-first search);
  - theorem 1 for every function on Z/n with n <= 6 and for random functions and random
    polynomial functions with 7 <= n <= 40; theorem 2 for n <= 40; theorem 3 for
    p^k = 4, 8, 16, 9; theorem 4 for every prime p < 50 and k <= 400 (uniqueness of the digits
    for p <= 5, k <= 60); theorem 5 for 2 <= n <= 40;
  - the data of the planned golden route: forward differences of the falling factorials,
    Legendre's formula, and the reduction map F -> (F mod p, F' mod p) on Z/p^2;
  - a numeric witness for every hypothesis: dropping it makes the statement false.
There is no finite search space: n, p, k, s, F are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t39_generator.py
"""

TASK = 39
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

POLYF = "exists P : Polynomial (ZMod n), forall x, F x = P.eval x"

THEOREMS = [
    ("exists_polynomial_iff",
     "(n : Nat) (hn : 0 < n) (F : ZMod n -> ZMod n)",
     "    (exists P : Polynomial (ZMod n), forall x : ZMod n, F x = P.eval x) <->\n"
     "      forall j : Nat, j < n ->\n"
     "        (Finset.range (j + 1)).sum (fun i =>\n"
     "            (-1 : Int) ^ (j - i) * (j.choose i : Int) * ((F (i : ZMod n)).val : Int)) %\n"
     "          (Nat.gcd n j.factorial : Int) = 0"),
    ("ncard_polynomial_functions",
     "(n : Nat) (hn : 0 < n)",
     "    Set.ncard {F : ZMod n -> ZMod n | " + POLYF + "} =\n"
     "      (Finset.range n).prod (fun j => n / Nat.gcd n j.factorial)"),
    ("ncard_bijective_polynomial_functions",
     "(p k : Nat) (hp : p.Prime) (hk : 2 <= k)",
     "    Set.ncard {F : ZMod (p ^ k) -> ZMod (p ^ k) |\n"
     "        Function.Bijective F /\\\n"
     "          exists P : Polynomial (ZMod (p ^ k)), forall x, F x = P.eval x} * p ^ (2 * p) =\n"
     "      p.factorial * (p - 1) ^ p *\n"
     "        (Finset.range (p ^ k)).prod (fun j => p ^ k / Nat.gcd (p ^ k) j.factorial)"),
    ("exists_digits_of_minimal",
     "(p k s : Nat) (hp : p.Prime) (hk : 1 <= k)\n"
     "    (hs : s.factorial % p ^ k = 0)\n"
     "    (hmin : forall m : Nat, m < s -> Not (m.factorial % p ^ k = 0))",
     "    exists (t : Nat) (c : Nat -> Nat), 1 <= c t /\\ (forall i, i <= t -> c i <= p) /\\\n"
     "      (forall i j, i < j -> j <= t -> c j = p -> c i = 0) /\\\n"
     "      k = (Finset.range (t + 1)).sum (fun i => c i * ((p ^ (i + 1) - 1) / (p - 1))) /\\\n"
     "      s = (Finset.range (t + 1)).sum (fun i => c i * p ^ (i + 1))"),
    ("natDegree_lt_of_minimal",
     "(n s : Nat) (hn : 2 <= n) (hs : s.factorial % n = 0)\n"
     "    (hmin : forall m : Nat, m < s -> Not (m.factorial % n = 0))",
     "    (forall P : Polynomial (ZMod n), exists Q : Polynomial (ZMod n),\n"
     "        Q.natDegree < s /\\ forall x, P.eval x = Q.eval x) /\\\n"
     "      exists P : Polynomial (ZMod n), forall Q : Polynomial (ZMod n),\n"
     "        (forall x, P.eval x = Q.eval x) -> s - 1 <= Q.natDegree"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. For $n \ge 1$, a function $F : \mathbb{Z}/n \to \mathbb{Z}/n$ is a polynomial function if there is a polynomial $P$ with coefficients in $\mathbb{Z}/n$ such that $F(x) = P(x)$ for all $x$. For integers $v_0, v_1, \dots$ write $\Delta^j v = \sum_{i=0}^{j} (-1)^{j-i} \binom{j}{i} v_i$ for the $j$-th forward difference at $0$.

1. (Newton series.) Let $n \ge 1$. A function $F$ on $\mathbb{Z}/n$ is a polynomial function if and only if $\gcd(n, j!)$ divides $\Delta^j v$ for every $j < n$, where $v_i \in \{0, \dots, n-1\}$ represents $F(i)$.
2. (Kempner.) For $n \ge 1$ there are exactly $\prod_{j=0}^{n-1} n/\gcd(n, j!)$ polynomial functions on $\mathbb{Z}/n$.
3. (Keller and Olson.) Let $p$ be a prime and $k \ge 2$. The number $N$ of bijective polynomial functions on $\mathbb{Z}/p^k$ satisfies $N p^{2p} = p! \, (p-1)^p \prod_{j=0}^{p^k-1} p^k/\gcd(p^k, j!)$.
4. (Kempner's function.) Let $p$ be a prime, $k \ge 1$, and let $s$ be the least integer with $p^k \mid s!$. Put $a_i = (p^{i+1}-1)/(p-1)$. Then there are $t \ge 0$ and digits $0 \le c_i \le p$ with $c_t \ge 1$ such that $k = \sum_{i=0}^{t} c_i a_i$, $s = \sum_{i=0}^{t} c_i p^{i+1}$, and every digit below a digit equal to $p$ is $0$.
5. Let $n \ge 2$ and let $s$ be the least integer with $n \mid s!$. Every polynomial function on $\mathbb{Z}/n$ comes from a polynomial of degree less than $s$, and some polynomial function comes from no polynomial of degree less than $s - 1$.

Lean statement. A polynomial function appears as `exists P : Polynomial (ZMod n), forall x, F x = P.eval x`, the counts in theorems 2 and 3 use `Set.ncard` of a set of functions `ZMod n -> ZMod n`, and divisibility uses `%` with `= 0`. In theorem 1 the representative of $F(i)$ is `(F i).val`, and in theorems 4 and 5 two hypotheses state that $s$ is the least integer with the divisibility property. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    from math import gcd, comb, factorial
    import random

    counts = {}
    rng = random.Random(39)

    def is_prime(n):
        return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))

    def kempner(n):                                   # least s with n | s!
        s, f = 0, 1
        while f % n:
            s += 1
            f *= s
        return s

    def vfact(p, m):                                  # Legendre: v_p(m!)
        v, q = 0, p
        while q <= m:
            v += m // q
            q *= p
        return v

    def kempner_pk(p, k):                             # least s with p^k | s!
        s = 0
        while vfact(p, s) < k:
            s += p
        return s

    def span(n, gens):
        """additive subgroup of (Z/n)^n generated by the tuples in gens (BFS closure)."""
        zero = (0,) * n
        seen = {zero}
        frontier = [zero]
        while frontier:
            new = []
            for v in frontier:
                for g in gens:
                    w = tuple((a + b) % n for a, b in zip(v, g))
                    if w not in seen:
                        seen.add(w)
                        new.append(w)
            frontier = new
        return seen

    def mono(n, m):
        return tuple(pow(i, m, n) if n > 1 else 0 for i in range(n))

    def hnf(n, gens):
        """echelon basis of the lattice spanned by gens and n Z^n (entries kept mod n)."""
        rem = [[x % n for x in g] for g in gens] + [[n if j == i else 0 for j in range(n)]
                                                  for i in range(n)]
        H = []
        for c in range(n):
            piv = [r for r in rem if r[c] % n]
            others = [r for r in rem if not r[c] % n]
            piv.append([n if j == c else 0 for j in range(n)])
            while len(piv) > 1:
                piv.sort(key=lambda r: abs(r[c]))
                p0, nxt = piv[0], [piv[0]]
                for r in piv[1:]:
                    q = r[c] // p0[c]
                    rr = [x - q * y for x, y in zip(r, p0)]
                    rr = rr[:c + 1] + [x % n for x in rr[c + 1:]]
                    (nxt if rr[c] else others).append(rr)
                piv = nxt
            p0 = piv[0] if piv[0][c] > 0 else [-x for x in piv[0]]
            H.append(p0)
            rem = [r[:c + 1] + [x % n for x in r[c + 1:]] for r in others]
        return H

    def order(H, n):
        d = 1
        for c in range(n):
            d *= H[c][c]
        assert n ** n % d == 0
        return n ** n // d

    def member(H, n, v):
        v = [x % n for x in v]
        for c in range(n):
            if v[c] % H[c][c]:
                return False
            q = v[c] // H[c][c]
            v = [(x - q * y) % n for x, y in zip(v, H[c])]
        return not any(v)

    def kempner_count(n):
        r = 1
        for j in range(n):
            r *= n // gcd(n, factorial(j))
        return r

    SMALL = [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16]
    POLY = {n: span(n, [mono(n, m) for m in range(n + 3)]) for n in SMALL}
    HN = {n: hnf(n, [mono(n, m) for m in range(n + 3)]) for n in range(1, 41)}

    CR = {}

    def crit(n, F):                                   # the condition of theorem 1
        if n not in CR:
            CR[n] = [(gcd(n, factorial(j)), [(-1) ** (j - i) * comb(j, i) for i in range(j + 1)])
                     for j in range(n)]
        for g, co in CR[n]:
            if g > 1 and sum(c * x for c, x in zip(co, F)) % g:
                return False
        return True

    # theorem 2: span of the monomials, two independent computations
    for n in range(1, 41):
        assert order(HN[n], n) == kempner_count(n), n
        assert member(HN[n], n, mono(n, n + 3))
    for n in SMALL:
        assert len(POLY[n]) == kempner_count(n), n
    counts["theorem 2 (Kempner's count), every n <= 40 (explicit sets for 12 values)"] = 40

    # theorem 1: all functions for n <= 6, samples for 7 <= n <= 40
    t1 = 0
    from itertools import product
    for n in range(1, 7):
        for F in product(range(n), repeat=n):
            assert crit(n, F) == (F in POLY[n]) == member(HN[n], n, F), (n, F)
            t1 += 1
    for n in range(7, 41):
        gens = [mono(n, m) for m in range(n + 3)]
        for _ in range(400):
            F = tuple(rng.randrange(n) for _ in range(n))
            assert crit(n, F) == member(HN[n], n, F), (n, F)
            G = [0] * n                               # a random polynomial function
            for g in gens:
                c = rng.randrange(n)
                G = [(a + c * b) % n for a, b in zip(G, g)]
            assert crit(n, G) and member(HN[n], n, G)
            t1 += 2
    counts["theorem 1 (Newton series), functions tested for n <= 40"] = t1

    # theorem 3
    t3 = 0
    for p, k in ((2, 2), (2, 3), (2, 4), (3, 2)):
        q = p ** k
        N = sum(1 for F in POLY[q] if len(set(F)) == q)
        assert N * p ** (2 * p) == factorial(p) * (p - 1) ** p * kempner_count(q), (p, k)
        t3 += N
    counts["theorem 3 (Keller-Olson), bijective polynomial functions for p^k = 4, 8, 16, 9"] = t3

    # theorem 4
    def digits(p, k):                                 # greedy expansion in the scale a_i
        a = [1]
        while p * a[-1] + 1 <= k:
            a.append(p * a[-1] + 1)
        c, r = [0] * len(a), k
        for i in range(len(a) - 1, -1, -1):
            c[i], r = divmod(r, a[i])
        assert r == 0
        return c, a

    def admissible(p, c):
        t = len(c) - 1
        if c[t] < 1 or any(x > p for x in c):
            return False
        return all(c[i] == 0 for j in range(t + 1) if c[j] == p for i in range(j))

    t4 = 0
    for p in [x for x in range(2, 50) if is_prime(x)]:
        for k in range(1, 401):
            s = kempner_pk(p, k)
            c, a = digits(p, k)
            assert admissible(p, c), (p, k, c)
            assert sum(ci * ai for ci, ai in zip(c, a)) == k
            assert sum(ci * p ** (i + 1) for i, ci in enumerate(c)) == s, (p, k)
            t4 += 1
    for p in (2, 3, 5):                               # uniqueness of admissible digits
        for k in range(1, 61):
            s = kempner_pk(p, k)
            assert s == kempner(p ** k) or k > 30
            sols = []
            for t in range(0, 6):
                a = [(p ** (i + 1) - 1) // (p - 1) for i in range(t + 1)]
                if a[t] > k:
                    break
                for c in product(range(p + 1), repeat=t + 1):
                    if admissible(p, list(c)) and sum(x * y for x, y in zip(c, a)) == k:
                        sols.append((t, c))
            assert len(sols) == 1, (p, k, sols)
            t, c = sols[0]
            assert sum(ci * p ** (i + 1) for i, ci in enumerate(c)) == s
    counts["theorem 4 (Kempner's digits), primes p < 50 and k <= 400"] = t4

    # theorem 5
    def falling(n, j):
        return tuple((factorial(i) // factorial(i - j) if i >= j else 0) % n for i in range(n))

    t5 = 0
    for n in range(2, 41):
        s = kempner(n)
        low = hnf(n, [mono(n, m) for m in range(s)])
        assert order(low, n) == order(HN[n], n), n
        lower = hnf(n, [mono(n, m) for m in range(s - 1)])
        assert not member(lower, n, falling(n, s - 1)) and member(HN[n], n, falling(n, s - 1))
        t5 += 1
    counts["theorem 5 (degree below s, sharp), 2 <= n <= 40"] = t5

    # golden-route data
    route = 0
    for j in range(20):
        for m in range(20):
            d = sum((-1) ** (j - i) * comb(j, i) * (factorial(i) // factorial(i - m) if i >= m else 0)
                    for i in range(j + 1))
            assert d == (factorial(j) if m == j else 0)
            route += 1
    for p in [x for x in range(2, 30) if is_prime(x)]:
        for m in range(1, 300):
            v, f = 0, factorial(m)
            while f % p == 0:
                f //= p
                v += 1
            digits_m, x = 0, m
            while x:
                digits_m += x % p
                x //= p
            assert (p - 1) * v == m - digits_m
            route += 1
    for p in (2, 3):                                  # F -> (F mod p, F' mod p) on Z/p^2
        q = p * p
        fib = {}
        for F in POLY[q]:
            key = (tuple(F[i] % p for i in range(p)),
                   tuple(((F[(i + p) % q] - F[i]) // p) % p for i in range(p)))
            fib[key] = fib.get(key, 0) + 1
        assert len(fib) == p ** (2 * p) and len(set(fib.values())) == 1
        route += len(fib)
    counts["golden-route data (falling factorials, Legendre, derivative map on Z/p^2)"] = route

    # witnesses
    w = 0
    absx = [abs(x) for x in range(-3, 4)]            # thm 1, 2: n = 0, Z/0 = Z and F = |x|
    assert absx[:3] != [x for x in range(-3, 0)] and absx[3:] == [0, 1, 2, 3]
    w += 2
    for p in (2, 3, 5, 7):                            # thm 3, k = 1: all p! bijections count
        assert order(HN[p], p) == p ** p              # every function on Z/p is polynomial
        N = factorial(p)
        assert N * p ** (2 * p) != factorial(p) * (p - 1) ** p * kempner_count(p)
    assert 1 * 1 != 1 * 0 ** 1 * 1                    # p = 1: one bijection, right side 0
    N16 = sum(1 for F in POLY[16] if len(set(F)) == 16)
    assert N16 * 4 ** 8 != factorial(4) * 3 ** 4 * kempner_count(16)
    w += 2

    def reps(p, k, s):                                # admissible digit vectors giving (k, s)
        out = []
        for t in range(0, 5):
            for c in product(range(p + 1), repeat=t + 1):
                if not admissible(p, list(c)):
                    continue
                a = [(p ** (i + 1) - 1) // (p - 1) if p > 1 else 0 for i in range(t + 1)]
                if sum(x * y for x, y in zip(c, a)) == k and \
                        sum(ci * p ** (i + 1) for i, ci in enumerate(c)) == s:
                    out.append(c)
        return out
    assert reps(2, 0, 0) == []                        # thm 4, k = 0 (s = 0)
    assert kempner(16) == 6 and reps(4, 2, 6) == []   # p = 4 (not prime), k = 2
    assert reps(2, 2, 2) == []                        # s = 2 is too small for k = 2 (4 | 2!)
    assert reps(2, 2, 6) == []                        # s = 6 is not the least for k = 2
    w += 4
    assert kempner(1) == 0                            # thm 5, n = 1: degree < 0 is impossible
    low3 = span(4, [mono(4, m) for m in range(3)])    # n = 4, s = 3: x(x-1)(x-2) needs degree 3
    assert falling(4, 3) not in low3
    low4 = span(4, [mono(4, m) for m in range(4)])    # n = 4, s = 5: everything has degree < 4
    assert low4 == POLY[4]
    w += 3
    counts["witnesses for the 11 hypotheses (each one false when dropped)"] = w
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


RULES = """Rules. You may add helper definitions and lemmas, in this file or in other project files that it imports, and you may use any proof that the Lean kernel checks. Keep `import Mathlib`, the namespace `@NS@`, @KEEP@ unchanged. Do not use `sorry`, `admit`, `native_decide`, new axioms or any other way to bypass the kernel. For each of the @COUNT@ theorems, `#print axioms` must report only `propext`, `Classical.choice` and `Quot.sound`. Use Lean toolchain `@TOOLCHAIN@` and Mathlib commit `@COMMIT@`. Check the project with `lake build`, which must finish without errors.
"""

# ---- Humanize_AI check (HUMANIZE_AI_CHECKLIST.md, humanize_scan.py): must pass before writing ----
HUMANIZE_ALLOW = []   # exact excerpts allowed after a manual review, each with a reason in a comment


def humanize_findings(text: str):
    """Mechanical part of the line check on the prose of `text` (code and $...$ math skipped).
    Returns (errors, warnings). Errors are hard bans. Warnings need a manual decision."""
    import re as _re
    ai_words = ["delve", "tapestry", "landscape", "realm", "robust", "seamless", "cutting-edge",
                "game-changer", "pivotal", "crucial", "crucially", "unlock", "unleash", "elevate",
                "empower", "harness", "leverage", "synergy", "holistic", "ecosystem", "journey",
                "transformative", "paradigm", "spearhead", "bolster", "underscore", "testament",
                "ever-evolving", "it is worth noting", "plays a key role", "next-generation",
                "broad-based", "best-in-class", "key insight", "remarkably", "notably",
                "intricate", "meticulous", "showcase", "plethora", "myriad"]
    handwave = ["clearly", "obviously", "trivially", "it is easy to see", "it is clear that",
                "straightforward", "of course", "needless to say"]
    filler = ["note that", "moreover,", "furthermore,", "additionally,", "in conclusion,",
              "importantly,", "interestingly,", "in summary,", "let us", "it should be noted"]
    exceptions = {"even", "open", "seven", "eleven", "often", "ten", "then", "when", "own",
                  "between", "need", "seed", "indeed", "hundred"}
    passive = _re.compile(r"\b(is|are|was|were|be|been|being)\s+(?:\w+ly\s+)?(\w+ed|\w+en|"
                          r"built|made|done|shown|set|put|kept|known|seen|proved|found|left|held|"
                          r"met|sent|told|run|cut|read|split)\b", _re.IGNORECASE)
    errors, warnings = [], []
    fence = False
    for n, line in enumerate(text.split("\n"), 1):
        if line.strip().startswith("```"):
            fence = not fence
            continue
        if fence or not line.strip():
            continue
        line = _re.sub(r"`[^`]*`", " CODE ", line)
        line = _re.sub(r"\$[^$]*\$", " MATH ", line)
        low = line.lower()
        hits_e, hits_w = [], []
        for ch, name in (("\u2014", "em dash"), ("\u2013", "en dash"), (";", "semicolon"),
                         ("|", "vertical bar"), ("\u2192", "arrow"), ("\u2022", "in-line dot"),
                         ("\u00b7", "in-line dot")):
            if ch in line:
                hits_e.append(name)
        if _re.search(r"(?<![-<])(-{1,2}>|=>)", line):
            hits_e.append("arrow")
        if _re.search(r"[A-Za-z]\s+-\s+[A-Za-z]", line):
            hits_e.append("spaced hyphen pause")
        for pat in (r"\bnot just\b", r"\brather than\b", r"\bisn't just\b",
                    r",\s+not\s+(?:a|an|the|only|just|merely)\b", r"\bnot only\b"):
            if _re.search(pat, low):
                hits_e.append("contrast frame")
        if "e.g." in low and "etc." in low:
            hits_e.append("e.g. with etc.")
        for s in _re.split(r"(?<=[.!?])\s+", line):
            if _re.sub(r"^\s*(?:[-*]|\d+\.)\s+", "", s).count(":") > 1:
                hits_e.append("colon chain")
        for w in ai_words + handwave:
            if _re.search(r"(?<![\w-])" + _re.escape(w) + r"(?![\w-])", low):
                hits_e.append("word '%s'" % w)
        for w in filler:
            if _re.search(r"(?<![\w-])" + _re.escape(w) + r"(?![\w-])", low):
                hits_w.append("filler '%s'" % w)
        for m in passive.finditer(line):
            if m.group(2).lower() not in exceptions:
                hits_w.append("passive '%s'" % m.group(0))
        for m in _re.finditer(r"\b([A-Za-z]{2,})/([A-Za-z]{2,})\b", line):
            hits_w.append("slash '%s'" % m.group(0))
        if any(a in line for a in HUMANIZE_ALLOW):
            continue
        errors += [(n, h) for h in hits_e]
        warnings += [(n, h) for h in hits_w]
    return errors, warnings


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
    h_err, h_warn = humanize_findings(prompt_text())
    assert not h_err and not h_warn, "Humanize_AI check failed: %r %r" % (h_err, h_warn)
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
    print("  Humanize_AI check of the prompt prose: 0 errors, 0 warnings")
    for rel, text in files.items():
        print(f"  wrote {rel}: {len(text)} chars, ASCII ok")


if __name__ == "__main__":
    main()

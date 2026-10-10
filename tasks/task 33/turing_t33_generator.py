#!/usr/bin/env python3
"""Project Turing, task 33 generator (proof writing): arithmetic of F_q[X], namely quadratic
reciprocity for polynomials (Dedekind 1857, Kuehne 1902, Artin 1924), its supplements for X - c
and for constants, Gauss's count of monic irreducible polynomials, and Carlitz's product of all
monic polynomials of degree d (Carlitz 1935).

F_q is a finite field with q elements; "A is a square mod Q" means A = B^2 mod Q for some B.
Theorems:
  1. q odd, P != Q monic irreducible: (P square mod Q <-> Q square mod P) iff
     q = 1 mod 4 or deg P even or deg Q even
  2. Q monic irreducible, c in F_q: X - c is a square mod Q iff (-1)^deg Q * Q(c) is a square
  3. Q irreducible, c in F_q: c is a square mod Q iff c is a square in F_q or deg Q is even
  4. n * N_n = sum_{d | n} mu(d) q^(n/d), N_n = number of monic irreducibles of degree n
  5. the product of all monic polynomials of degree d is prod_{i < d} (X^(q^d) - X^(q^i))

Writes, next to this script:
  task33_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact arithmetic in F_q[X] (tables for F_q, q = 2, 3, 4, 5, 7, 8, 9, 11, 13):
  - theorem 1 for every pair of distinct monic irreducible polynomials of degree <= 4 (q = 3),
    <= 3 (q = 5, 7), <= 2 (q = 9, 11, 13);
  - theorems 2 and 3 for every monic irreducible Q of degree <= 6 (q = 2), <= 4 (q = 3, 4),
    <= 3 (q = 5, 7, 8, 9), <= 2 (q = 11, 13), every c, and every nonzero multiple of Q in theorem 3;
  - theorem 4 for n <= 8 (q = 2), <= 5 (q = 3, 4), <= 4 (q = 5), <= 3 (q = 7, 8, 9), <= 2 (q = 11, 13);
  - theorem 5 for d <= 4 (q = 2), <= 3 (q = 3, 4), <= 2 (q = 5, 7, 8, 9);
  - the data of the planned golden route: for monic irreducible Q of degree e and A != 0 mod Q,
    A^((q^e - 1)/(q - 1)) mod Q is the constant Res(Q, A), A is a square mod Q iff Res(Q, A)
    is a square in F_q, Res(P, Q) = (-1)^(deg P deg Q) Res(Q, P), Res(Q, X - c) = (-1)^e Q(c);
    X^(q^n) - X is the product of the monic irreducibles of degree dividing n; the multiplicity
    of each monic irreducible P of degree k in the product of theorem 5 is
    sum_{j >= 1, j k <= d} q^(d - j k);
  - a numeric witness for every hypothesis: dropping it makes the statement false.
There is no finite search space: the field and the degrees are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t33_generator.py
"""

TASK = 33
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

THEOREMS = [
    ("isSquare_mod_iff_isSquare_mod_iff",
     "(K : Type*) [Field K] [Fintype K]\n"
     "    (hK : Fintype.card K % 2 = 1) (P Q : Polynomial K) (hP : P.Monic) (hQ : Q.Monic)\n"
     "    (hP' : Irreducible P) (hQ' : Irreducible Q) (hPQ : Not (P = Q))",
     "    ((exists A : Polynomial K, (A ^ 2 - P) % Q = 0) <->\n"
     "        (exists B : Polynomial K, (B ^ 2 - Q) % P = 0)) <->\n"
     "      (Fintype.card K % 4 = 1 \\/ P.natDegree % 2 = 0 \\/ Q.natDegree % 2 = 0)"),
    ("isSquare_X_sub_C_mod_iff",
     "(K : Type*) [Field K] [Fintype K] (Q : Polynomial K)\n"
     "    (hQ : Q.Monic) (hQ' : Irreducible Q) (c : K)",
     "    (exists A : Polynomial K, (A ^ 2 - (Polynomial.X - Polynomial.C c)) % Q = 0) <->\n"
     "      IsSquare ((-1) ^ Q.natDegree * Q.eval c)"),
    ("isSquare_C_mod_iff",
     "(K : Type*) [Field K] [Fintype K] (Q : Polynomial K)\n"
     "    (hQ' : Irreducible Q) (c : K)",
     "    (exists A : Polynomial K, (A ^ 2 - Polynomial.C c) % Q = 0) <->\n"
     "      (IsSquare c \\/ Q.natDegree % 2 = 0)"),
    ("card_monic_irreducible",
     "(K : Type*) [Field K] [Fintype K] (n : Nat)",
     "    ((n * Nat.card {P : Polynomial K // P.Monic /\\ Irreducible P /\\ P.natDegree = n} : Nat) :\n"
     "        Int) =\n"
     "      Finset.sum (Nat.divisors n)\n"
     "        (fun d => ArithmeticFunction.moebius d * (Fintype.card K : Int) ^ (n / d))"),
    ("prod_monic_eq_prod_X_pow_sub_X_pow",
     "(K : Type*) [Field K] [Fintype K] (d : Nat)",
     "    Finset.prod Finset.univ (fun c : Fin d -> K =>\n"
     "        Polynomial.X ^ d +\n"
     "          Finset.sum Finset.univ (fun i : Fin d => Polynomial.C (c i) * Polynomial.X ^ (i : Nat))) =\n"
     "      Finset.prod (Finset.range d)\n"
     "        (fun i => Polynomial.X ^ (Fintype.card K ^ d) - Polynomial.X ^ (Fintype.card K ^ i))"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. Let $\mathbb{F}_q$ be a finite field with $q$ elements. For $A, Q \in \mathbb{F}_q[X]$ with $Q \ne 0$, say that $A$ is a square modulo $Q$ if $A \equiv B^2 \pmod Q$ for some $B \in \mathbb{F}_q[X]$. Below $\deg$ is the degree and $\mu$ is the Moebius function.

1. (Quadratic reciprocity.) Let $q$ be odd and let $P \ne Q$ be monic irreducible polynomials in $\mathbb{F}_q[X]$. The statements "$P$ is a square modulo $Q$" and "$Q$ is a square modulo $P$" are equivalent if and only if $q \equiv 1 \pmod 4$ or $\deg P$ is even or $\deg Q$ is even.
2. Let $Q$ be monic irreducible and $c \in \mathbb{F}_q$. Then $X - c$ is a square modulo $Q$ if and only if $(-1)^{\deg Q} Q(c)$ is a square in $\mathbb{F}_q$.
3. Let $Q$ be irreducible and $c \in \mathbb{F}_q$. Then the constant polynomial $c$ is a square modulo $Q$ if and only if $c$ is a square in $\mathbb{F}_q$ or $\deg Q$ is even.
4. (Gauss.) For every $n \ge 0$ the number $N_n$ of monic irreducible polynomials of degree $n$ in $\mathbb{F}_q[X]$ satisfies $n N_n = \sum_{d \mid n} \mu(d)\, q^{n/d}$.
5. (Carlitz.) For every $d \ge 0$ the product of all $q^d$ monic polynomials of degree $d$ in $\mathbb{F}_q[X]$ equals $\prod_{i=0}^{d-1} \big( X^{q^d} - X^{q^i} \big)$.

Lean statement. A finite field is a type `K` with `[Field K] [Fintype K]`, so $q$ is `Fintype.card K`, and $\mathbb{F}_q[X]$ is `Polynomial K`. The condition "$A$ is a square modulo $Q$" is `exists B : Polynomial K, (B ^ 2 - A) % Q = 0`, where `%` is the remainder of polynomial division, and $Q(c)$ is `Q.eval c`. In theorem 4, $N_n$ is the `Nat.card` of a subtype, $\mu$ is `ArithmeticFunction.moebius` and the sum runs over `Nat.divisors n` (for $n = 0$ both sides are $0$). In theorem 5 the monic polynomials of degree $d$ are $X^d + \sum_{i < d} c_i X^i$ for the functions `c : Fin d -> K`. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    import itertools
    from math import gcd
    import numpy as np

    counts = {}

    def gf(p, k):
        """Addition, multiplication and negation tables of F_(p^k); the element e stands for
        the polynomial sum_i digit_i(e) t^i modulo a monic irreducible of degree k."""
        q = p ** k
        digits = [[(e // p ** i) % p for i in range(k)] for e in range(q)]

        def to_int(c):
            return sum(int(c[i]) * p ** i for i in range(k))

        def divides(g, f):
            r = list(f)
            d = len(g) - 1
            for s in range(len(r) - 1, d - 1, -1):
                c = r[s]
                if c:
                    for i in range(d + 1):
                        r[s - d + i] = (r[s - d + i] - c * g[i]) % p
            return all(v == 0 for v in r[:d])

        mod = None
        if k > 1:
            for cs in itertools.product(range(p), repeat=k):
                f = list(cs) + [1]
                if not any(divides(list(g) + [1], f) for d in range(1, k // 2 + 1)
                           for g in itertools.product(range(p), repeat=d)):
                    mod = f
                    break

        def mul(a, b):
            res = [0] * (2 * k - 1)
            for i, x in enumerate(a):
                for j, y in enumerate(b):
                    res[i + j] = (res[i + j] + x * y) % p
            for d in range(2 * k - 2, k - 1, -1):
                c = res[d]
                if c:
                    for i in range(k + 1):
                        res[d - k + i] = (res[d - k + i] - c * mod[i]) % p
            return res[:k]

        AT = np.zeros((q, q), dtype=np.int64)
        MT = np.zeros((q, q), dtype=np.int64)
        for x in range(q):
            for y in range(q):
                AT[x, y] = to_int([(digits[x][i] + digits[y][i]) % p for i in range(k)])
                MT[x, y] = (x * y) % p if k == 1 else to_int(mul(digits[x], digits[y]))
        NEG = np.array([to_int([(-c) % p for c in digits[x]]) for x in range(q)], dtype=np.int64)
        assert (MT[1] == np.arange(q)).all() and len(set(MT[1:, 1:].ravel().tolist()) - {0}) == q - 1
        for x in range(1, q):                     # field check: no zero divisors
            assert (MT[x, 1:] != 0).all()
        return q, AT, MT, NEG

    class Fq:
        """F_q with polynomial arithmetic; a polynomial is a tuple of coefficients, constant
        term first, without trailing zeros."""

        def __init__(self, p, k):
            self.q, AT, MT, NEG = gf(p, k)
            self.AT, self.MT, self.NEG = AT.tolist(), MT.tolist(), NEG.tolist()
            q = self.q
            self.INV = [0] + [next(v for v in range(1, q) if self.MT[u][v] == 1)
                              for u in range(1, q)]
            self.SQ = {self.MT[t][t] for t in range(q)}

        def norm(self, a):
            a = list(a)
            while a and a[-1] == 0:
                a.pop()
            return tuple(a)

        def add(self, a, b):
            n = max(len(a), len(b))
            return self.norm([self.AT[a[i] if i < len(a) else 0][b[i] if i < len(b) else 0]
                              for i in range(n)])

        def neg(self, a):
            return tuple(self.NEG[x] for x in a)

        def sub(self, a, b):
            return self.add(a, self.neg(b))

        def mul(self, a, b):
            if not a or not b:
                return ()
            r = [0] * (len(a) + len(b) - 1)
            for i, x in enumerate(a):
                if x:
                    row = self.MT[x]
                    for j, y in enumerate(b):
                        if y:
                            r[i + j] = self.AT[r[i + j]][row[y]]
            return self.norm(r)

        def scal(self, c, a):
            return self.norm([self.MT[c][x] for x in a])

        def mod(self, a, b):
            a = list(a)
            db = len(b) - 1
            li = self.INV[b[-1]]
            while a and len(a) - 1 >= db:
                c = self.MT[a[-1]][li]
                sh = len(a) - 1 - db
                for i, y in enumerate(b):
                    a[sh + i] = self.AT[a[sh + i]][self.NEG[self.MT[c][y]]]
                a = list(self.norm(a))
            return tuple(a)

        def powmod(self, a, e, m):
            r, b = (1,), self.mod(a, m)
            while e:
                if e & 1:
                    r = self.mod(self.mul(r, b), m)
                b = self.mod(self.mul(b, b), m)
                e >>= 1
            return r

        def ev(self, a, c):
            v = 0
            for co in reversed(a):
                v = self.AT[self.MT[v][c]][co]
            return v

        def monics(self, d):
            for cs in itertools.product(range(self.q), repeat=d):
                yield tuple(cs) + (1,)

        def irreducible(self, f):
            d = len(f) - 1
            return d >= 1 and all(self.mod(f, g) != () for e in range(1, d // 2 + 1)
                                  for g in self.monics(e))

        def squares_mod(self, Q):
            e = len(Q) - 1
            return {self.mod(self.mul(A, A), Q) for A in
                    (self.norm(cs) for cs in itertools.product(range(self.q), repeat=e))}

        def is_sq_mod(self, A, Q, cache):
            if Q not in cache:
                cache[Q] = self.squares_mod(Q)
            return self.mod(A, Q) in cache[Q]

        def res(self, f, g):
            """lc(f)^deg g * prod over the roots of f of g."""
            if not g:
                return 0
            if len(f) == 1:
                return self.pw(f[0], len(g) - 1)
            if len(g) == 1:
                return self.pw(g[0], len(f) - 1)
            r = self.mod(g, f)
            if not r:
                return 0
            return self.MT[self.pw(f[-1], len(g) - len(r))][self.res_swap(f, r)]

        def res_swap(self, f, r):
            # res(f, r) = (-1)^(deg f deg r) res(r, f)
            s = self.res(r, f)
            return self.NEG[s] if ((len(f) - 1) * (len(r) - 1)) % 2 else s

        def pw(self, c, e):
            v = 1
            for _ in range(e):
                v = self.MT[v][c]
            return v

    def mobius(n):
        m, r, d = n, 1, 2
        while d * d <= m:
            if m % d == 0:
                m //= d
                if m % d == 0:
                    return 0
                r = -r
            d += 1
        return -r if m > 1 else r

    plan = {(2, 1): (6, 0, 8, 4), (3, 1): (4, 4, 5, 3), (2, 2): (4, 0, 5, 3),
            (5, 1): (3, 3, 4, 2), (7, 1): (3, 3, 3, 2), (2, 3): (3, 0, 3, 2),
            (3, 2): (3, 2, 3, 2), (11, 1): (2, 2, 2, 0), (13, 1): (2, 2, 2, 0)}
    t1 = t2 = t3 = t4 = t5 = route = 0
    fields = {}
    for (p, k), (D23, D1, D4, D5) in plan.items():
        f = Fq(p, k)
        q = f.q
        fields[q] = f
        cache = {}
        irr = {d: [g for g in f.monics(d) if f.irreducible(g)] for d in range(1, max(D23, D1, D4) + 1)}
        for n in range(0, D4 + 1):                                               # theorem 4
            lhs = n * len(irr[n]) if n else 0
            rhs = sum(mobius(d) * q ** (n // d) for d in range(1, n + 1) if n % d == 0)
            assert lhs == rhs, (q, n)
            t4 += 1
            if n:
                assert sum(d * len(irr[d]) for d in range(1, n + 1) if n % d == 0) == q ** n
                prod = (1,)
                for d in range(1, n + 1):
                    if n % d == 0:
                        for g in irr[d]:
                            prod = f.mul(prod, g)
                assert prod == f.sub((0,) * (q ** n) + (1,), (0, 1))     # X^(q^n) - X
                route += 2
        if q % 2 == 1:                                                           # theorem 1
            pool = [g for d in range(1, D1 + 1) for g in irr[d]]
            for P in pool:
                for Q in pool:
                    if P == Q:
                        continue
                    a = f.is_sq_mod(P, Q, cache)
                    b = f.is_sq_mod(Q, P, cache)
                    rhs = q % 4 == 1 or (len(P) - 1) % 2 == 0 or (len(Q) - 1) % 2 == 0
                    assert (a == b) == rhs, (q, P, Q)
                    t1 += 1
                    rPQ, rQP = f.res(P, Q), f.res(Q, P)
                    sgn = ((len(P) - 1) * (len(Q) - 1)) % 2
                    assert rPQ == (f.NEG[rQP] if sgn else rQP) and rPQ != 0
                    assert a == (rQP in f.SQ) and b == (rPQ in f.SQ)
                    route += 1
        X = (0, 1)
        for d in range(1, D23 + 1):                                              # theorems 2, 3
            for Q in irr[d]:
                e = len(Q) - 1
                for c in range(q):
                    lhs = f.is_sq_mod(f.sub(X, (c,) if c else ()), Q, cache)
                    val = f.MT[1 if e % 2 == 0 else f.NEG[1]][f.ev(Q, c)]
                    assert lhs == (val in f.SQ), (q, Q, c)
                    assert f.res(Q, f.sub(X, (c,) if c else ())) == val
                    t2 += 1
                    for u in range(1, q):                     # every nonzero multiple of Q
                        lhs3 = f.is_sq_mod((c,) if c else (), f.scal(u, Q), cache)
                        assert lhs3 == (c in f.SQ or e % 2 == 0), (q, Q, c, u)
                        t3 += 1
                    route += 1
                # norm data: A^((q^e - 1)/(q - 1)) mod Q is the constant Res(Q, A)
                for A in itertools.islice(itertools.product(range(q), repeat=e), 0, 400):
                    A = f.norm(A)
                    if not A:
                        continue
                    nA = f.powmod(A, (q ** e - 1) // (q - 1), Q)
                    assert len(nA) == 1 and nA[0] == f.res(Q, A)
                    assert f.is_sq_mod(A, Q, cache) == (nA[0] in f.SQ)
                    route += 1
        for d in range(0, D5 + 1):                                               # theorem 5
            L = (1,)
            for A in f.monics(d):
                L = f.mul(L, A)
            R = (1,)
            for i in range(d):
                R = f.mul(R, f.sub((0,) * (q ** d) + (1,), (0,) * (q ** i) + (1,)))
            assert L == R, (q, d)
            t5 += 1
            for kk in range(1, d + 1):                  # multiplicity of each irreducible
                for P in irr.get(kk, [])[:6]:
                    v, T = 0, L
                    while True:
                        r = f.mod(T, P)
                        if r:
                            break
                        v += 1
                        # divide T by P exactly
                        quo, rem = [], list(T)
                        dq = len(P) - 1
                        out = [0] * (len(rem) - dq)
                        while len(rem) - 1 >= dq and any(rem):
                            cc = f.MT[rem[-1]][f.INV[P[-1]]]
                            sh = len(rem) - 1 - dq
                            out[sh] = cc
                            for i, y in enumerate(P):
                                rem[sh + i] = f.AT[rem[sh + i]][f.NEG[f.MT[cc][y]]]
                            rem = list(f.norm(rem))
                        T = f.norm(out)
                    assert v == sum(q ** (d - j * kk) for j in range(1, d // kk + 1)), (q, d, P)
                    route += 1
    counts["theorem 1 (reciprocity), ordered pairs of distinct monic irreducibles"] = t1
    counts["theorem 2 (X - c), pairs (Q, c)"] = t2
    counts["theorem 3 (constants), triples (Q times a unit, c)"] = t3
    counts["theorem 4 (Gauss), pairs (q, n)"] = t4
    counts["theorem 5 (Carlitz), pairs (q, d)"] = t5
    counts["golden-route data (resultants and norms, X^(q^n) - X, multiplicities)"] = route

    # witnesses
    w = 0
    F3, F2 = fields[3], fields[2]
    c3 = {}
    sq = lambda f, A, Q: f.is_sq_mod(A, Q, {})
    X = (0, 1)
    # theorem 1: q = 2, P = X, Q = X + 1: both sides squares, right side false
    assert sq(F2, X, (1, 1)) and sq(F2, (1, 1), X) and not (2 % 4 == 1)
    # P = 2X (not monic), Q = X + 1 over F_3; and the mirror image
    assert sq(F3, (0, 2), (1, 1)) == sq(F3, (1, 1), (0, 2)) and not (3 % 4 == 1)
    assert sq(F3, (1, 1), (0, 2)) == sq(F3, (0, 2), (1, 1))
    # P = X^2 (reducible), Q = X + 2 over F_3; and the mirror image
    assert sq(F3, (0, 0, 1), (2, 1)) != sq(F3, (2, 1), (0, 0, 1))
    # P = Q = X over F_3
    assert sq(F3, X, X) == sq(F3, X, X) and not (3 % 4 == 1 or 1 % 2 == 0)
    w += 6
    # theorem 2: Q = 2X (not monic), c = 1; Q = X^2 (reducible), c = 1; both over F_3
    assert not sq(F3, (2, 1), (0, 2)) and F3.MT[F3.NEG[1]][F3.ev((0, 2), 1)] in F3.SQ
    assert not sq(F3, (2, 1), (0, 0, 1)) and F3.ev((0, 0, 1), 1) in F3.SQ
    w += 2
    # theorem 3: Q = X^2 (reducible), c = 2 over F_3
    assert not sq(F3, (2,), (0, 0, 1)) and 2 % 2 == 0
    w += 1
    counts["witnesses for the 9 hypotheses (each one false when dropped)"] = w
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

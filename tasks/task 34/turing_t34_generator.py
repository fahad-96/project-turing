#!/usr/bin/env python3
"""Project Turing, task 34 generator (proof writing): vanishing sums of roots of unity and the
orders of integer matrices (Redei 1959, de Bruijn 1953, Schoenberg 1964, Mann 1965, Lam and
Leung 2000; the crystallographic restriction in dimension 6).

z is a primitive m-th root of unity in C; a rotated p-gon (p a prime factor of m) is a set
{s, s + m/p, ..., s + (p - 1) m/p} of residues mod m. Theorems:
  1. m >= 1: a sum of n m-th roots of unity (repetitions allowed) can vanish iff n is a
     nonnegative integer combination of the prime factors of m (Lam and Leung)
  2. sum_{k < m} a_k z^k = 0 (a_k integers) iff k -> a_k is an integer combination of
     indicator functions of rotated p-gons (Redei, de Bruijn, Schoenberg)
  3. if m has at most two prime factors and a_k >= 0, the combination can be taken with
     nonnegative coefficients (de Bruijn); false for m = 30
  4. a vanishing integer combination of roots of unity with no vanishing proper subsum has
     (z_i / z_j)^(product of the primes <= k) = 1 (Mann)
  5. the orders of 6 x 6 integer matrices are exactly 0 (infinite), 1-10, 12, 14, 15, 18, 20,
     24, 30

Writes, next to this script:
  task34_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic. A sum sum_k a_k z^k vanishes iff the
cyclotomic polynomial Phi_m divides sum_k a_k x^k, so everything is computed with the integer
vectors x^k mod Phi_m (Phi_m by exact division of x^m - 1, m <= 60):
  - theorem 2 for every 1 <= m <= 60: the rotated polygons lie in the lattice of vanishing
    vectors, their span has rank m - phi(m) and all its elementary divisors equal 1 (Smith
    normal form), so it is the whole lattice;
  - theorems 1 and 3 by exhaustive search over all multisets of exponents up to a size bound
    (m = 6, 10, 12, 14, 15, 18, 20, 21, 22): every vanishing multiset is a nonnegative union
    of rotated polygons, and the sizes that occur are exactly the combinations of the primes
    (this covers every non-representable size for m = 6, 10, 12, 14, 15, 18, 20, 22);
  - theorem 4 for the minimal vanishing relations supported on sets of at most 5 (m <= 30)
    or 6 (m <= 15) residues containing 0 (generic kernel vectors, fixed seed);
  - theorem 5: the products of cyclotomic polynomials of total degree <= 6 give exactly the
    listed orders, and an explicit 6 x 6 integer matrix of each order is built and its order
    computed;
  - a numeric witness for every hypothesis: dropping it makes the statement false (m = 30 for
    the two-prime condition, z = (-1 + sqrt(-7))/4 for m >= 1, and others).
There is no finite search space: m, n, k and the coefficients are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t34_generator.py
"""

TASK = 34
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

THEOREMS = [
    ("exists_sum_pow_eq_zero_iff",
     "(m n : Nat) (hm : 0 < m) (z : Complex)\n    (hz : IsPrimitiveRoot z m)",
     "    (exists e : Fin n -> Nat, Finset.sum Finset.univ (fun i => z ^ e i) = 0) <->\n"
     "      exists c : Nat -> Nat, n = Finset.sum m.primeFactors (fun p => c p * p)"),
    ("sum_mul_pow_eq_zero_iff",
     "(m : Nat) (z : Complex) (hz : IsPrimitiveRoot z m)\n    (a : Nat -> Int)",
     "    Finset.sum (Finset.range m) (fun k => (a k : Complex) * z ^ k) = 0 <->\n"
     "      exists b : Nat -> Nat -> Int, forall k, k < m ->\n"
     "        a k = Finset.sum m.primeFactors\n"
     "          (fun p => Finset.sum (Finset.range p) (fun j => b p ((k + j * (m / p)) % m)))"),
    ("exists_nonneg_of_sum_mul_pow_eq_zero",
     "(m : Nat) (hm : m.primeFactors.card <= 2)\n"
     "    (z : Complex) (hz : IsPrimitiveRoot z m) (a : Nat -> Nat)\n"
     "    (ha : Finset.sum (Finset.range m) (fun k => (a k : Complex) * z ^ k) = 0)",
     "    exists b : Nat -> Nat -> Nat, forall k, k < m ->\n"
     "      a k = Finset.sum m.primeFactors\n"
     "        (fun p => Finset.sum (Finset.range p) (fun j => b p ((k + j * (m / p)) % m)))"),
    ("div_pow_primorial_eq_one",
     "(k : Nat) (a : Fin k -> Int) (z : Fin k -> Complex)\n"
     "    (hz : forall i, exists n, 0 < n /\\ z i ^ n = 1)\n"
     "    (hsum : Finset.sum Finset.univ (fun i => (a i : Complex) * z i) = 0)\n"
     "    (hmin : forall S : Finset (Fin k),\n"
     "      Finset.sum S (fun i => (a i : Complex) * z i) = 0 -> S.card = 0 \\/ S.card = k)",
     "    forall i j, (z i / z j) ^ primorial k = 1"),
    ("exists_orderOf_eq_iff",
     "(n : Nat)",
     "    (exists A : Matrix (Fin 6) (Fin 6) Int, orderOf A = n) <->\n"
     "      Membership.mem\n"
     "        ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} : Finset Nat) n"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. Below $m, n, k \ge 0$ are integers and $z$ is a primitive $m$-th root of unity in $\mathbb{C}$. For a prime $p \mid m$, a rotated $p$-gon is a set of residues modulo $m$ of the form $\{s, s + m/p, s + 2m/p, \dots, s + (p - 1)m/p\}$. For every rotated $p$-gon $P$ the sum $\sum_{k \in P} z^k$ vanishes.

1. (Lam and Leung.) Let $m \ge 1$ have the prime factors $p_1, \dots, p_r$. There are $m$-th roots of unity $\zeta_1, \dots, \zeta_n$, repetitions allowed, with $\zeta_1 + \dots + \zeta_n = 0$ if and only if $n = c_1 p_1 + \dots + c_r p_r$ for some integers $c_1, \dots, c_r \ge 0$.
2. (Redei, de Bruijn, Schoenberg.) For integers $a_0, \dots, a_{m-1}$, the sum $\sum_{k < m} a_k z^k$ vanishes if and only if the function $k \mapsto a_k$ on the residues modulo $m$ is an integer combination of indicator functions of rotated $p$-gons with $p \mid m$.
3. (de Bruijn.) Suppose that $m$ has at most two distinct prime factors. If $a_0, \dots, a_{m-1} \ge 0$ are integers with $\sum_{k < m} a_k z^k = 0$, then $k \mapsto a_k$ is a combination of indicator functions of rotated $p$-gons with nonnegative integer coefficients.
4. (Mann.) Let $\zeta_1, \dots, \zeta_k$ be roots of unity and $a_1, \dots, a_k$ integers with $\sum_i a_i \zeta_i = 0$, such that no proper nonempty subsum $\sum_{i \in S} a_i \zeta_i$ vanishes. Then $(\zeta_i / \zeta_j)^N = 1$ for all $i, j$, where $N$ is the product of the primes $p \le k$.
5. The orders of the $6 \times 6$ integer matrices of finite order are exactly $1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30$.

Lean statement. A primitive root is `IsPrimitiveRoot z m` with `z : Complex`, and the prime factors of $m$ form `m.primeFactors`. In theorem 1 the roots are `z ^ e i` for a function `e : Fin n -> Nat`. In theorems 2 and 3 the coefficients `b p s` describe a combination of rotated $p$-gons through $a_k = \sum_{p \mid m} \sum_{j < p} b_p\big((k + j m/p) \bmod m\big)$, where the coefficient of a polygon is the sum of the values `b p s` over its elements $s$. In theorem 4 the product of the primes $p \le k$ is `primorial k`, and the condition on subsums says that a vanishing subsum uses no index or every index. In theorem 5, `orderOf A` is the order of `A` in the monoid of integer matrices, which is $0$ when no positive power of `A` is the identity, so the value $0$ appears in the set. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    import itertools
    import random
    from fractions import Fraction
    from math import gcd

    counts = {}

    def is_prime(n):
        return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))

    def primes_of(m):
        return [p for p in range(2, m + 1) if m % p == 0 and is_prime(p)]

    cyc = {}

    def Phi(n):
        """Integer coefficients of the n-th cyclotomic polynomial, constant term first."""
        if n not in cyc:
            num = [-1] + [0] * (n - 1) + [1]
            for d in range(1, n):
                if n % d == 0:
                    b = Phi(d)
                    out = [0] * (len(num) - len(b) + 1)
                    for s in range(len(num) - len(b), -1, -1):
                        c = num[s + len(b) - 1] // b[-1]
                        out[s] = c
                        for i, y in enumerate(b):
                            num[s + i] -= c * y
                    assert not any(num)
                    num = out
            cyc[n] = num
        return cyc[n]

    def red(m):
        """x^k mod Phi_m as integer vectors of length phi(m), for 0 <= k < m."""
        f = Phi(m)
        deg = len(f) - 1
        out = []
        for k in range(m):
            a = [0] * k + [1]
            for s in range(len(a) - 1, deg - 1, -1):
                c = a[s]
                if c:
                    for i, y in enumerate(f):
                        a[s - deg + i] -= c * y
            a = a[:deg] + [0] * max(0, deg - len(a))
            out.append(tuple(a[:deg]))
        return out

    def polygons(m):
        return [tuple(sorted((s + j * (m // p)) % m for j in range(p)))
                for p in primes_of(m) for s in range(m // p)]

    # Phi_n against the product formula prod_{d | n} (x^d - 1)^mu(n/d), checked at x = 2, 3
    def mobius(n):
        r, d, mm = 1, 2, n
        while d * d <= mm:
            if mm % d == 0:
                mm //= d
                if mm % d == 0:
                    return 0
                r = -r
            d += 1
        return -r if mm > 1 else r

    route = 0
    for n in range(1, 61):
        for x in (2, 3):
            val = sum(c * x ** i for i, c in enumerate(Phi(n)))
            num, den = 1, 1
            for d in range(1, n + 1):
                if n % d == 0:
                    e = mobius(n // d)
                    if e == 1:
                        num *= x ** d - 1
                    elif e == -1:
                        den *= x ** d - 1
            assert val * den == num
            route += 1

    # theorem 2: the rotated polygons span the lattice of vanishing vectors, 1 <= m <= 60
    def lattice_index(rows, d):
        rows = [list(r) for r in rows if any(r)]
        idx = 1
        for col in range(d):
            while True:
                nz = [r for r in rows if r[col] != 0]
                if not nz:
                    return 0
                if len(nz) == 1:
                    break
                nz.sort(key=lambda r: abs(r[col]))
                piv = nz[0]
                for r in nz[1:]:
                    q = r[col] // piv[col]
                    for t in range(d):
                        r[t] -= q * piv[t]
            piv = next(r for r in rows if r[col] != 0)
            idx *= abs(piv[col])
            rows.remove(piv)
        return idx

    t2 = 0
    for m in range(1, 61):
        R = red(m)
        phi = len(Phi(m)) - 1
        P = polygons(m)
        for poly in P:
            assert all(sum(R[k][i] for k in poly) == 0 for i in range(phi))
            route += 1
        # the vanishing vectors are determined by their coordinates phi, ..., m - 1
        d = m - phi
        rows = []
        for poly in P:
            v = [0] * m
            for k in poly:
                v[k] += 1
            rows.append(v[phi:])
        assert d == 0 or lattice_index(rows, d) == 1, m
        t2 += 1
    counts["theorem 2 (polygons span the vanishing lattice, index 1), m <= 60"] = t2

    # theorems 1 and 3: exhaustive search over multisets of exponents
    def decomposable(cnt, P, memo):
        key = tuple(cnt)
        if key in memo:
            return memo[key]
        if not any(cnt):
            return True
        k0 = next(i for i, c in enumerate(cnt) if c)
        res = False
        for poly in P:
            if k0 in poly and all(cnt[i] >= 1 for i in poly):
                for i in poly:
                    cnt[i] -= 1
                ok = decomposable(cnt, P, memo)
                for i in poly:
                    cnt[i] += 1
                if ok:
                    res = True
                    break
        memo[key] = res
        return res

    def explore(m, N, fix0=False):
        R = red(m)
        phi = len(R[0])
        P = polygons(m)
        sizes, nondec = set(), []
        nvan = [0]
        cnt = [0] * m
        memo = {}

        def dfs(start, depth, vec):
            if depth > 0 and not any(vec):
                nvan[0] += 1
                sizes.add(depth)
                if not decomposable(cnt, P, memo):
                    nondec.append(tuple(i for i in range(m) for _ in range(cnt[i])))
            if depth == N:
                return
            for k in range(start, m):
                cnt[k] += 1
                dfs(k, depth + 1, tuple(a + b for a, b in zip(vec, R[k])))
                cnt[k] -= 1
        if fix0:
            cnt[0] += 1
            dfs(0, 1, R[0])
            cnt[0] -= 1
        else:
            dfs(0, 0, tuple([0] * phi))
        return sizes, nondec, nvan[0]

    t13 = 0
    for (m, N) in [(6, 9), (10, 8), (12, 8), (14, 8), (15, 8), (18, 7), (20, 7), (21, 6),
                   (22, 6)]:
        sizes, nondec, nvan = explore(m, N)
        ps = primes_of(m)
        semi = {n for n in range(1, N + 1)
                if any(n == sum(c * p for c, p in zip(cs, ps))
                       for cs in itertools.product(range(N + 1), repeat=len(ps)))}
        assert sizes == semi and not nondec, m
        t13 += nvan
    counts["theorems 1 and 3 (vanishing multisets found, all nonnegative unions of polygons, "
           "sizes = prime combinations)"] = t13
    sizes30, nondec30, _ = explore(30, 6, fix0=True)
    assert (0, 1, 7, 13, 19, 20) in nondec30 and sizes30 == {2, 3, 4, 5, 6}

    # theorem 4 (Mann): minimal relations on sets containing 0
    def kernel(cols):
        k, r = len(cols), len(cols[0])
        M = [[Fraction(cols[j][i]) for j in range(k)] for i in range(r)]
        piv, row = [], 0
        for c in range(k):
            pr = next((i for i in range(row, r) if M[i][c] != 0), None)
            if pr is None:
                continue
            M[row], M[pr] = M[pr], M[row]
            inv = 1 / M[row][c]
            M[row] = [v * inv for v in M[row]]
            for i in range(r):
                if i != row and M[i][c] != 0:
                    f = M[i][c]
                    M[i] = [x - f * y for x, y in zip(M[i], M[row])]
            piv.append(c)
            row += 1
            if row == r:
                break
        basis = []
        for fc in [c for c in range(k) if c not in piv]:
            v = [Fraction(0)] * k
            v[fc] = Fraction(1)
            for i, pc in enumerate(piv):
                v[pc] = -M[i][fc]
            basis.append(v)
        return basis

    def primorial(k):
        out = 1
        for p in range(2, k + 1):
            if is_prime(p):
                out *= p
        return out

    rng = random.Random(34)
    t4 = 0
    for m in range(2, 31):
        R = red(m)
        phi = len(R[0])
        for k in range(2, 6 if m > 15 else 7):
            N = primorial(k)
            for rest in itertools.combinations(range(1, m), k - 1):
                S = (0,) + rest
                B = kernel([R[e] for e in S])
                if not B:
                    continue
                for _ in range(2):
                    coef = [rng.randint(-50, 50) for _ in B]
                    v = [sum(c * b[i] for c, b in zip(coef, B)) for i in range(k)]
                    if any(x == 0 for x in v):
                        continue
                    if any(all(sum(v[i] * R[S[i]][j] for i in range(k) if mask >> i & 1) == 0
                               for j in range(phi)) for mask in range(1, 2 ** k - 1)):
                        continue
                    assert all((e * N) % m == 0 for e in S), (m, S)
                    t4 += 1
                    break
    counts["theorem 4 (Mann), minimal relations tested (m <= 30)"] = t4

    # theorem 5: orders of 6 x 6 integer matrices
    def totient(n):
        return sum(1 for j in range(1, n + 1) if gcd(j, n) == 1)

    def lcm(a, b):
        return a * b // gcd(a, b)

    small = [d for d in range(1, 40) if totient(d) <= 6]
    orders = set()

    def comb(start, budget, cur):
        orders.add(cur)
        for i in range(start, len(small)):
            d = small[i]
            if totient(d) <= budget:
                comb(i, budget - totient(d), lcm(cur, d))
    comb(0, 6, 1)
    claimed = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30}
    assert orders == claimed and max(small) == 18

    def companion(d):
        f = Phi(d)
        deg = len(f) - 1
        C = [[0] * deg for _ in range(deg)]
        for i in range(1, deg):
            C[i][i - 1] = 1
        for i in range(deg):
            C[i][deg - 1] = -f[i]
        return C

    def blockdiag(blocks, size=6):
        A = [[0] * size for _ in range(size)]
        pos = 0
        for B in blocks:
            for i in range(len(B)):
                for j in range(len(B)):
                    A[pos + i][pos + j] = B[i][j]
            pos += len(B)
        for i in range(pos, size):
            A[i][i] = 1
        return A

    def mul(A, B):
        n = len(A)
        return [[sum(A[i][t] * B[t][j] for t in range(n)) for j in range(n)] for i in range(n)]

    I6 = blockdiag([])
    choice = {1: [], 2: [2], 3: [3], 4: [4], 5: [5], 6: [6], 7: [7], 8: [8], 9: [9],
              10: [10], 12: [12], 14: [14], 15: [3, 5], 18: [18], 20: [4, 5], 24: [3, 8],
              30: [3, 10]}
    t5 = 0
    for n, ds in choice.items():
        assert sum(totient(d) for d in ds) <= 6
        A = blockdiag([companion(d) for d in ds])
        P, order = A, 1
        while P != I6:
            P, order = mul(P, A), order + 1
            assert order <= 30
        assert order == n
        t5 += 1
    J = blockdiag([[[1, 1], [0, 1]]])
    P = J
    for j in range(1, 61):
        assert P != I6 and P[0][1] == j
        P = mul(P, J)
    t5 += 1
    counts["theorem 5 (the order set from cyclotomic degrees <= 6, explicit matrices of every "
           "order, one of infinite order)"] = t5
    counts["golden-route data (Phi_n against the product formula, polygon relations)"] = route

    # witnesses
    w = 0
    # theorem 1, m >= 1: z = (-1 + sqrt(-7))/4 is no root of unity (|z|^2 = 1/2) and
    # 1 + z + 2 z^2 = 0, a vanishing sum of 4 powers; m = 0 has no prime factors
    zr, zi2 = Fraction(-1, 4), Fraction(7, 16)            # z = zr + i y with y^2 = zi2
    sq_r, sq_iy = zr * zr - zi2, 2 * zr                   # z^2 = (zr^2 - y^2) + i (2 zr) y
    assert 1 + zr + 2 * sq_r == 0 and 1 + 2 * sq_iy == 0  # real part, coefficient of i y
    assert zr * zr + zi2 == Fraction(1, 2)
    # theorem 1, hz: z = 1 is no primitive 6th root; 1 + 1 != 0 although 2 = 1 * 2
    assert 1 + 1 != 0 and 2 in {2 * c + 3 * d for c in range(3) for d in range(3)}
    w += 2
    # theorem 2, hz: m = 2, z = 1, a = (1, -1) vanishes, polygons force a(0) = a(1)
    assert 1 * 1 + (-1) * 1 == 0 and 1 != -1
    w += 1
    # theorem 3, hm: m = 30 has three prime factors and the vanishing multiset
    # {0, 1, 7, 13, 19, 20} is no nonnegative union of rotated polygons (found above)
    assert len(primes_of(30)) == 3
    # theorem 3, hz: m = 4, z = -1, a = (1, 1, 0, 0) vanishes, polygons force a(0) = a(2)
    assert 1 * 1 + 1 * (-1) == 0 and 1 != 0
    w += 2
    # theorem 4: z = (1, 2), a = (2, -1) (not roots of unity); a = (1, 1), z = (1, zeta_5)
    # (no vanishing); z = (1, -1, zeta_5, -zeta_5) as 10th roots, a = (1, 1, 1, 1) (a
    # vanishing proper subsum); in each case the conclusion fails
    assert 2 * 1 - 1 * 2 == 0 and Fraction(1, 2) ** 2 != 1
    R5 = red(5)
    assert any(a + b for a, b in zip(R5[0], R5[1])) and (1 * primorial(2)) % 5 != 0
    R10 = red(10)
    assert not any(sum(R10[e][j] for e in (0, 5, 2, 7)) for j in range(4))
    assert not any(R10[0][j] + R10[5][j] for j in range(4)) and (2 * primorial(4)) % 10 != 0
    w += 3
    counts["witnesses for the 8 hypotheses (each one false when dropped)"] = w
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

#!/usr/bin/env python3
"""Project Turing, task 32 generator (proof writing): permutation behaviour, value sets, fixed
points and iterates of Dickson polynomials over finite fields and over Z/mZ (Dickson 1897,
Noebauer 1968, Lausch, Mueller and Noebauer 1973, Chou, Gomez-Calderon and Mullen 1988).

D_n(x, a): D_0 = 2, D_1 = x, D_{n+2} = x D_{n+1} - a D_n (Mathlib: Polynomial.dickson 1 a n).
F_q is a finite field with q elements. Theorems:
  1. a != 0 in F_q: D_n(x, a) permutes F_q iff gcd(n, q^2 - 1) = 1
  2. a a unit of Z/mZ (m >= 0): D_n(x, a) permutes Z/mZ iff every prime p | m has
     gcd(n, p^2 - 1) = 1, and p does not divide n when p^2 | m
  3. a != 0 in F_q: D_n(x, a) takes exactly
     floor(((q - 1)/gcd(n, q - 1) + (q + 1)/gcd(n, q + 1) + 1)/2) + e values, where e = 1 if a
     is a non-square and (q^2 - 1)/gcd(n, q^2 - 1) = 2 mod 4, else e = 0
  4. q odd, n >= 1: D_n(x, 1) = x has exactly
     (gcd(n-1, q-1) + gcd(n+1, q-1) + gcd(n-1, q+1) + gcd(n+1, q+1))/2 - 1 - (n mod 2)
     solutions x in F_q
  5. the k-fold iterate of x -> D_n(x, 1) on F_q is the identity iff n^k = +-1 mod q - 1 and
     n^k = +-1 mod q + 1 (independent signs)

Writes, next to this script:
  task32_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact arithmetic in finite fields (tables for F_q, q prime or q in
{4, 8, 9, 16, 25, 27, 32, 49}) and in Z/mZ:
  - theorems 1 and 3 for every field in the list, every a != 0 and every n in one full period
    0 <= n <= q^2 - 2 (the map x -> D_n(x, a) and both right-hand sides depend only on
    n mod q^2 - 1), so they hold for all n over these fields;
  - theorem 4 for every odd q in the list and 1 <= n <= q^2 - 1 (one full period);
  - theorem 5 for every field in the list and every n in one period: the order of the
    permutation equals the least k >= 1 with n^k = +-1 mod q - 1 and mod q + 1, and for
    non-bijective maps no iterate with k >= 1 is the identity and the right side fails;
  - theorem 2 for 1 <= m <= 100 with every unit a and 0 <= n <= 36, and for prime powers
    m <= 361 with three units and 0 <= n <= 60 (m = 0 reduces to m = p^2, see the golden plan);
  - the data of the planned golden route: x = u + a/u with u in F_q* or u^(q+1) = a inside
    F_(q^2) and D_n(x, a) = u^n + a^n u^(-n); the orbit count of the value sets; the fixed point
    criterion u^(n-1) = 1 or u^(n+1) = 1; D_n' = n E_(n-1) in Z[x, a]; the Hensel data mod p^2;
  - a numeric witness for every hypothesis: dropping it makes the statement false (also for
    replacing the field by the ring Z/4Z in theorems 1 and 5).
There is no finite search space: the field, m, n and k are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t32_generator.py
"""

TASK = 32
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

THEOREMS = [
    ("dickson_bijective_iff",
     "(K : Type*) [Field K] [Fintype K] (a : K) (ha : Not (a = 0))\n    (n : Nat)",
     "    Function.Bijective (fun x : K => (Polynomial.dickson 1 a n).eval x) <->\n"
     "      Nat.Coprime n (Fintype.card K ^ 2 - 1)"),
    ("dickson_bijective_zmod_iff",
     "(m n : Nat) (a : ZMod m) (ha : IsUnit a)",
     "    Function.Bijective (fun x : ZMod m => (Polynomial.dickson 1 a n).eval x) <->\n"
     "      forall p : Nat, p.Prime -> m % p = 0 ->\n"
     "        Nat.Coprime n (p ^ 2 - 1) /\\ (m % p ^ 2 = 0 -> Not (n % p = 0))"),
    ("card_image_dickson",
     "(K : Type*) [Field K] [Fintype K] [DecidableEq K] (a : K)\n"
     "    (ha : Not (a = 0)) (n : Nat)",
     "    (Finset.image (fun x : K => (Polynomial.dickson 1 a n).eval x) Finset.univ).card =\n"
     "      ((Fintype.card K - 1) / Nat.gcd n (Fintype.card K - 1) +\n"
     "          (Fintype.card K + 1) / Nat.gcd n (Fintype.card K + 1) + 1) / 2 +\n"
     "        (if Not (IsSquare a) /\\\n"
     "            (Fintype.card K ^ 2 - 1) / Nat.gcd n (Fintype.card K ^ 2 - 1) % 4 = 2\n"
     "          then 1 else 0)"),
    ("card_fixed_dickson_one",
     "(K : Type*) [Field K] [Fintype K] [DecidableEq K]\n"
     "    (hK : Fintype.card K % 2 = 1) (n : Nat) (hn : 1 <= n)",
     "    (Finset.filter (fun x : K => (Polynomial.dickson 1 (1 : K) n).eval x = x)\n"
     "        Finset.univ).card =\n"
     "      (Nat.gcd (n - 1) (Fintype.card K - 1) + Nat.gcd (n + 1) (Fintype.card K - 1) +\n"
     "          Nat.gcd (n - 1) (Fintype.card K + 1) + Nat.gcd (n + 1) (Fintype.card K + 1)) / 2 -\n"
     "        1 - n % 2"),
    ("iterate_dickson_one_eq_id_iff",
     "(K : Type*) [Field K] [Fintype K] (n k : Nat)",
     "    Nat.iterate (fun x : K => (Polynomial.dickson 1 (1 : K) n).eval x) k = id <->\n"
     "      (((n : Int) ^ k - 1) % ((Fintype.card K : Int) - 1) = 0 \\/\n"
     "          ((n : Int) ^ k + 1) % ((Fintype.card K : Int) - 1) = 0) /\\\n"
     "        (((n : Int) ^ k - 1) % ((Fintype.card K : Int) + 1) = 0 \\/\n"
     "          ((n : Int) ^ k + 1) % ((Fintype.card K : Int) + 1) = 0)"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. Over a commutative ring, define the Dickson polynomials $D_n(x, a)$ with parameter $a$ by $D_0(x, a) = 2$, $D_1(x, a) = x$ and $D_{n+2}(x, a) = x D_{n+1}(x, a) - a D_n(x, a)$, so for example $D_2(x, a) = x^2 - 2a$ and $D_3(x, a) = x^3 - 3ax$. Below $\mathbb{F}_q$ is a finite field with $q$ elements, $n, k \ge 0$, and $D_n(x, a)$ permutes a ring $R$ when $x \mapsto D_n(x, a)$ is a bijection from $R$ to $R$.

1. Let $a \in \mathbb{F}_q$ with $a \ne 0$. Then $D_n(x, a)$ permutes $\mathbb{F}_q$ if and only if $\gcd(n, q^2 - 1) = 1$.
2. Let $m \ge 0$ and let $a$ be a unit of $\mathbb{Z}/m\mathbb{Z}$ (for $m = 0$ this ring is $\mathbb{Z}$). Then $D_n(x, a)$ permutes $\mathbb{Z}/m\mathbb{Z}$ if and only if every prime $p$ dividing $m$ satisfies $\gcd(n, p^2 - 1) = 1$, and also $p \nmid n$ whenever $p^2 \mid m$.
3. Let $a \in \mathbb{F}_q$ with $a \ne 0$. The number of distinct values of $D_n(x, a)$ for $x \in \mathbb{F}_q$ is
$$\left\lfloor \frac{1}{2} \left( \frac{q - 1}{\gcd(n, q - 1)} + \frac{q + 1}{\gcd(n, q + 1)} + 1 \right) \right\rfloor + \varepsilon,$$
where $\varepsilon = 1$ if $a$ is not a square in $\mathbb{F}_q$ and $(q^2 - 1)/\gcd(n, q^2 - 1) \equiv 2 \pmod 4$, and $\varepsilon = 0$ otherwise.
4. If $q$ is odd and $n \ge 1$, the number of $x \in \mathbb{F}_q$ with $D_n(x, 1) = x$ is
$$\frac{1}{2} \big( \gcd(n - 1, q - 1) + \gcd(n + 1, q - 1) + \gcd(n - 1, q + 1) + \gcd(n + 1, q + 1) \big) - 1 - \delta,$$
where $\delta = 1$ for odd $n$, $\delta = 0$ for even $n$, and $\gcd(0, b) = b$.
5. The $k$-fold composition of the map $x \mapsto D_n(x, 1)$ on $\mathbb{F}_q$ is the identity if and only if $n^k \equiv \pm 1 \pmod{q - 1}$ and $n^k \equiv \pm 1 \pmod{q + 1}$, where the two signs need not agree.

Lean statement. $D_n(x, a)$ is `(Polynomial.dickson 1 a n).eval x`, since Mathlib's `Polynomial.dickson 1 a n` satisfies the recursion above. A finite field is a type `K` with `[Field K] [Fintype K]`, so $q$ is `Fintype.card K`, and $\mathbb{Z}/m\mathbb{Z}$ is `ZMod m`. In theorem 3 the number of values is the size of a `Finset.image` and $\lfloor s/2 \rfloor$ is the natural-number division `s / 2`. In theorem 5 the composition is `Nat.iterate` and the congruences use integer remainders. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
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

    def dickson_rows(T, a, N, dom=None):
        """Values of D_n(x, a) for x in dom (default: all elements), n = 0..N."""
        q, AT, MT, NEG = T
        X = np.arange(q) if dom is None else np.array(dom)
        d0 = np.full(len(X), AT[1, 1])
        d1 = X.copy()
        out = [d0, d1]
        for n in range(2, N + 1):
            d0, d1 = d1, AT[MT[X, d1], NEG[MT[a, d0]]]
            out.append(d1)
        return out[:N + 1]

    def nvalues(v, q):
        return int(np.count_nonzero(np.bincount(v, minlength=q)))

    def is_prime(m):
        return m > 1 and all(m % d for d in range(2, int(m ** 0.5) + 1))

    fields = [(p, 1) for p in range(2, 44) if is_prime(p)]
    fields += [(2, 2), (2, 3), (3, 2), (2, 4), (5, 2), (3, 3), (2, 5), (7, 2)]
    tables = {}
    t1 = t3 = t4 = t5 = 0
    for (p, k) in fields:
        T = gf(p, k)
        q, AT, MT, NEG = T
        tables[q] = T
        squares = set(int(MT[t, t]) for t in range(q))
        X = np.arange(q)
        for a in range(1, q):
            rows = dickson_rows(T, a, q * q - 1)
            for n in range(q * q - 1):
                V = nvalues(rows[n], q)
                assert (V == q) == (gcd(n, q * q - 1) == 1), (q, a, n)          # theorem 1
                t1 += 1
                eps = 1 if (a not in squares and (q * q - 1) // gcd(n, q * q - 1) % 4 == 2) else 0
                F = ((q - 1) // gcd(n, q - 1) + (q + 1) // gcd(n, q + 1) + 1) // 2 + eps
                assert V == F, (q, a, n, V, F)                                    # theorem 3
                t3 += 1
            if a != 1:
                continue
            if q % 2 == 1:
                for n in range(1, q * q):                                         # theorem 4
                    fx = int((rows[n] == X).sum())
                    F4 = (gcd(n - 1, q - 1) + gcd(n + 1, q - 1) + gcd(n - 1, q + 1)
                          + gcd(n + 1, q + 1)) // 2 - 1 - n % 2
                    assert fx == F4, (q, n, fx, F4)
                    t4 += 1
            for n in range(q * q - 1):                                            # theorem 5
                f = rows[n]

                def rhs(kk):
                    N1, N2 = pow(n, kk, q - 1) if q > 2 else 0, pow(n, kk, q + 1)
                    return (N1 in (1 % (q - 1), (q - 2) % (q - 1)) if q > 2 else True) and \
                        N2 in (1, q)
                assert rhs(0)
                if nvalues(f, q) == q:
                    cur, order = f.copy(), 1
                    while not (cur == X).all():
                        cur, order = f[cur], order + 1
                    k0 = 1
                    while not rhs(k0):
                        k0 += 1
                    assert order == k0, (q, n, order, k0)
                    for kk in range(0, 3 * order + 2):
                        assert rhs(kk) == (kk % order == 0)
                else:
                    cur = f.copy()
                    for kk in range(1, q + 3):
                        assert not (cur == X).all() and not rhs(kk)
                        cur = f[cur]
                t5 += 1
    counts["theorem 1 (bijective iff gcd(n, q^2 - 1) = 1), (q, a, n) over full periods"] = t1
    counts["theorem 3 (value set size), (q, a, n) over full periods"] = t3
    counts["theorem 4 (fixed points of D_n(x, 1)), (q, n) with q odd"] = t4
    counts["theorem 5 (iterates of D_n(x, 1)), (q, n): order = least k with n^k = +-1"] = t5

    # theorem 2 over Z/mZ
    def zrows(m, a, N):
        X = np.arange(m)
        d0 = np.full(m, 2 % m)
        d1 = X % m
        out = [d0, d1]
        for n in range(2, N + 1):
            d0, d1 = d1, (X * d1 - a * d0) % m
            out.append(d1)
        return out[:N + 1]

    def rhs2(m, n):
        ps = [p for p in range(2, m + 1) if m % p == 0 and is_prime(p)]
        return all(gcd(n, p * p - 1) == 1 and (m % (p * p) != 0 or n % p != 0) for p in ps)

    t2 = 0
    cases = [(m, a, 36) for m in range(1, 101) for a in range(m) if gcd(a, m) == 1]
    for m in (121, 125, 128, 169, 243, 289, 343, 361):
        units = [a for a in range(2, m) if gcd(a, m) == 1][:1]
        cases += [(m, 1, 60), (m, m - 1, 60), (m, units[0], 60)]
    for (m, a, N) in cases:
        rows = zrows(m, a, N)
        for n in range(N + 1):
            bij = nvalues(rows[n], m) == m
            assert bij == rhs2(m, n), (m, a, n)
            t2 += 1
    counts["theorem 2 (permutations of Z/mZ), (m, a, n)"] = t2

    # golden-route data
    route = 0

    def gpow(MT, u, e):
        r, b = 1, u
        while e:
            if e & 1:
                r = int(MT[r, b])
            b = int(MT[b, b])
            e >>= 1
        return r

    for (p, k) in [(2, 1), (3, 1), (2, 2), (5, 1), (7, 1), (2, 3), (3, 2)]:
        q = p ** k
        T2 = gf(p, 2 * k)
        Q, AT, MT, NEG = T2
        INV = {u: int(np.nonzero(MT[u] == 1)[0][0]) for u in range(1, Q)}
        sub = [u for u in range(Q) if gpow(MT, u, q) == u]               # F_q inside F_(q^2)
        assert len(sub) == q
        for a in [s for s in sub if s]:
            rows = dickson_rows(T2, a, q * q, dom=sub)
            roots = {}
            for i, x in enumerate(sub):
                us = [u for u in range(1, Q)
                      if AT[AT[MT[u, u], NEG[MT[x, u]]], a] == 0]           # u^2 - x u + a = 0
                assert us
                for u in us:
                    assert u in sub or gpow(MT, u, q + 1) == a
                    for n in range(q * q + 1):
                        an = gpow(MT, a, n)
                        un = gpow(MT, u, n)
                        assert rows[n][i] == AT[un, MT[an, INV[un]]]
                        route += 1
                roots[x] = us[0]
            # orbit count of the value set
            g = [u for u in range(1, Q) if gpow(MT, u, q + 1) == a]
            for n in range(q * q - 1):
                an = gpow(MT, a, n)
                T1 = {gpow(MT, u, n) for u in sub if u}
                T2s = {gpow(MT, u, n) for u in g}

                def orbits(S):
                    return (len(S) + sum(1 for w in S if MT[w, w] == an)) // 2
                val = orbits(T1) + orbits(T2s) - len(T1 & T2s)
                assert val == len(set(rows[n].tolist()))
                route += 1
            # fixed points of D_n(x, 1)
            if a == 1 and q % 2 == 1:
                for n in range(1, q * q):
                    for i, x in enumerate(sub):
                        u = roots[x]
                        fixed = rows[n][i] == x
                        assert fixed == (gpow(MT, u, n - 1) == 1 or gpow(MT, u, n + 1) == 1)
                        route += 1

    # D_n' = n E_(n-1) in Z[x, a]: polynomials as dicts {(i, j): c} for x^i a^j
    def padd(f, g, s=1):
        h = dict(f)
        for key, c in g.items():
            h[key] = h.get(key, 0) + s * c
        return {key: c for key, c in h.items() if c}

    def pmulx(f, i0, j0):
        return {(i + i0, j + j0): c for (i, j), c in f.items()}

    D = [{(0, 0): 2}, {(1, 0): 1}]
    E = [{(0, 0): 1}, {(1, 0): 1}]
    for n in range(2, 32):
        D.append(padd(pmulx(D[n - 1], 1, 0), pmulx(D[n - 2], 0, 1), -1))
        E.append(padd(pmulx(E[n - 1], 1, 0), pmulx(E[n - 2], 0, 1), -1))
    for n in range(1, 32):
        der = {(i - 1, j): i * c for (i, j), c in D[n].items() if i}
        assert der == {key: n * c for key, c in E[n - 1].items()}
        route += 1

    # Hensel data mod p^2 under gcd(n, p^2 - 1) = 1
    for p in (2, 3, 5, 7, 11, 13, 17, 19):
        m = p * p
        for a in range(1, p):
            Erows = [np.full(p, 1), np.arange(p)]
            X = np.arange(p)
            for n in range(2, 3 * (p * p - 1)):
                Erows.append((X * Erows[-1] - a * Erows[-2]) % p)
            rows = zrows(m, a, 3 * (p * p - 1))
            for n in range(1, 3 * (p * p - 1)):
                if gcd(n, p * p - 1) != 1:
                    continue
                if n % p:
                    assert (Erows[n - 1] % p != 0).all()          # D_n' = n E_(n-1) has no root
                else:
                    v = rows[n]
                    assert all(v[(x + p) % m] == v[x] for x in range(m))   # not injective
                route += 1
    # m = 0: for n >= 2 and a = +-1 some p^2 with p | n already fails
    for n in range(2, 61):
        p = next(d for d in range(2, n + 1) if n % d == 0)
        for a in (1, -1):
            assert nvalues(zrows(p * p, a % (p * p), n)[n], p * p) < p * p
            route += 1
    counts["golden-route data (u + a/u, orbit counts, fixed points, D_n' = n E_(n-1), Hensel)"] \
        = route

    # witnesses
    w = 0
    T5 = tables[5]
    assert nvalues(dickson_rows(T5, 0, 3)[3], 5) == 5 and gcd(3, 24) == 3   # thm 1 with a = 0
    z4 = zrows(4, 1, 5)
    assert nvalues(z4[2], 4) < 4 and gcd(2, 15) == 1        # thm 1 for the ring Z/4Z, n = 2
    w += 1
    z9 = zrows(9, 3, 5)
    assert nvalues(z9[5], 9) < 9 and rhs2(9, 5)              # thm 2 with a = 3, m = 9, n = 5
    w += 1
    F = ((5 - 1) // gcd(3, 4) + (5 + 1) // gcd(3, 6) + 1) // 2
    assert nvalues(dickson_rows(T5, 0, 3)[3], 5) == 5 != F   # thm 3 with a = 0 (0 is a square)
    w += 1
    T2f = tables[2]
    fx = int((dickson_rows(T2f, 1, 1)[1] == np.arange(2)).sum())
    assert fx == 2 != (gcd(0, 1) + gcd(2, 1) + gcd(0, 3) + gcd(2, 3)) // 2 - 1 - 1   # q = 2
    T3 = tables[3]
    fx0 = int((dickson_rows(T3, 1, 1)[0] == np.arange(3)).sum())
    assert fx0 == 1 != (gcd(0, 2) + gcd(1, 2) + gcd(0, 4) + gcd(1, 4)) // 2 - 1 - 0   # n = 0
    w += 2
    assert (z4[5] == np.arange(4)).all()                     # thm 5 for the ring Z/4Z: n = 5,
    assert not ((5 - 1) % 5 == 0 or (5 + 1) % 5 == 0)        # k = 1 is the identity, 5 = 0 mod 5
    counts["witnesses for the 5 hypotheses (each one false when dropped), plus Z/4Z for the "
           "field in theorems 1 and 5"] = w
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

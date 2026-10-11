#!/usr/bin/env python3
"""Project Turing, task 35 generator (proof writing): discriminants and the parity of the number
of irreducible factors (Stickelberger 1897, Swan 1962), and the Liouville sum over F_q[X].

disc = discriminant, r(f) = number of irreducible factors of f counted with multiplicity.
Theorems:
  1. q odd, f in F_q[X] squarefree: disc(f) is a square iff r(f) = deg f mod 2 (Stickelberger)
  2. F in Z[X] monic with squarefree reduction mod 2: disc(F) = 1 mod 8 iff r(F mod 2) = deg F
     mod 2 (Swan)
  3. 0 < k < n, d = gcd(n, k), N = n/d, K = k/d:
     disc(X^n + a X^k + b) = (-1)^(n(n-1)/2) b^(k-1) (n^N b^(N-K) - (-1)^N (n-k)^(N-K) k^K a^N)^d
  4. 0 < k < n, n + k odd: X^n + X^k + 1 in F_2[X] has an even number of irreducible factors
     iff (n even, n != 2k, nk/2 = 0 or 1 mod 4) or (n odd, k does not divide 2n,
     n = +-3 mod 8) or (n odd, k | 2n, n = +-1 mod 8) (Swan)
  5. sum over the q^n monic f of degree n of (-1)^r(f) = (-1)^n q^ceil(n/2)

Writes, next to this script:
  task35_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact arithmetic. Discriminants over Z come from the Sylvester
determinant (fraction-free Bareiss elimination): disc(F) = (-1)^(n(n-1)/2) Res(F, F')/lc(F).
Factor counts over F_2 come from Berlekamp's matrix (for squarefree f the number of irreducible
factors is deg f - rank(Q - I)), and over F_q (q = 3, 4, 5, 7, 9) from trial division.
  - theorem 1 for every squarefree polynomial (any leading coefficient) of degree <= 5 over F_3,
    <= 4 over F_5, <= 3 over F_7 and F_9;
  - theorem 2 for every monic F in Z[X] of degree 1 to 6 with coefficients in [-2, 2] and
    squarefree reduction;
  - theorem 3 for 2 <= n <= 11, every 0 < k < n and a, b in [-3, 3];
  - theorem 4 for every n <= 200 (10,000 pairs (n, k));
  - theorem 5 for q = 2 (n <= 8), 3 (n <= 5), 4 and 5 (n <= 4), 7 and 9 (n <= 3);
  - the data of the planned golden route: disc(f g) = disc(f) disc(g) Res(f, g)^2 for random
    monic integer f, g, and Swan's formula mod 8 at the trinomials of theorem 4 (n <= 60);
  - a numeric witness for every hypothesis: dropping it makes the statement false.
There is no finite search space: the field, the degree and the coefficients are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t35_generator.py
"""

TASK = 35
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

THEOREMS = [
    ("isSquare_discr_iff",
     "(K : Type*) [Field K] [Fintype K] [DecidableEq K]\n"
     "    (hK : Fintype.card K % 2 = 1) (f : Polynomial K) (hf : Squarefree f)",
     "    IsSquare f.discr <->\n"
     "      (Multiset.card (UniqueFactorizationMonoid.normalizedFactors f) + f.natDegree) % 2 = 0"),
    ("discr_emod_eight_eq_one_iff",
     "(F : Polynomial Int) (hF : F.Monic)\n"
     "    (hsq : Squarefree (F.map (Int.castRingHom (ZMod 2))))",
     "    F.discr % 8 = 1 <->\n"
     "      (Multiset.card (UniqueFactorizationMonoid.normalizedFactors\n"
     "          (F.map (Int.castRingHom (ZMod 2)))) + F.natDegree) % 2 = 0"),
    ("discr_trinomial",
     "(n k : Nat) (hk : 0 < k) (hkn : k < n) (a b : Int)",
     "    (Polynomial.X ^ n + Polynomial.C a * Polynomial.X ^ k + Polynomial.C b).discr =\n"
     "      (-1) ^ (n * (n - 1) / 2) * b ^ (k - 1) *\n"
     "        ((n : Int) ^ (n / Nat.gcd n k) * b ^ (n / Nat.gcd n k - k / Nat.gcd n k) -\n"
     "          (-1) ^ (n / Nat.gcd n k) * ((n - k : Nat) : Int) ^ (n / Nat.gcd n k - k / Nat.gcd n k) *\n"
     "            (k : Int) ^ (k / Nat.gcd n k) * a ^ (n / Nat.gcd n k)) ^ Nat.gcd n k"),
    ("even_card_normalizedFactors_trinomial_iff",
     "(n k : Nat) (hk : 0 < k) (hkn : k < n)\n    (hnk : (n + k) % 2 = 1)",
     "    Multiset.card (UniqueFactorizationMonoid.normalizedFactors\n"
     "        (Polynomial.X ^ n + Polynomial.X ^ k + 1 : Polynomial (ZMod 2))) % 2 = 0 <->\n"
     "      (n % 2 = 0 /\\ Not (n = 2 * k) /\\ n * k / 2 % 4 <= 1) \\/\n"
     "        (n % 2 = 1 /\\ Not (2 * n % k = 0) /\\ (n % 8 = 3 \\/ n % 8 = 5)) \\/\n"
     "          (n % 2 = 1 /\\ 2 * n % k = 0 /\\ (n % 8 = 1 \\/ n % 8 = 7))"),
    ("sum_neg_one_pow_card_normalizedFactors",
     "(K : Type*) [Field K] [Fintype K] [DecidableEq K]\n    (n : Nat)",
     "    Finset.sum Finset.univ (fun c : Fin n -> K =>\n"
     "        (-1 : Int) ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors\n"
     "          (Polynomial.X ^ n +\n"
     "            Finset.sum Finset.univ\n"
     "              (fun i : Fin n => Polynomial.C (c i) * Polynomial.X ^ (i : Nat))))) =\n"
     "      (-1) ^ n * (Fintype.card K : Int) ^ ((n + 1) / 2)"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. For a polynomial $f$ over a commutative ring, $\operatorname{disc}(f)$ denotes its discriminant, and for a polynomial $f$ over a field, $r(f)$ is the number of irreducible factors of $f$ counted with multiplicity. Below $\mathbb{F}_q$ is a finite field with $q$ elements.

1. (Stickelberger.) Let $q$ be odd and let $f \in \mathbb{F}_q[X]$ be squarefree. Then $\operatorname{disc}(f)$ is a square in $\mathbb{F}_q$ if and only if $r(f) \equiv \deg f \pmod 2$.
2. (Swan.) Let $F \in \mathbb{Z}[X]$ be monic with squarefree reduction $\bar F \in \mathbb{F}_2[X]$. Then $\operatorname{disc}(F) \equiv 1 \pmod 8$ if and only if $r(\bar F) \equiv \deg F \pmod 2$.
3. (Swan.) Let $0 < k < n$, $d = \gcd(n, k)$, $N = n/d$, $K = k/d$ and $a, b \in \mathbb{Z}$. Then
$$\operatorname{disc}(X^n + aX^k + b) = (-1)^{n(n-1)/2}\, b^{k-1} \big( n^N b^{N-K} - (-1)^N (n-k)^{N-K} k^K a^N \big)^d.$$
4. (Swan.) Let $0 < k < n$ with $n + k$ odd. Then $X^n + X^k + 1 \in \mathbb{F}_2[X]$ has an even number of irreducible factors if and only if (a) $n$ is even, $n \ne 2k$ and $nk/2 \equiv 0$ or $1 \pmod 4$, or (b) $n$ is odd, $k \nmid 2n$ and $n \equiv \pm 3 \pmod 8$, or (c) $n$ is odd, $k \mid 2n$ and $n \equiv \pm 1 \pmod 8$.
5. For every $n \ge 0$, the sum of $(-1)^{r(f)}$ over the $q^n$ monic polynomials $f \in \mathbb{F}_q[X]$ of degree $n$ equals $(-1)^n q^{\lceil n/2 \rceil}$.

Lean statement. The discriminant is Mathlib's `Polynomial.discr`, $r(f)$ is `Multiset.card (UniqueFactorizationMonoid.normalizedFactors f)`, and the reduction modulo $2$ is `F.map (Int.castRingHom (ZMod 2))`. A finite field is a type `K` with `[Field K] [Fintype K] [DecidableEq K]`, so $q$ is `Fintype.card K`. In theorem 4 the condition "$nk/2 \equiv 0$ or $1 \pmod 4$" reads `n * k / 2 % 4 <= 1`. In theorem 5 the monic polynomials of degree $n$ are $X^n + \sum_{i < n} c_i X^i$ for the functions `c : Fin n -> K`, and $\lceil n/2 \rceil$ is `(n + 1) / 2`. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    import itertools
    import random
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


    def bareiss_det(M):
        """Exact determinant of an integer matrix (fraction-free elimination)."""
        A = [row[:] for row in M]
        n = len(A)
        if n == 0:
            return 1
        sign, prev = 1, 1
        for k in range(n - 1):
            if A[k][k] == 0:
                sw = next((i for i in range(k + 1, n) if A[i][k] != 0), None)
                if sw is None:
                    return 0
                A[k], A[sw] = A[sw], A[k]
                sign = -sign
            for i in range(k + 1, n):
                for j in range(k + 1, n):
                    A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
            prev = A[k][k]
        return sign * A[n - 1][n - 1]

    def sylvester(f, g, m, n):
        """Sylvester matrix of f (formal degree m) and g (formal degree n), coefficient lists
        with the constant term first."""
        size = m + n
        S = []
        for i in range(n):
            row = [0] * size
            for j in range(m + 1):
                row[i + j] = f[m - j] if m - j < len(f) else 0
            S.append(row)
        for i in range(m):
            row = [0] * size
            for j in range(n + 1):
                row[i + j] = g[n - j] if n - j < len(g) else 0
            S.append(row)
        return S

    def disc_int(f):
        """Discriminant of an integer polynomial of degree n = len(f) - 1 (leading coefficient
        nonzero): (-1)^(n(n-1)/2) Res(f, f') / lc(f)."""
        n = len(f) - 1
        if n <= 0:
            return 1
        df = [i * f[i] for i in range(1, n + 1)]
        r = bareiss_det(sylvester(f, df, n, n - 1))
        assert r % f[-1] == 0
        return (-1) ** (n * (n - 1) // 2) * (r // f[-1])

    # quick self-test of disc_int on quadratics and cubics
    for (a, b, c) in [(1, 0, -4), (2, 1, 1), (3, -5, 7)]:
        assert disc_int([c, b, a]) == b * b - 4 * a * c
    for (a, b, c, d) in [(1, 0, -1, 0), (2, -3, 5, 7)]:
        assert disc_int([d, c, b, a]) == (b * b * c * c - 4 * a * c ** 3 - 4 * b ** 3 * d
                                          - 27 * a * a * d * d + 18 * a * b * c * d)

    # F_2[X] as bitmasks
    def f2_mulmod(a, b, f, n):
        r = 0
        while b:
            if b & 1:
                r ^= a
            b >>= 1
            a <<= 1
            if a >> n & 1:
                a ^= f
        return r

    def f2_mod(a, b):
        db = b.bit_length() - 1
        while a and a.bit_length() - 1 >= db:
            a ^= b << (a.bit_length() - 1 - db)
        return a

    def f2_gcd(a, b):
        while b:
            a, b = b, f2_mod(a, b)
        return a

    def f2_deriv(a):
        out, i = 0, 1
        while a >> i:
            if (a >> i) & 1 and i % 2 == 1:
                out |= 1 << (i - 1)
            i += 1
        return out

    def f2_squarefree(a):
        return a != 0 and f2_gcd(a, f2_deriv(a)) == 1

    def f2_count(f):
        """Number of irreducible factors of a squarefree f in F_2[X] (Berlekamp)."""
        n = f.bit_length() - 1
        if n <= 0:
            return 0
        xsq = f2_mulmod(2, 2, f, n) if n > 1 else f2_mod(4, f)
        rows, cur = [], 1
        for i in range(n):
            rows.append(cur ^ (1 << i))
            cur = f2_mulmod(cur, xsq, f, n)
        rank = 0
        for bit in range(n):
            piv = next((j for j in range(rank, n) if rows[j] >> bit & 1), None)
            if piv is None:
                continue
            rows[rank], rows[piv] = rows[piv], rows[rank]
            for j in range(n):
                if j != rank and rows[j] >> bit & 1:
                    rows[j] ^= rows[rank]
            rank += 1
        return n - rank

    def swan_rhs(n, k):
        return ((n % 2 == 0 and n != 2 * k and (n * k // 2) % 4 <= 1) or
                (n % 2 == 1 and (2 * n) % k != 0 and n % 8 in (3, 5)) or
                (n % 2 == 1 and (2 * n) % k == 0 and n % 8 in (1, 7)))

    def swan_disc(n, k, a, b):
        d = gcd(n, k)
        N, K = n // d, k // d
        return ((-1) ** (n * (n - 1) // 2) * b ** (k - 1)
                * (n ** N * b ** (N - K) - (-1) ** N * (n - k) ** (N - K) * k ** K * a ** N) ** d)

    route = 0
    # theorem 4: all trinomials with n <= 200
    t4 = 0
    for n in range(2, 201):
        for k in range(1, n):
            if (n + k) % 2 == 0:
                continue
            f = (1 << n) | (1 << k) | 1
            assert f2_squarefree(f)
            r = f2_count(f)
            assert (r % 2 == 0) == swan_rhs(n, k), (n, k)
            t4 += 1
            if n <= 60:                       # the route: Swan's formula mod 8 and theorem 2
                dsc = swan_disc(n, k, 1, 1)
                assert (dsc % 8 == 1) == ((r + n) % 2 == 0)
                route += 1
    counts_t4 = t4

    # theorem 3: Swan's discriminant formula against the Sylvester determinant
    t3 = 0
    for n in range(2, 12):
        for k in range(1, n):
            rng = range(-3, 4) if n <= 8 else range(-2, 3)
            for a in rng:
                for b in rng:
                    f = [0] * (n + 1)
                    f[0] += b
                    f[k] += a
                    f[n] += 1
                    assert disc_int(f) == swan_disc(n, k, a, b), (n, k, a, b)
                    t3 += 1

    # theorem 2: monic integer polynomials of degree 1..6, coefficients in [-2, 2]
    t2 = 0
    for n in range(1, 7):
        for cs in itertools.product(range(-2, 3), repeat=n):
            F = list(cs) + [1]
            red = sum(1 << i for i, c in enumerate(F) if c % 2)
            if not f2_squarefree(red):
                continue
            r = f2_count(red)
            assert (disc_int(F) % 8 == 1) == ((r + n) % 2 == 0), F
            t2 += 1

    # F_q helpers on top of the class above
    def fq_divmod(f, a, b):
        a = list(a)
        db = len(b) - 1
        li = f.INV[b[-1]]
        quo = [0] * max(0, len(a) - db)
        while a and len(a) - 1 >= db:
            c = f.MT[a[-1]][li]
            sh = len(a) - 1 - db
            quo[sh] = c
            for i, y in enumerate(b):
                a[sh + i] = f.AT[a[sh + i]][f.NEG[f.MT[c][y]]]
            a = list(f.norm(a))
        return f.norm(quo), tuple(a)

    def fq_deriv(f, a):
        out = []
        for i in range(1, len(a)):
            c = 0
            for _ in range(i % f.p):
                c = f.AT[c][a[i]]
            out.append(c)
        return f.norm(out)

    def fq_gcd(f, a, b):
        while b:
            a, b = b, f.mod(a, b)
        return a

    def fq_squarefree(f, a):
        return bool(a) and len(fq_gcd(f, a, fq_deriv(f, a))) == 1

    def fq_count(f, a, irr):
        """Irreducible factors of a with multiplicity, by trial division."""
        cnt = 0
        for d in sorted(irr):
            for g in irr[d]:
                while len(a) - 1 >= d:
                    q_, r_ = fq_divmod(f, a, g)
                    if r_:
                        break
                    a = q_
                    cnt += 1
        assert len(a) == 1, a
        return cnt

    def fq_det(f, M):
        A = [row[:] for row in M]
        n = len(A)
        det = 1
        for k in range(n):
            piv = next((i for i in range(k, n) if A[i][k]), None)
            if piv is None:
                return 0
            if piv != k:
                A[k], A[piv] = A[piv], A[k]
                det = f.NEG[det]
            det = f.MT[det][A[k][k]]
            inv = f.INV[A[k][k]]
            for i in range(k + 1, n):
                if A[i][k]:
                    c = f.MT[A[i][k]][inv]
                    A[i] = [f.AT[x][f.NEG[f.MT[c][y]]] for x, y in zip(A[i], A[k])]
        return det

    def fq_disc(f, a):
        n = len(a) - 1
        if n <= 0:
            return 1
        da = [0] * n
        for i in range(1, n + 1):
            c = 0
            for _ in range(i % f.p):
                c = f.AT[c][a[i]]
            da[i - 1] = c
        r = fq_det(f, sylvester(list(a), da, n, n - 1))
        r = f.MT[r][f.INV[a[-1]]]
        return f.NEG[r] if (n * (n - 1) // 2) % 2 else r

    plan = {(3, 1): (5, 5), (5, 1): (4, 4), (7, 1): (3, 3), (3, 2): (3, 3), (2, 1): (0, 8),
            (2, 2): (0, 4)}
    t1 = t5 = 0
    fields = {}
    for (p, k), (D1, D5) in plan.items():
        f = Fq(p, k)
        f.p = p
        q = f.q
        fields[q] = f
        D = max(D1, D5)
        irr = {d: [g for g in f.monics(d) if f.irreducible(g)] for d in range(1, D + 1)}
        for n in range(0, D1 + 1):                                               # theorem 1
            for lead in range(1, q):
                for cs in itertools.product(range(q), repeat=n):
                    a = tuple(cs) + (lead,)
                    if not fq_squarefree(f, a):
                        continue
                    r = fq_count(f, a, irr)
                    assert (fq_disc(f, a) in f.SQ) == ((r + n) % 2 == 0), (q, a)
                    t1 += 1
        for n in range(0, D5 + 1):                                               # theorem 5
            s = 0
            for a in f.monics(n):
                s += (-1) ** fq_count(f, a, irr)
            assert s == (-1) ** n * q ** ((n + 1) // 2), (q, n, s)
            t5 += 1

    # golden route: disc(f g) = disc(f) disc(g) Res(f, g)^2 for monic integer f, g
    rnd = random.Random(35)
    for _ in range(300):
        m, n = rnd.randint(1, 4), rnd.randint(1, 4)
        F = [rnd.randint(-3, 3) for _ in range(m)] + [1]
        G = [rnd.randint(-3, 3) for _ in range(n)] + [1]
        FG = [0] * (m + n + 1)
        for i, x in enumerate(F):
            for j, y in enumerate(G):
                FG[i + j] += x * y
        res = bareiss_det(sylvester(F, G, m, n))
        assert disc_int(FG) == disc_int(F) * disc_int(G) * res * res
        route += 1

    counts["theorem 1 (Stickelberger), squarefree polynomials over F_3, F_5, F_7, F_9"] = t1
    counts["theorem 2 (Swan, mod 8), monic integer polynomials with squarefree reduction"] = t2
    counts["theorem 3 (trinomial discriminant), (n, k, a, b)"] = t3
    counts["theorem 4 (trinomials over F_2), pairs (n, k) with n <= 200"] = counts_t4
    counts["theorem 5 (Liouville sum), pairs (q, n)"] = t5
    counts["golden-route data (disc of products, Swan's formula mod 8 at the trinomials)"] = route

    # witnesses
    w = 0
    F2, F3 = fields[2], fields[3]
    irr2 = {d: [g for g in F2.monics(d) if F2.irreducible(g)] for d in range(1, 5)}
    irr3 = {d: [g for g in F3.monics(d) if F3.irreducible(g)] for d in range(1, 5)}
    a = (1, 1, 1)                                      # q = 2: X^2 + X + 1
    assert fq_squarefree(F2, a) and fq_disc(F2, a) in F2.SQ and (fq_count(F2, a, irr2) + 2) % 2
    a = (0, 0, 1, 0, 1)                                # q = 3: X^2 (X^2 + 1), not squarefree
    assert fq_disc(F3, a) == 0 and (fq_count(F3, a, irr3) + 4) % 2 == 1
    w += 2
    assert disc_int([1, 1, 2]) % 8 == 1 and (1 + 2) % 2 == 1      # F = 2X^2 + X + 1 (X + 1 mod 2)
    assert not f2_squarefree(0b101) and disc_int([1, 0, 1]) % 8 != 1    # F = X^2 + 1
    assert (2 + 2) % 2 == 0                            # (X + 1)^2 has two factors
    w += 2

    def lean_swan(n, k, a, b):                         # natural-number subtraction as in Lean
        d = gcd(n, k)
        N, K = n // d, k // d
        return ((-1) ** (n * (n - 1) // 2) * b ** max(k - 1, 0)
                * (n ** N * b ** max(N - K, 0)
                   - (-1) ** N * max(n - k, 0) ** max(N - K, 0) * k ** K * a ** N) ** d)
    assert disc_int([2, 0, 1]) == -8 != lean_swan(2, 0, 1, 1)     # k = 0: X^2 + 1 + 1
    assert disc_int([1, 0, 2]) == -8 != lean_swan(2, 2, 1, 1)     # k = n: 2 X^2 + 1
    w += 2

    def lean_rhs4(n, k):                               # Lean's n % 0 = n
        m2 = (2 * n) % k if k else 2 * n
        return ((n % 2 == 0 and n != 2 * k and (n * k // 2) % 4 <= 1) or
                (n % 2 == 1 and m2 != 0 and n % 8 in (3, 5)) or
                (n % 2 == 1 and m2 == 0 and n % 8 in (1, 7)))
    assert lean_rhs4(3, 0) and 3 % 2 == 1              # k = 0: X^3 + 1 + 1 = X^3, 3 factors
    assert f2_count(0b111) == 1 and lean_rhs4(1, 2)    # k > n: X + X^2 + 1 is irreducible
    assert not lean_rhs4(4, 2)                         # n + k even: (X^2 + X + 1)^2, 2 factors
    w += 3
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

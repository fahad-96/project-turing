#!/usr/bin/env python3
"""Project Turing, task 28 generator (proof writing): quartic and octic residuacity of 2 and
-4, the quadratic character of 1 + sqrt 2, and Dirichlet's rational quartic law for q = 2, 3
mod 4 (Gauss 1828, Dirichlet 1860, Barrucand and Cohn 1969, E. Lehmer 1978).

Theorems (p prime, all other variables natural numbers):
  1. p = 1 mod 4:  2 is a 4th power mod p  <->  p = a^2 + 64 b^2
  2. p = 1 mod 8: -4 is an 8th power mod p  <->  p = a^2 + 32 b^2
  3. p odd:        2 is a 4th power mod p  <->  e^2 = p + 2 f^2 with e = 1, 3 mod 8
  4. p = 1 mod 4, q = 2, 3 mod 4, p = c^2 + q d^2:  q is a 4th power mod p  <->  J(q | c) = 1
  5. p = 1 mod 8, s^2 = 2 mod p:  1 + s is a square mod p  <->  p = a^2 + 32 b^2

Writes, next to this script:
  task28_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic:
  - every theorem, both directions, for all primes below the stated bounds, with the left-hand
    side computed literally (search over all x in ZMod p) for p < 3000 and by the Euler
    criterion above that (the two methods are compared on the literal range);
  - the right-hand sides by complete enumeration of the representations (theorem 3: the class
    of e mod 8 is the same for every representation found in a window of several unit orbits,
    so the existential statement is decided by any one of them);
  - the data of the planned golden route: Dirichlet's formula 2^((p-1)/4) = (-1)^(b/4) for
    p = a^2 + b^2, the identity J(a + b | p) = J(2 | a + b), the general formula
    (-q)^((p-1)/4) = J(q | c) J(2 | p)^v2(d), the formulas 2^((p-1)/4) = J(-2 | e) and
    chi(1 + e/f) = J(-1 | e + f) for p = e^2 - 2 f^2, existence of the representations
    c^2 + 2 d^2 and e^2 - 2 f^2 (Thue), and the unit step e -> 3e + 4f for p = 7 mod 8;
  - a numeric witness for every hypothesis: dropping it makes the statement false.
There is no finite search space: p is unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t28_generator.py
"""

TASK = 28
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

THEOREMS = [
    ("exists_pow_four_eq_two_iff",
     "(p : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)",
     "    (exists x : ZMod p, x ^ 4 = 2) <-> exists a b : Nat, p = a ^ 2 + 64 * b ^ 2"),
    ("exists_pow_eight_eq_neg_four_iff",
     "(p : Nat) (hp : p.Prime) (hp8 : p % 8 = 1)",
     "    (exists x : ZMod p, x ^ 8 = -4) <-> exists a b : Nat, p = a ^ 2 + 32 * b ^ 2"),
    ("exists_pow_four_eq_two_iff_sq_eq_add_two_mul_sq",
     "(p : Nat) (hp : p.Prime) (hp2 : p % 2 = 1)",
     "    (exists x : ZMod p, x ^ 4 = 2) <->\n"
     "      exists e f : Nat,\n"
     "        e ^ 2 = p + 2 * f ^ 2 /\\ Membership.mem ({1, 3} : Finset Nat) (e % 8)"),
    ("exists_pow_four_eq_iff_jacobiSym",
     "(p q c d : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)\n"
     "    (hq : Membership.mem ({2, 3} : Finset Nat) (q % 4)) (hpcd : p = c ^ 2 + q * d ^ 2)",
     "    (exists x : ZMod p, x ^ 4 = (q : ZMod p)) <-> jacobiSym (q : Int) c = 1"),
    ("exists_sq_eq_one_add_sqrt_two_iff",
     "(p : Nat) (hp : p.Prime) (hp8 : p % 8 = 1)",
     "    (exists s t : ZMod p, s ^ 2 = 2 /\\ t ^ 2 = 1 + s) <->\n"
     "      exists a b : Nat, p = a ^ 2 + 32 * b ^ 2"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. Let $p$ be a prime. An integer $m$ is a $k$-th power modulo $p$ if $x^k \equiv m \pmod p$ for some integer $x$. Write $\left(\frac{a}{b}\right)$ for the Jacobi symbol, which Mathlib calls `jacobiSym a b`. In the five theorems, $a, b, c, d, e, f, q$ are natural numbers and $s$ is an integer.

1. If $p \equiv 1 \pmod 4$, then $2$ is a fourth power modulo $p$ if and only if $p = a^2 + 64 b^2$ for some $a, b$.
2. If $p \equiv 1 \pmod 8$, then $-4$ is an eighth power modulo $p$ if and only if $p = a^2 + 32 b^2$ for some $a, b$.
3. If $p$ is odd, then $2$ is a fourth power modulo $p$ if and only if $e^2 = p + 2 f^2$ for some $e, f$ with $e \equiv 1$ or $3 \pmod 8$.
4. If $p \equiv 1 \pmod 4$, $q \equiv 2$ or $3 \pmod 4$ and $p = c^2 + q d^2$, then $q$ is a fourth power modulo $p$ if and only if $\left(\frac{q}{c}\right) = 1$.
5. If $p \equiv 1 \pmod 8$ and $s^2 \equiv 2 \pmod p$, then $1 + s$ is a square modulo $p$ if and only if $p = a^2 + 32 b^2$ for some $a, b$.

In theorem 5 the answer does not depend on the choice of $s$, because $(1 + s)(1 - s) \equiv -1 \pmod p$ and $-1$ is a square modulo $p$.

Lean statement. A statement about residues modulo $p$ appears as an equation in `ZMod p`, for example `exists x : ZMod p, x ^ 4 = 2`. Theorem 5 states its left side as `exists s t : ZMod p, s ^ 2 = 2 /\ t ^ 2 = 1 + s`. A set of residues such as $e \equiv 1$ or $3 \pmod 8$ appears as `Membership.mem ({1, 3} : Finset Nat) (e % 8)`. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    from math import isqrt, gcd

    counts = {}
    N = 100000
    sieve = bytearray([1]) * (N + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, isqrt(N) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, N + 1, i)))
    primes = [p for p in range(3, N + 1) if sieve[p]]

    def jac_odd(a, n):
        """Jacobi symbol (a | n) for odd n >= 1 (value 1 for n = 1)."""
        assert n >= 1 and n % 2 == 1
        a %= n
        r = 1
        while a:
            while a % 2 == 0:
                a //= 2
                if n % 8 in (3, 5):
                    r = -r
            a, n = n, a
            if a % 4 == 3 and n % 4 == 3:
                r = -r
            a %= n
        return r if n == 1 else 0

    def jacobi_mathlib(a, n):
        """Mathlib's jacobiSym a n for n >= 0: product of Legendre symbols over the prime
        factors of n; the factor for the prime 2 is 1 if a is odd and 0 if a is even."""
        r = 1
        while n > 0 and n % 2 == 0:
            n //= 2
            r *= 1 if a % 2 else 0
        if n == 0:
            return 1
        return r * jac_odd(a, n)

    def kth_power_literal(a, k, m):
        """exists x in ZMod m with x^k = a, by search over all residues."""
        a %= m
        return any(pow(x, k, m) == a for x in range(m))

    def kth_power(a, k, p):
        """the same for a prime p, by the Euler criterion for the cyclic group."""
        a %= p
        if a == 0:
            return True
        return pow(a, (p - 1) // gcd(k, p - 1), p) == 1

    def reps(p, q):
        """all (c, d) natural with p = c^2 + q d^2"""
        out, d = [], 0
        while q * d * d <= p:
            c2 = p - q * d * d
            c = isqrt(c2)
            if c * c == c2:
                out.append((c, d))
            d += 1
        return out

    def sqrt_mod(a, p):
        """a square root of a modulo the odd prime p (Tonelli and Shanks), or None"""
        a %= p
        if a == 0:
            return 0
        if pow(a, (p - 1) // 2, p) != 1:
            return None
        q, s = p - 1, 0
        while q % 2 == 0:
            q //= 2
            s += 1
        z = 2
        while pow(z, (p - 1) // 2, p) != p - 1:
            z += 1
        m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
        while t != 1:
            i, t2 = 0, t
            while t2 != 1:
                t2 = t2 * t2 % p
                i += 1
            b = pow(c, 1 << (m - i - 1), p)
            m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
        assert r * r % p == a
        return r

    def pell_reps(p, fmax):
        """all (e, f) natural with e^2 = p + 2 f^2 and f <= fmax"""
        out = []
        for f in range(fmax + 1):
            e2 = p + 2 * f * f
            e = isqrt(e2)
            if e * e == e2:
                out.append((e, f))
        return out

    # Euler criterion against the literal definition
    lit = 0
    for p in primes:
        if p >= 3000:
            break
        for a in (2, -4, 3, 5, 6, 7, 10, 11):
            for k in (2, 4, 8):
                assert kth_power(a, k, p) == kth_power_literal(a, k, p), (a, k, p)
                lit += 1
    counts["Euler criterion = literal search over ZMod p (p < 3000)"] = lit

    # theorem 1
    c1 = 0
    for p in primes:
        if p % 4 != 1:
            continue
        lhs = kth_power(2, 4, p)
        assert lhs == bool(reps(p, 64)), p
        c1 += 1
    counts["theorem 1, primes p = 1 mod 4 below %d" % N] = c1

    # theorem 2
    c2 = 0
    for p in primes:
        if p % 8 != 1:
            continue
        assert kth_power(-4, 8, p) == bool(reps(p, 32)), p
        c2 += 1
    counts["theorem 2, primes p = 1 mod 8 below %d" % N] = c2

    # theorem 3: every odd prime below N3
    N3 = 30000
    c3 = 0
    for p in primes:
        if p >= N3:
            break
        lhs = kth_power(2, 4, p)
        if p % 8 in (3, 5):
            # 2 is not a square, so e^2 = 2 f^2 mod p forces p | e, f and p^2 | p
            assert pow(2, (p - 1) // 2, p) == p - 1 and not lhs
            assert not pell_reps(p, 3 * isqrt(p) + 10)
        else:
            R = pell_reps(p, 40 * isqrt(p) + 40)   # several orbits of the unit 3 + 2 sqrt 2
            assert R, p
            classes = {e % 8 in (1, 3) for e, f in R}
            if p % 8 == 1:
                assert len(classes) == 1, p          # the class of e is an invariant
                assert lhs == classes.pop(), p
                for e, f in R:                         # golden route: 2^((p-1)/4) = J(-2|e)
                    assert pow(2, (p - 1) // 4, p) == jac_odd(-2, e) % p, p
            else:                                      # p = 7 mod 8: both classes occur
                assert lhs and classes == {True, False}, p
        c3 += 1
    counts["theorem 3, odd primes below %d" % N3] = c3

    # theorem 4
    N4 = 50000
    c4 = 0
    for p in primes:
        if p >= N4:
            break
        if p % 4 != 1:
            continue
        for q in range(2, 160):
            if q % 4 not in (2, 3):
                continue
            for c, d in reps(p, q):
                assert kth_power(q, 4, p) == (jacobi_mathlib(q, c) == 1), (p, q, c, d)
                c4 += 1
    counts["theorem 4, (p, q, c, d) with p = 1 mod 4 < %d and q < 160" % N4] = c4

    # theorem 5
    c5 = 0
    for p in primes:
        if p % 8 != 1:
            continue
        s = sqrt_mod(2, p)
        lhs = pow((1 + s) % p, (p - 1) // 2, p) == 1
        assert lhs == (pow((1 - s) % p, (p - 1) // 2, p) == 1)   # independent of s
        assert lhs == bool(reps(p, 32)), p
        c5 += 1
    counts["theorem 5, primes p = 1 mod 8 below %d" % N] = c5

    # literal left sides for small p (theorems 1, 2, 3, 5)
    lit = 0
    for p in primes:
        if p >= 1500:
            break
        L = [x * x % p for x in range(p)]
        if p % 4 == 1:
            assert kth_power_literal(2, 4, p) == bool(reps(p, 64))
            lit += 1
        if p % 8 == 1:
            assert kth_power_literal(-4, 8, p) == bool(reps(p, 32))
            sq = set(L)
            lhs5 = any(L[s] == 2 % p and (1 + s) % p in sq for s in range(p))
            assert lhs5 == bool(reps(p, 32))
            lit += 2
    counts["literal left sides of theorems 1, 2, 5 for p < 1500"] = lit

    # data of the golden route
    route = 0
    for p in primes:
        if p % 4 != 1:
            continue
        for a, b in reps(p, 1):
            if a % 2 == 0 or b == 0:
                continue
            # Dirichlet: J(a + b | p) = J(2 | a + b), from 2p = (a + b)^2 + (a - b)^2
            assert jac_odd(a + b, p) == jac_odd(2, a + b)
            if p % 8 == 1:
                assert pow(2, (p - 1) // 4, p) == (1 if (b // 4) % 2 == 0 else p - 1)
                # the quadratic character of 1 + i, i = a / b, is J(2 | a + b)
                i = a * pow(b, -1, p) % p
                assert pow(-4 % p, (p - 1) // 8, p) == jac_odd(2, a + b) % p
                assert pow((1 + i) % p, (p - 1) // 2, p) == jac_odd(2, a + b) % p
            route += 1
        if p < 30000:
            for q in range(1, 40):
                for c, d in reps(p, q):
                    if c % 2 == 0 or d == 0 or gcd(c, q * d) != 1:
                        continue
                    v2, dd = 0, d
                    while dd % 2 == 0:
                        dd //= 2
                        v2 += 1
                    rhs = jac_odd(q, c) * jac_odd(2, p) ** v2
                    assert pow(-q % p, (p - 1) // 4, p) == rhs % p, (p, q, c, d)
                    route += 1
        if p % 8 == 1 and p < 30000:
            s = sqrt_mod(2, p)
            chi = pow((1 + s) % p, (p - 1) // 2, p)
            for e, f in pell_reps(p, 6 * isqrt(p) + 10):
                if f == 0:
                    continue
                assert chi == jac_odd(-1, e + f) % p
                route += 1
    for p in primes:
        if p >= 30000:
            break
        if p % 8 in (1, 3):
            assert reps(p, 2), p
            route += 1
        if p % 8 in (1, 7):
            assert pell_reps(p, isqrt(p) + 2), p     # Thue: a representation with f <= sqrt p
            route += 1
        if p % 8 == 7:
            e, f = pell_reps(p, isqrt(p) + 2)[0]
            e2, f2 = 3 * e + 4 * f, 2 * e + 3 * f        # multiply by the unit 3 + 2 sqrt 2
            assert e2 * e2 == p + 2 * f2 * f2 and (e % 8 in (1, 3)) != (e2 % 8 in (1, 3))
            route += 1
    counts["golden-route data (Dirichlet's formulas, representations, unit step)"] = route

    # witnesses: dropping a hypothesis makes the statement false
    def rhs_sum(n, q):
        return bool(reps(n, q))

    w = 0
    # theorem 1: p = 7 (p = 3 mod 4), n = 65 (composite)
    assert kth_power_literal(2, 4, 7) and not rhs_sum(7, 64)
    assert not kth_power_literal(2, 4, 65) and rhs_sum(65, 64)
    w += 2
    # theorem 2: p = 5 (p = 5 mod 8), n = 33 (composite)
    assert kth_power_literal(-4, 8, 5) and not rhs_sum(5, 32)
    assert not kth_power_literal(-4, 8, 33) and rhs_sum(33, 32)
    w += 2
    # theorem 3: p = 2 (even: e^2 = 2 + 2 f^2 forces e even), n = 9 (composite, e = 3, f = 0)
    assert kth_power_literal(2, 4, 2)
    assert all((2 + 2 * f * f) % 2 == 0 for f in range(100))
    assert not kth_power_literal(2, 4, 9) and 3 * 3 == 9 + 2 * 0 and 3 % 8 == 3
    w += 2
    # theorem 4: (n, q, c, d) = (49, 3, 1, 4) composite, (7, 3, 2, 1) with 7 = 3 mod 4,
    # (61, 5, 4, 3) with q = 1 mod 4
    for (n, q, c, d) in ((49, 3, 1, 4), (7, 3, 2, 1), (61, 5, 4, 3)):
        assert n == c * c + q * d * d
        assert not kth_power_literal(q, 4, n) and jacobi_mathlib(q, c) == 1, (n, q, c, d)
        w += 1
    # theorem 5: p = 7 (s = 3, t = 2), n = 33 (2 is not a square mod 3)
    assert 3 * 3 % 7 == 2 and 2 * 2 % 7 == (1 + 3) % 7 and not rhs_sum(7, 32)
    assert not any(s * s % 33 == 2 for s in range(33)) and rhs_sum(33, 32)
    w += 2
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

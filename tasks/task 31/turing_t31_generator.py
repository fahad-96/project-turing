#!/usr/bin/env python3
"""Project Turing, task 31 generator (proof writing): coefficients of binary and ternary
cyclotomic polynomials (Migotti 1883, Bang 1895, Carlitz 1966, Lenstra 1979, Lam and Leung 1996,
Kaplan 2007, Gallot and Moree 2009).

a_n(k) = coefficient of x^k in the cyclotomic polynomial Phi_n(x); p, q, r primes, k >= 0.
Theorems:
  1. p != q: every partial sum a_pq(0) + ... + a_pq(k) is 0 or 1
  2. u < q, v < p, u p = 1 mod q, v q = 1 mod p: exactly u v coefficients of Phi_pq equal 1
  3. |a_pqr(k)| <= p - 1
  4. r = 1 or -1 mod p q: every a_pqr(k) is -1, 0 or 1
  5. |a_pqr(k + 1) - a_pqr(k)| <= 1

Writes, next to this script:
  task31_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic. Phi_n is computed from the product formula
Phi_n(x) = prod_{d | n} (1 - x^d)^mu(n/d) (n > 1) and compared with the long division of
x^n - 1 by the Phi_d, d | n, d < n, for n <= 400. Then:
  - theorems 1 and 2 for all primes p, q < 300 with p q <= 30,000 (both orders);
  - theorems 3 and 5 for all prime triples (repetitions and the prime 2 allowed) with
    p q r <= 40,000, in every order;
  - theorem 4 for all prime triples with r = +-1 mod p q and p q r <= 150,000;
  - the data of the planned golden route: the Lam-Leung expansion of Phi_pq (positions of the
    coefficients 1 and -1), the identity Phi_pq (x^p - 1)(x^q - 1) = (x^pq - 1)(x - 1),
    Kaplan's lemma for every ternary coefficient of the checked triples p < q < r odd, and the
    reductions Phi_2m(x) = Phi_m(-x) (m odd) and Phi_pm(x) = Phi_m(x^p) (p | m);
  - a numeric witness for every hypothesis: dropping it makes the statement false.
There is no finite search space: p, q, r, k are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t31_generator.py
"""

TASK = 31
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

THEOREMS = [
    ("sum_range_coeff_cyclotomic_mul_mem",
     "(p q : Nat) (hp : p.Prime) (hq : q.Prime)\n    (hpq : Not (p = q)) (k : Nat)",
     "    Membership.mem ({0, 1} : Finset Int)\n"
     "      (Finset.sum (Finset.range (k + 1))\n        (fun i => (Polynomial.cyclotomic (p * q) Int).coeff i))"),
    ("card_coeff_cyclotomic_mul_eq_one",
     "(p q u v : Nat) (hp : p.Prime) (hq : q.Prime)\n"
     "    (hu : u * p % q = 1) (hv : v * q % p = 1) (huq : u < q) (hvp : v < p)",
     "    (Finset.filter (fun k => (Polynomial.cyclotomic (p * q) Int).coeff k = 1)\n"
     "      (Finset.range (p * q))).card = u * v"),
    ("abs_coeff_cyclotomic_mul_mul_le",
     "(p q r : Nat) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)\n    (k : Nat)",
     "    |(Polynomial.cyclotomic (p * q * r) Int).coeff k| <= (p : Int) - 1"),
    ("coeff_cyclotomic_mul_mul_mem_of_mod",
     "(p q r : Nat) (hp : p.Prime) (hq : q.Prime)\n"
     "    (hr : r.Prime) (hr' : r % (p * q) = 1 \\/ r % (p * q) + 1 = p * q) (k : Nat)",
     "    Membership.mem ({-1, 0, 1} : Finset Int) ((Polynomial.cyclotomic (p * q * r) Int).coeff k)"),
    ("abs_coeff_succ_sub_coeff_cyclotomic_le",
     "(p q r : Nat) (hp : p.Prime) (hq : q.Prime)\n    (hr : r.Prime) (k : Nat)",
     "    |(Polynomial.cyclotomic (p * q * r) Int).coeff (k + 1) -\n"
     "      (Polynomial.cyclotomic (p * q * r) Int).coeff k| <= 1"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. For $n \ge 1$ write $\Phi_n(x) = \sum_{k \ge 0} a_n(k)\, x^k$ for the $n$-th cyclotomic polynomial, so $a_n(k)$ is an integer and $a_n(k) = 0$ for $k > \varphi(n)$. Below $p, q, r$ are primes, not necessarily distinct, and $k \ge 0$.

1. If $p \ne q$, then every partial sum $a_{pq}(0) + a_{pq}(1) + \dots + a_{pq}(k)$ is $0$ or $1$. In other words, every coefficient of $\Phi_{pq}$ is $-1$, $0$ or $1$, and the nonzero ones alternate $1, -1, 1, \dots$, starting with $1$.
2. Let $u, v$ be natural numbers with $u < q$, $v < p$, $u p \equiv 1 \pmod q$ and $v q \equiv 1 \pmod p$ (such $u, v$ exist exactly when $p \ne q$). Then exactly $u v$ coefficients of $\Phi_{pq}$ equal $1$.
3. Every coefficient of $\Phi_{pqr}$ satisfies $|a_{pqr}(k)| \le p - 1$.
4. If $r \equiv \pm 1 \pmod{p q}$, then every coefficient of $\Phi_{pqr}$ is $-1$, $0$ or $1$.
5. Neighbouring coefficients of $\Phi_{pqr}$ differ by at most $1$, that is, $|a_{pqr}(k + 1) - a_{pqr}(k)| \le 1$.

Lean statement. The coefficient $a_n(k)$ is `(Polynomial.cyclotomic n Int).coeff k`, and `|x|` is the absolute value of an integer. In theorem 4 the condition $r \equiv -1 \pmod{p q}$ appears as `r % (p * q) + 1 = p * q`. A set of values such as $\{-1, 0, 1\}$ appears as a `Finset Int` together with `Membership.mem`. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    from math import isqrt, gcd
    import numpy as np

    counts = {}

    def is_prime(m):
        return m > 1 and all(m % d for d in range(2, isqrt(m) + 1))

    def mobius(n):
        m, k, p = n, 0, 2
        while p * p <= m:
            if m % p == 0:
                m //= p
                if m % p == 0:
                    return 0
                k += 1
            p += 1
        if m > 1:
            k += 1
        return -1 if k % 2 else 1

    def phi(n):
        res, m, p = n, n, 2
        while p * p <= m:
            if m % p == 0:
                while m % p == 0:
                    m //= p
                res -= res // p
            p += 1
        if m > 1:
            res -= res // m
        return res

    cache = {}

    def cyc(n):
        """coefficients a_n(0..phi(n)) as a numpy int64 array (exact: all values are tiny)"""
        if n in cache:
            return cache[n]
        if n == 1:
            res = np.array([-1, 1], dtype=np.int64)
        else:
            N = n + 1
            a = np.zeros(N, dtype=np.int64)
            a[0] = 1
            for d in range(1, n + 1):
                if n % d:
                    continue
                mu = mobius(n // d)
                if mu == 1:
                    a[d:] = a[d:] - a[:N - d]
                elif mu == -1:
                    m = -(-N // d)
                    b = np.zeros(m * d, dtype=np.int64)
                    b[:N] = a
                    a = b.reshape(m, d).cumsum(axis=0).reshape(-1)[:N]
            f = phi(n)
            assert not a[f + 1:].any() and a[f] == 1
            res = a[:f + 1]
        if n <= 5000:
            cache[n] = res
        return res

    def coeff(n, k):
        a = cyc(n)
        return int(a[k]) if k < len(a) else 0

    # the product formula against long division
    def cyc_div(n, memo={}):
        if n in memo:
            return memo[n]
        num = [-1] + [0] * (n - 1) + [1]
        for d in range(1, n):
            if n % d == 0:
                den = cyc_div(d)
                quo = [0] * (len(num) - len(den) + 1)
                rem = num[:]
                for i in range(len(quo) - 1, -1, -1):
                    c = rem[i + len(den) - 1]
                    quo[i] = c
                    if c:
                        for j, y in enumerate(den):
                            rem[i + j] -= c * y
                assert not any(rem[:len(den) - 1])
                num = quo
        memo[n] = num
        return num

    c0 = 0
    for n in range(1, 401):
        assert list(cyc(n)) == cyc_div(n), n
        c0 += 1
    counts["product formula = long division for n <= 400"] = c0

    primes = [p for p in range(2, 300) if is_prime(p)]

    # theorems 1 and 2, with the Lam-Leung expansion
    c1 = c2 = route = 0
    for p in primes:
        for q in primes:
            if p == q or p * q > 30000:
                continue
            a = cyc(p * q)
            s = np.cumsum(a)
            assert set(np.unique(s).tolist()) <= {0, 1}, (p, q)
            c1 += 1
            u, v = pow(p, -1, q), pow(q, -1, p)
            assert int((a == 1).sum()) == u * v, (p, q)
            c2 += 1
            # Lam-Leung: a = 1 exactly at i p + j q (i < u, j < v), a = -1 exactly at
            # i p + j q - p q (u <= i < q, v <= j < p), 0 elsewhere
            plus = {i * p + j * q for i in range(u) for j in range(v)}
            minus = {i * p + j * q - p * q for i in range(u, q) for j in range(v, p)}
            assert plus == set(np.nonzero(a == 1)[0].tolist())
            assert minus == set(np.nonzero(a == -1)[0].tolist())
            route += 1
    counts["theorem 1, distinct primes p, q < 300 with p q <= 30,000"] = c1
    counts["theorem 2, the same pairs"] = c2

    # theorems 3 and 5 for all prime triples, every order
    c3 = 0
    for p in primes:
        for q in primes:
            for r in primes:
                n = p * q * r
                if n > 40000:
                    continue
                a = cyc(n)
                assert int(np.abs(a).max()) <= p - 1, (p, q, r)
                ext = np.concatenate([a, [0]])
                assert int(np.abs(np.diff(ext)).max()) <= 1, (p, q, r)
                c3 += 1
    counts["theorems 3 and 5, prime triples with p q r <= 40,000, every order"] = c3

    # theorem 4: r = +-1 mod p q
    c4 = 0
    for p in primes:
        for q in primes:
            if p * q > 400:
                continue
            for r in range(2, 150000 // (p * q) + 1):
                if is_prime(r) and (r % (p * q) == 1 or r % (p * q) + 1 == p * q):
                    a = cyc(p * q * r)
                    assert int(np.abs(a).max()) <= 1, (p, q, r)
                    c4 += 1
    counts["theorem 4, prime triples with r = +-1 mod p q and p q r <= 150,000"] = c4

    # golden route: Kaplan's lemma for p < q < r odd primes
    def kaplan(p, q, r, j):
        rinv = pow(r, -1, p * q)
        b = lambda i: coeff(p * q, i) if r * i <= j else 0
        f = lambda m: ((j - m) * rinv) % (p * q)
        return sum(b(f(m)) - b(f(m + q)) for m in range(p))

    for p in primes:
        for q in primes:
            for r in primes:
                if not (2 < p < q < r) or p * q * r > 8000:
                    continue
                a = cyc(p * q * r)
                for j in range(len(a)):
                    assert kaplan(p, q, r, j) == int(a[j]), (p, q, r, j)
                route += 1
    # identity for Phi_pq and the reductions
    for p in primes[:12]:
        for q in primes[:12]:
            if p == q:
                continue
            lhs = np.convolve(np.convolve(cyc(p * q), np.r_[-1, [0] * (p - 1), 1]),
                              np.r_[-1, [0] * (q - 1), 1])
            rhs = np.convolve(np.r_[-1, [0] * (p * q - 1), 1], np.r_[-1, 1])
            assert (lhs == rhs).all()
            route += 1
    for m in range(3, 400, 2):
        a2, a1 = cyc(2 * m), cyc(m)
        assert (a2 == a1 * (-1) ** np.arange(len(a1))).all()
        route += 1
    for m in range(2, 300):
        for p in primes[:8]:
            if m % p == 0 and m * p <= 3000:
                a = cyc(p * m)
                expect = np.zeros(len(a), dtype=np.int64)
                expect[::p] = cyc(m)
                assert (a == expect).all()
                route += 1
    counts["golden-route data (Lam-Leung, Kaplan's lemma, identity, reductions)"] = route

    # witnesses
    w = 0
    s4 = np.cumsum(cyc(4))                       # theorem 1, p = q = 2
    assert not set(np.unique(s4).tolist()) <= {0, 1}
    s105 = np.cumsum(cyc(105))                   # theorem 1, q = 35 not prime
    assert not set(np.unique(s105).tolist()) <= {0, 1}
    w += 3                                       # (p, q) = (35, 3) is the same polynomial
    a12 = cyc(12)                 # theorem 2 with p = 4 (u = 1, v = 3) or q = 4 (u = 3, v = 1)
    assert int((a12 == 1).sum()) == 2
    assert 1 * 4 % 3 == 1 and 3 * 3 % 4 == 1 and 1 < 3 and 3 < 4 and 1 * 3 != 2
    assert 3 * 3 % 4 == 1 and 1 * 4 % 3 == 1 and 3 < 4 and 1 < 3 and 3 * 1 != 2
    a15 = cyc(15)                 # theorem 2 with (p, q) = (3, 5): u = 2, v = 2, four 1s
    assert int((a15 == 1).sum()) == 4 == 2 * 2
    assert (2 + 5) * 3 % 5 == 1 and (2 + 5) * 2 != 4      # u + q breaks only u < q
    assert (2 + 3) * 5 % 3 == 1 and 2 * (2 + 3) != 4      # v + p breaks only v < p
    assert 1 * 3 % 5 != 1 and 1 < 5 and 1 * 2 != 4       # u = 1 breaks only u p = 1 mod q
    assert 1 * 5 % 3 != 1 and 1 < 3 and 2 * 1 != 4       # v = 1 breaks only v q = 1 mod p
    w += 6
    assert int(np.abs(cyc(210)).max()) == 2      # theorem 3: (2, 15, 7) or (2, 7, 15)
    assert int(np.abs(cyc(15)).max()) == 1 > 1 - 1   # theorem 3: p = 1, q = 3, r = 5
    w += 3
    assert int(np.abs(cyc(105)).max()) == 2 and 7 % 15 not in (1, 14)    # theorem 4: (3, 5, 7)
    assert int(np.abs(cyc(210)).max()) == 2 and 14 % 15 + 1 == 15        # r = 14
    assert int(np.abs(cyc(15 * 7 * 211)).max()) == 2 and 211 % 105 == 1  # p = 15, or q = 15
    w += 4
    assert int(np.abs(np.diff(cyc(15))).max()) == 2                      # theorem 5: r = 1
    assert int(np.abs(np.diff(cyc(210))).max()) == 3                     # theorem 5: 35 or 15
    w += 3
    counts["witnesses for the 19 hypotheses (each one false when dropped)"] = w
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

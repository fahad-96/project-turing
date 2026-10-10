#!/usr/bin/env python3
"""Project Turing, task 24 generator (proof writing): extremal and fixed-point values of the
Pisano period pi(n) and of the entry point z(n) of the Fibonacci numbers modulo n
(Wall 1960, Fulton and Morris 1969, Salle 1975, Freyd and Brown 1992, Marques 2012).

pi(n) = least k >= 1 with F_k = 0 and F_(k+1) = 1 (mod n);  z(n) = least k >= 1 with n | F_k.
Theorems: pi(n) <= 6 n;  pi(n) = 6 n iff n = 2 * 5^j (j >= 1);  pi(n) = n iff n = 1 or
n = 24 * 5^j;  z(n) = 2 n iff n = 6 * 5^j;  z(n) = n iff n = 5^j or n = 12 * 5^j.

Writes, next to this script:
  task24_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic:
  - pi(n) and z(n) by direct iteration of (F_k, F_(k+1)) mod n for every n <= 20000, and all five
    statements (both directions) for every n <= 20000;
  - the left-hand sides evaluated literally, as written in Lean (remainders, `1 % n`, the
    quantifier over k), for every n <= 1500, and compared with the pi / z evaluation;
  - the five families beyond the range: pi or z computed directly for n = 2 * 5^j (j <= 7),
    24 * 5^j (j <= 5), 6 * 5^j (j <= 7), 5^j (j <= 8), 12 * 5^j (j <= 6);
  - the data of the planned golden route: z(p) | p - (5/p) and pi(p) | p - 1 or 2 (p + 1) for
    primes p < 5000; z(p^e) | p^(e-1) z(p) and pi(p^e) | p^(e-1) pi(p) for p^e <= 20000; the
    exact values at powers of 2, 3, 5; z and pi of coprime products are lcm's; pi / z in
    {1, 2, 4}, = 4 iff z(n) is odd (n >= 3);
  - for each theorem, a witness showing that each hypothesis (0 < n, 0 < j, the case n = 1,
    each of the two families, `1 % n` instead of `1`, `<=` instead of `<`) cannot be dropped.
There is no finite search space: n and j are unbounded natural numbers.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t24_generator.py
"""

TASK = 24
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

THEOREMS = [
    ("pisano_le_six_mul",
     "(n : Nat) (hn : 0 < n)", """\
    exists k : Nat, 0 < k /\\ k <= 6 * n /\\ Nat.fib k % n = 0 /\\ Nat.fib (k + 1) % n = 1 % n"""),
    ("pisano_eq_six_mul_iff",
     "(n : Nat) (hn : 0 < n)", """\
    (Nat.fib (6 * n) % n = 0 /\\ Nat.fib (6 * n + 1) % n = 1 % n /\\
      forall k : Nat, 0 < k -> k < 6 * n ->
        Not (Nat.fib k % n = 0 /\\ Nat.fib (k + 1) % n = 1 % n)) <->
      exists j : Nat, 0 < j /\\ n = 2 * 5 ^ j"""),
    ("pisano_eq_self_iff",
     "(n : Nat) (hn : 0 < n)", """\
    (Nat.fib n % n = 0 /\\ Nat.fib (n + 1) % n = 1 % n /\\
      forall k : Nat, 0 < k -> k < n ->
        Not (Nat.fib k % n = 0 /\\ Nat.fib (k + 1) % n = 1 % n)) <->
      (n = 1 \\/ exists j : Nat, n = 24 * 5 ^ j)"""),
    ("entry_eq_two_mul_iff",
     "(n : Nat) (hn : 0 < n)", """\
    (Nat.fib (2 * n) % n = 0 /\\ forall k : Nat, 0 < k -> k < 2 * n -> 0 < Nat.fib k % n) <->
      exists j : Nat, n = 6 * 5 ^ j"""),
    ("entry_eq_self_iff",
     "(n : Nat) (hn : 0 < n)", """\
    (Nat.fib n % n = 0 /\\ forall k : Nat, 0 < k -> k < n -> 0 < Nat.fib k % n) <->
      ((exists j : Nat, n = 5 ^ j) \\/ exists j : Nat, n = 12 * 5 ^ j)"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. $F_k$ is the $k$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$, $F_{k+2} = F_{k+1} + F_k$; `Nat.fib k` in Mathlib). For an integer $n \ge 1$ let $\pi(n)$, the Pisano period, be the least $k \ge 1$ with $F_k \equiv 0$ and $F_{k+1} \equiv 1 \pmod n$, and let $z(n)$, the entry point, be the least $k \ge 1$ with $n \mid F_k$. In the Lean statements these conditions are written with remainders, and $1 \bmod n$ is written `1 % n` so that $n = 1$ is included. All variables are natural numbers. For every $n \ge 1$:

1. $\pi(n) \le 6 n$.
2. $\pi(n) = 6 n$ if and only if $n = 2 \cdot 5^j$ for some $j \ge 1$.
3. $\pi(n) = n$ if and only if $n = 1$ or $n = 24 \cdot 5^j$ for some $j \ge 0$.
4. $z(n) = 2 n$ if and only if $n = 6 \cdot 5^j$ for some $j \ge 0$.
5. $z(n) = n$ if and only if $n = 5^j$ or $n = 12 \cdot 5^j$ for some $j \ge 0$.

Lean statement. The file `@FILE@` must contain the five theorems, stated exactly as below, with each `sorry` replaced by a complete proof:
"""

EXTRA_RULE = """Nothing may be declared inside the namespace `@NS@` that shadows a Mathlib name: every name used in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements and of the data of the planned proof."""
    from math import gcd

    NMAX = 20000
    LIT = 1500

    def lmod(a, n):
        """Lean's `a % n` on Nat (a % 0 = a)."""
        return a if n == 0 else a % n

    def z_of(n):
        if n == 1:
            return 1
        a, b, k = 1, 1, 1  # F_k, F_(k+1) mod n
        while a % n:
            a, b, k = b, (a + b) % n, k + 1
        return k

    def pi_of(n):
        if n == 1:
            return 1
        a, b, k = 1, 1, 1
        while not (a == 0 and b == 1):
            a, b, k = b, (a + b) % n, k + 1
        return k

    def fam(n, base, jmin=0):
        if n % base:
            return False
        q, j = n // base, 0
        while q % 5 == 0:
            q //= 5
            j += 1
        return q == 1 and j >= jmin

    rhs = [
        lambda n: True,
        lambda n: fam(n, 2, 1),
        lambda n: n == 1 or fam(n, 24),
        lambda n: fam(n, 6),
        lambda n: fam(n, 1) or fam(n, 12),
    ]

    def lhs_from(n, p, z):
        return [p <= 6 * n, p == 6 * n, p == n, z == 2 * n, z == n]

    Z = [0] * (NMAX + 1)
    P = [0] * (NMAX + 1)
    checks = 0
    for n in range(1, NMAX + 1):
        Z[n], P[n] = z_of(n), pi_of(n)
        lh = lhs_from(n, P[n], Z[n])
        for t in range(5):
            assert lh[t] == rhs[t](n), (t + 1, n)
            checks += 1
    counts = {"pi(n), z(n) computed and theorems 1-5 checked for 1 <= n <= %d" % NMAX: checks}

    # literal Lean semantics of the left-hand sides for small n
    def lit_lhs(n):
        f = [0, 1]
        while len(f) < 6 * n + 3:
            f.append(f[-1] + f[-2])
        per = lambda k: lmod(f[k], n) == 0 and lmod(f[k + 1], n) == lmod(1, n)
        t1 = any(per(k) for k in range(1, 6 * n + 1))
        t2 = per(6 * n) and all(not per(k) for k in range(1, 6 * n))
        t3 = per(n) and all(not per(k) for k in range(1, n))
        t4 = lmod(f[2 * n], n) == 0 and all(lmod(f[k], n) > 0 for k in range(1, 2 * n))
        t5 = lmod(f[n], n) == 0 and all(lmod(f[k], n) > 0 for k in range(1, n))
        return [t1, t2, t3, t4, t5]

    lit = 0
    for n in range(1, LIT + 1):
        a = lit_lhs(n)
        assert a == lhs_from(n, P[n], Z[n]), n
        lit += 5
    counts["left-hand sides evaluated literally (Lean remainders, 1 %% n) for n <= %d" % LIT] = lit

    # the families beyond the range
    fam_checks = 0
    for j in range(1, 8):
        n = 2 * 5 ** j
        assert pi_of(n) == 6 * n
        fam_checks += 1
    for j in range(0, 6):
        n = 24 * 5 ** j
        assert pi_of(n) == n
        fam_checks += 1
    for j in range(0, 8):
        n = 6 * 5 ** j
        assert z_of(n) == 2 * n
        fam_checks += 1
    for j in range(0, 9):
        n = 5 ** j
        assert z_of(n) == n
        fam_checks += 1
    for j in range(0, 7):
        n = 12 * 5 ** j
        assert z_of(n) == n
        fam_checks += 1
    counts["family members checked directly up to n = 468750"] = fam_checks

    # golden-route data
    def is_prime(m):
        if m < 2:
            return False
        d = 2
        while d * d <= m:
            if m % d == 0:
                return False
            d += 1
        return True

    route = 0
    for p in range(3, 5000):
        if not is_prime(p) or p == 5:
            continue
        leg = 1 if p % 5 in (1, 4) else -1
        zp, pp = z_of(p), pi_of(p)
        assert (p - leg) % zp == 0
        if leg == 1:
            assert (p - 1) % pp == 0
        else:
            assert (2 * (p + 1)) % pp == 0 and (p + 1) % pp != 0
        route += 1
    for p in range(2, NMAX + 1):
        if not is_prime(p):
            continue
        q, e = p, 1
        while q * p <= NMAX:
            q, e = q * p, e + 1
            assert (p ** (e - 1) * Z[p]) % Z[q] == 0 and (p ** (e - 1) * P[p]) % P[q] == 0
            route += 1
    for a in range(1, 15):
        q = 2 ** a
        assert Z[q] == (3 if a == 1 else 6 if a == 2 else 3 * 2 ** (a - 2))
        assert P[q] == 3 * 2 ** (a - 1)
        route += 1
    for b in range(1, 10):
        q = 3 ** b
        assert Z[q] == 4 * 3 ** (b - 1) and P[q] == 8 * 3 ** (b - 1)
        route += 1
    for c in range(1, 7):
        q = 5 ** c
        assert Z[q] == q and P[q] == 4 * q
        route += 1
    for a in range(1, 300):
        for b in range(a + 1, 300):
            if gcd(a, b) == 1 and a * b <= NMAX:
                l1 = Z[a] * Z[b] // gcd(Z[a], Z[b])
                l2 = P[a] * P[b] // gcd(P[a], P[b])
                assert Z[a * b] == l1 and P[a * b] == l2
                route += 1
    for n in range(1, NMAX + 1):
        w = P[n] // Z[n]
        assert P[n] % Z[n] == 0 and w in (1, 2, 4)
        if n >= 3:
            assert (w == 4) == (Z[n] % 2 == 1)
        route += 1
    counts["golden-route data (apparition, lifting, prime powers, lcm, pi / z)"] = route

    # witnesses: every hypothesis is needed (Lean semantics at n = 0 included)
    def lhs_lean(n):
        if n == 0:
            f0, f1, f6, f61 = 0, 1, 0, 1  # fib 0, fib 1, fib (6 * 0), fib (6 * 0 + 1)
            t1 = False  # no k with 0 < k <= 0
            t2 = lmod(f6, 0) == 0 and lmod(f61, 0) == lmod(1, 0)
            t3 = lmod(f0, 0) == 0 and lmod(f1, 0) == lmod(1, 0)
            t4 = lmod(0, 0) == 0
            t5 = lmod(0, 0) == 0
            return [t1, t2, t3, t4, t5]
        return lit_lhs(n)

    wit = 0
    l0 = lhs_lean(0)
    for t in range(5):
        r0 = [True, False, False, False, False][t]  # right-hand sides at n = 0
        assert l0[t] != r0, ("0 < n needed", t + 1)
        wit += 1
    assert not lit_lhs(2)[1] and fam(2, 2, 0)          # theorem 2 needs 0 < j
    assert lit_lhs(1)[2] and not fam(1, 24)            # theorem 3 needs the case n = 1
    assert lit_lhs(5)[4] and fam(5, 1) and not fam(5, 12)    # theorem 5 needs 5^j
    assert lit_lhs(12)[4] and fam(12, 12) and not fam(12, 1)  # theorem 5 needs 12 * 5^j
    assert not any(lmod(f, 1) == 1 for f in range(100))  # `= 1` instead of `= 1 % n` fails at n = 1
    assert P[1] == 1 and Z[1] == 1
    assert P[10] == 60                                 # theorem 1 is sharp: `k <= 6 n` needed
    assert Z[6] == 12                                  # theorem 4: z(6) = 2 * 6
    wit += 8
    counts["witnesses for the hypotheses and sharpness"] = wit
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

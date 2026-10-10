#!/usr/bin/env python3
"""Project Turing, task 29 generator (proof writing): signs of arithmetic permutations
(Zolotarev 1872, Lerch 1896, Frobenius 1914).

Theorems (sgn = sign of a permutation, mu_a = multiplication by a on Z/n):
  1. n odd, gcd(a, n) = 1:  sgn(mu_a on Z/n) = J(a | n)
  2. n even, gcd(a, n) = 1: sgn(mu_a on Z/n) = 1 if n = 2 mod 4, (-1)^((a-1)/2) if 4 | n
  3. u a unit mod n: sgn(x -> u x on (Z/n)^*) = -1  <->  n in {4, p^k, 2 p^k} (p odd prime,
     k >= 1) and u is not a square in (Z/n)^*
  4. p prime, x -> x^k a bijection of Z/p: sgn = -1  <->  p = 1 mod 4 and k = 3 mod 4
  5. the transpose i n + j -> j m + i of {0, ..., m n - 1}: sgn = (-1)^(C(m,2) C(n,2))

Writes, next to this script:
  task29_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic (signs from the cycle decomposition):
  - theorems 1 and 2 for every n < 400 and every a < 2n coprime to n;
  - theorem 3 for every n < 300 and every unit u, squares found by listing all of them;
  - theorem 4 for every prime p < 400 and every k < 3p, bijectivity tested directly;
  - theorem 5 for all m, n <= 14, and the sign of the transpose computed independently by
    counting inversions;
  - the data of the planned golden route: sgn = (-1)^(size - number of cycles), the
    multiplicativity of the sign under the Chinese remainder theorem, the values on Z/p^k
    and Z/2^k, the discrete logarithm that turns x -> x^k on (Z/p)^* into y -> k y on
    Z/(p - 1), the 2-parts of orders that decide theorem 3, and the inversion count
    C(m,2) C(n,2) of the transpose;
  - a numeric witness for every hypothesis: dropping it makes the statement false.
There is no finite search space: n, p, k, m are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t29_generator.py
"""

TASK = 29
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

THEOREMS = [
    ("sign_mulLeft_eq_jacobiSym",
     "(n a : Nat) [NeZero n] (hn : n % 2 = 1) (ha : Nat.Coprime a n)",
     "    (Equiv.Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) : Int) = jacobiSym a n"),
    ("sign_mulLeft_of_even",
     "(n a : Nat) [NeZero n] (hn : n % 2 = 0) (ha : Nat.Coprime a n)",
     "    (Equiv.Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) : Int) =\n"
     "      if n % 4 = 2 then 1 else if a % 4 = 1 then 1 else -1"),
    ("sign_mulLeft_units_eq_neg_one_iff",
     "(n : Nat) [NeZero n] (u : Units (ZMod n))",
     "    Equiv.Perm.sign (Equiv.mulLeft u) = -1 <->\n"
     "      (n = 4 \\/\n"
     "        exists p k : Nat, p.Prime /\\ p % 2 = 1 /\\ 0 < k /\\ (n = p ^ k \\/ n = 2 * p ^ k)) /\\\n"
     "        Not (IsSquare u)"),
    ("sign_ofBijective_pow",
     "(p k : Nat) [NeZero p] (hp : p.Prime)\n"
     "    (hk : Function.Bijective (fun x : ZMod p => x ^ k))",
     "    (Equiv.Perm.sign (Equiv.ofBijective (fun x : ZMod p => x ^ k) hk) : Int) =\n"
     "      if p % 4 = 1 /\\ k % 4 = 3 then -1 else 1"),
    ("sign_transpose",
     "(m n : Nat)",
     "    (Equiv.Perm.sign ((finProdFinEquiv.symm.trans (Equiv.prodComm (Fin m) (Fin n))).trans\n"
     "        (finProdFinEquiv.trans (finCongr (Nat.mul_comm n m)))) : Int) =\n"
     "      (-1) ^ (Nat.choose m 2 * Nat.choose n 2)"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. Every permutation $\sigma$ of a finite set has a sign $\operatorname{sgn}(\sigma) \in \{1, -1\}$, equal to $(-1)^t$ when $\sigma$ is a product of $t$ transpositions. For $n \ge 1$ and $a$ coprime to $n$, let $\mu_a$ be the permutation $x \mapsto a x$ of $\mathbb{Z}/n\mathbb{Z}$. Write $\left(\frac{a}{n}\right)$ for the Jacobi symbol, which Mathlib calls `jacobiSym a n`. Apart from the unit $u$ in theorem 3, all variables are natural numbers.

1. If $n$ is odd, then $\operatorname{sgn}(\mu_a) = \left(\frac{a}{n}\right)$.
2. If $n$ is even, then $\operatorname{sgn}(\mu_a) = 1$ when $n \equiv 2 \pmod 4$, and $\operatorname{sgn}(\mu_a) = (-1)^{(a-1)/2}$ when $4$ divides $n$.
3. Let $u$ be a unit of $\mathbb{Z}/n\mathbb{Z}$. The permutation $x \mapsto u x$ of the unit group $(\mathbb{Z}/n\mathbb{Z})^\times$ has sign $-1$ if and only if $u$ is not a square in $(\mathbb{Z}/n\mathbb{Z})^\times$ and $n$ is $4$, $p^k$ or $2 p^k$ for an odd prime $p$ and some $k \ge 1$.
4. If $p$ is prime and $x \mapsto x^k$ is a bijection of $\mathbb{Z}/p\mathbb{Z}$, then its sign is $-1$ when $p \equiv 1 \pmod 4$ and $k \equiv 3 \pmod 4$, and $1$ in all other cases.
5. The permutation of $\{0, 1, \dots, m n - 1\}$ that sends $i n + j$ to $j m + i$ for $0 \le i < m$ and $0 \le j < n$ has sign $(-1)^{\binom{m}{2} \binom{n}{2}}$.

Lean statement. `Equiv.Perm.sign` takes values in the units of `Int`, and theorems 1, 2, 4 and 5 compare it with an integer through the coercion to `Int`. The permutation $\mu_a$ is `Units.mulLeft (ZMod.unitOfCoprime a ha)`, where `ha` says that $a$ and $n$ are coprime, and the instance `NeZero n` makes `ZMod n` a finite type. In theorem 4 the bijection is `Equiv.ofBijective (fun x : ZMod p => x ^ k) hk`. In theorem 5 the permutation of `Fin (m * n)` comes from `finProdFinEquiv`, which sends the pair $(i, j)$ to $j + n i$. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    from math import gcd, comb, isqrt

    counts = {}

    def cycles(perm):
        n, seen, out = len(perm), [False] * len(perm), []
        for i in range(n):
            if not seen[i]:
                L, j = 0, i
                while not seen[j]:
                    seen[j] = True
                    j = perm[j]
                    L += 1
                out.append(L)
        return out

    def sign(perm):
        return -1 if sum(L - 1 for L in cycles(perm)) % 2 else 1

    def sign_inversions(perm):
        inv = sum(1 for i in range(len(perm)) for j in range(i + 1, len(perm)) if perm[i] > perm[j])
        return -1 if inv % 2 else 1

    def jac_odd(a, n):
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
        """Mathlib's jacobiSym a n: the factor for each prime 2 of n is 1 if a is odd and 0 if
        a is even."""
        r = 1
        while n > 0 and n % 2 == 0:
            n //= 2
            r *= 1 if a % 2 else 0
        return r * jac_odd(a, n) if n else r

    def is_prime(m):
        return m > 1 and all(m % q for q in range(2, isqrt(m) + 1))

    def cyclic_form(n):
        """n = 4, p^k or 2 p^k with p an odd prime and k >= 1"""
        if n == 4:
            return True
        m = n // 2 if n % 2 == 0 else n
        if m % 2 == 0 or m < 3:
            return False
        p = next(q for q in range(3, m + 1) if m % q == 0)
        while m % p == 0:
            m //= p
        return m == 1

    def mul_perm(a, n):
        return [a * x % n for x in range(n)]

    # theorems 1 and 2
    c1 = c2 = 0
    for n in range(1, 400):
        for a in range(0, 2 * n + 1):
            if gcd(a, n) != 1:
                continue
            sg = sign(mul_perm(a, n))
            # golden route: the sign is (-1)^(n - number of cycles)
            assert sg == (-1) ** (n - len(cycles(mul_perm(a, n))))
            if n % 2 == 1:
                assert sg == jac_odd(a, n), (n, a)
                c1 += 1
            else:
                assert sg == (1 if n % 4 == 2 else (1 if a % 4 == 1 else -1)), (n, a)
                c2 += 1
    counts["theorem 1, odd n < 400, a < 2n coprime"] = c1
    counts["theorem 2, even n < 400, a < 2n coprime"] = c2

    # theorem 3
    c3 = 0
    for n in range(1, 300):
        U = [x for x in range(n) if gcd(x, n) == 1] if n > 1 else [0]
        idx = {x: i for i, x in enumerate(U)}
        squares = {x * x % n for x in U} if n > 1 else {0}
        for u in U:
            sg = sign([idx[u * x % n] if n > 1 else 0 for x in U])
            assert (sg == -1) == (cyclic_form(n) and u not in squares), (n, u)
            c3 += 1
    counts["theorem 3, every unit u for n < 300"] = c3

    # theorem 4
    c4 = 0
    for p in range(2, 400):
        if not is_prime(p):
            continue
        for k in range(0, 3 * p):
            perm = [pow(x, k, p) if (x or k) else 1 for x in range(p)]   # 0^0 = 1 in Lean
            if len(set(perm)) != p:
                assert not (k >= 1 and gcd(k, p - 1) == 1)
                continue
            assert k >= 1 and gcd(k, p - 1) == 1
            sg = sign(perm)
            assert sg == (-1 if (p % 4 == 1 and k % 4 == 3) else 1), (p, k)
            c4 += 1
    counts["theorem 4, primes p < 400, bijective x -> x^k with k < 3p"] = c4

    # theorem 5
    c5 = 0
    for m in range(0, 15):
        for n in range(0, 15):
            perm = [0] * (m * n)
            for i in range(m):
                for j in range(n):
                    perm[j + n * i] = i + m * j      # finProdFinEquiv (i, j) = j + n i
            sg = sign(perm)
            assert sg == sign_inversions(perm) == (-1) ** (comb(m, 2) * comb(n, 2)), (m, n)
            inv = sum(1 for x in range(m * n) for y in range(x + 1, m * n) if perm[x] > perm[y])
            assert inv == comb(m, 2) * comb(n, 2)        # golden route: exact inversion count
            c5 += 1
    counts["theorem 5, all m, n <= 14 (inversions counted exactly)"] = c5

    # data of the golden route
    route = 0
    for n1 in range(1, 60, 2):
        for n2 in range(1, 60, 2):
            if gcd(n1, n2) != 1:
                continue
            for a in range(1, n1 * n2):
                if gcd(a, n1 * n2) == 1 and a % 7 in (1, 2, 3):
                    assert sign(mul_perm(a, n1 * n2)) == sign(mul_perm(a, n1)) * sign(mul_perm(a, n2))
                    route += 1
    for p in (3, 5, 7, 11, 13):
        for k in range(1, 4):
            for a in range(1, p ** k):
                if a % p:
                    assert sign(mul_perm(a, p ** k)) == jac_odd(a, p) ** k
                    route += 1
    for e in range(2, 9):
        for a in range(1, 2 ** e, 2):
            assert sign(mul_perm(a, 2 ** e)) == (1 if a % 4 == 1 else -1)
            route += 1
    for p in range(3, 200):
        if not is_prime(p):
            continue
        g = next(g for g in range(2, p) if all(pow(g, (p - 1) // q, p) != 1
                                              for q in range(2, p) if (p - 1) % q == 0 and is_prime(q)))
        log = {pow(g, i, p): i for i in range(p - 1)}
        for k in range(1, p - 1):
            if gcd(k, p - 1) != 1:
                continue
            on_units = [log[pow(pow(g, i, p), k, p)] for i in range(p - 1)]
            assert on_units == [k * i % (p - 1) for i in range(p - 1)]
            assert sign(on_units) == sign(mul_perm(k, p - 1))
            route += 1
    for n in range(3, 200):
        U = [x for x in range(n) if gcd(x, n) == 1]
        phi = len(U)
        two_phi = phi & -phi
        for u in U:
            o = next(t for t in range(1, phi + 1) if pow(u, t, n) == 1)
            # the regular permutation of u has phi / o cycles of length o
            sg = -1 if (phi - phi // o) % 2 else 1
            assert sg == (-1 if (o & -o) == two_phi and (phi // o) % 2 == 1 else 1)
            route += 1
    counts["golden-route data (cycles, CRT, prime powers, discrete log, orders)"] = route

    # witnesses
    w = 0
    # theorem 1 at n = 4 (even): sgn = -1 but jacobiSym 3 4 = 1
    assert sign(mul_perm(3, 4)) == -1 and jacobi_mathlib(3, 4) == 1
    w += 1
    # theorem 2 at n = 5 (odd): sgn = J(4|5) = 1 but the formula gives -1
    assert sign(mul_perm(4, 5)) == 1 and (1 if 5 % 4 == 2 else (1 if 4 % 4 == 1 else -1)) == -1
    w += 1
    perm = [pow(x, 3, 15) for x in range(15)]                      # theorem 4 at n = 15
    assert len(set(perm)) == 15 and sign(perm) == -1 and 15 % 4 != 1
    w += 1
    counts["witnesses for the 3 dropped-hypothesis cases (n odd, n even, p prime)"] = w
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

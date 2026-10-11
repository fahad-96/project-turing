#!/usr/bin/env python3
"""Project Turing, task 38 generator (proof writing): Gauss factorials and the Gauss-Wilson
theorem (Gauss 1801; Cosgrave and Dilcher 2008, 2011).

P(n) = product of the k in [1, n] coprime to n, G(n) = product of the k in [1, n/2] coprime
to n (floor division), both taken modulo n. Theorems:
  1. n != 1: P(n) = +-1 mod n, and P(n) = -1 iff n = 2, 4, p^a or 2 p^a (p an odd prime)
  2. at least three distinct odd primes divide n: G(n) = 1 mod n
  3. n = p^a q^b, p != q odd primes, a, b >= 1: G(n)^2 = 1 mod n, and G(n) = +-1 mod n iff
     p = q = 1 mod 4
  4. p = 1 mod 4 prime, n = p^a or 2 p^a: G(n)^2 = -1 mod n
  5. G(2^k) = 2^(k-1) + 1 mod 2^k for k >= 4, and G(n) = 1 mod n when 8 | n and an odd prime
     divides n

Writes, next to this script:
  task38_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic:
  - theorem 1 for every 0 <= n <= 3000;
  - theorems 2 and 5 for every n <= 12,000 with the respective hypotheses, and k <= 20;
  - theorem 3 for every n = p^a q^b <= 12,000;
  - theorem 4 for every n = p^a or 2 p^a <= 20,000 with p = 1 mod 4;
  - the data of the planned golden route: P(n) = (-1)^(phi(n)/2) G(n)^2 mod n (pairing k with
    n - k) for n <= 4000, and the residues of G(n) modulo each prime power factor of n;
  - a numeric witness for every hypothesis: dropping it makes the statement false.
There is no finite search space: n, p, q, a, b, k are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t38_generator.py
"""

TASK = 38
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

FULL = "(Finset.filter (fun k => Nat.Coprime k n) (Finset.Icc 1 n)).prod id"
HALF = "(Finset.filter (fun k => Nat.Coprime k n) (Finset.Icc 1 (n / 2))).prod id"
PQ = "(p ^ a * q ^ b)"
HPQ = ("(Finset.filter (fun k => Nat.Coprime k " + PQ + ")\n"
       "          (Finset.Icc 1 " + PQ[:-1] + " / 2))).prod id")

THEOREMS = [
    ("prod_coprime_emod",
     "(n : Nat) (hn : Not (n = 1))",
     "    (" + FULL + " % n = 1 \\/\n"
     "        " + FULL + " % n = n - 1) /\\\n"
     "      (" + FULL + " % n = n - 1 <->\n"
     "        n = 2 \\/ n = 4 \\/\n"
     "          exists p a : Nat, p.Prime /\\ p % 2 = 1 /\\ 1 <= a /\\ (n = p ^ a \\/ n = 2 * p ^ a))"),
    ("prod_half_emod_of_three_le",
     "(n : Nat)\n    (hn : 3 <= (Finset.filter (fun p => p % 2 = 1) n.primeFactors).card)",
     "    " + HALF + " % n = 1"),
    ("prod_half_two_primes",
     "(p q a b : Nat) (hp : p.Prime) (hq : q.Prime) (hp2 : p % 2 = 1)\n"
     "    (hq2 : q % 2 = 1) (hpq : Not (p = q)) (ha : 1 <= a) (hb : 1 <= b)",
     "    (Finset.filter (fun k => Nat.Coprime k " + PQ + ")\n"
     "        (Finset.Icc 1 " + PQ[:-1] + " / 2))).prod id ^ 2 % " + PQ + " = 1 /\\\n"
     "      (" + HPQ + " % " + PQ + " = 1 \\/\n"
     "        " + HPQ + " % " + PQ + " =\n"
     "          p ^ a * q ^ b - 1 <->\n"
     "        p % 4 = 1 /\\ q % 4 = 1)"),
    ("prod_half_sq_add_one",
     "(p a n : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)\n    (hn : n = p ^ a \\/ n = 2 * p ^ a)",
     "    (" + HALF + " ^ 2 + 1) %\n      n = 0"),
    ("prod_half_two_pow_and_eight_dvd",
     "",
     "    (forall k : Nat, 4 <= k ->\n"
     "      (Finset.filter (fun j => Nat.Coprime j (2 ^ k)) (Finset.Icc 1 (2 ^ k / 2))).prod id %\n"
     "          2 ^ k = 2 ^ (k - 1) + 1) /\\\n"
     "      forall n : Nat, n % 8 = 0 -> (exists p : Nat, p.Prime /\\ p % 2 = 1 /\\ n % p = 0) ->\n"
     "        (Finset.filter (fun j => Nat.Coprime j n) (Finset.Icc 1 (n / 2))).prod id % n = 1"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. For an integer $n \ge 0$ let $P(n)$ be the product of the integers $k$ with $1 \le k \le n$ and $\gcd(k, n) = 1$, and let $G(n)$ be the product of those with $1 \le k \le \lfloor n/2 \rfloor$ (an empty product is $1$). Gauss's theorem 1 extends Wilson's theorem, and theorems 2 to 5 describe the half product $G(n)$ modulo $n$.

1. (Gauss.) For $n \ne 1$, $P(n) \equiv \pm 1 \pmod n$, and $P(n) \equiv -1 \pmod n$ if and only if $n = 2$, $n = 4$, $n = p^a$ or $n = 2p^a$ for an odd prime $p$ and $a \ge 1$.
2. If at least three distinct odd primes divide $n$, then $G(n) \equiv 1 \pmod n$.
3. Let $p \ne q$ be odd primes, $a, b \ge 1$ and $n = p^a q^b$. Then $G(n)^2 \equiv 1 \pmod n$, and $G(n) \equiv \pm 1 \pmod n$ if and only if $p \equiv q \equiv 1 \pmod 4$.
4. If $p \equiv 1 \pmod 4$ is prime and $n = p^a$ or $n = 2p^a$, then $G(n)^2 \equiv -1 \pmod n$.
5. For $k \ge 4$, $G(2^k) \equiv 2^{k-1} + 1 \pmod{2^k}$. If $8 \mid n$ and some odd prime divides $n$, then $G(n) \equiv 1 \pmod n$.

Lean statement. The products are `Finset.prod id` over `Finset.filter (fun k => Nat.Coprime k n)` of `Finset.Icc 1 n` and of `Finset.Icc 1 (n / 2)`, and the congruences use `%` on `Nat`, so $-1$ modulo $n$ is `n - 1`. Theorem 2 counts the odd prime factors of $n$ through `n.primeFactors`. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    from math import gcd

    counts = {}

    def factor(n):
        f, m, d = {}, n, 2
        while d * d <= m:
            while m % d == 0:
                f[d] = f.get(d, 0) + 1
                m //= d
            d += 1
        if m > 1:
            f[m] = f.get(m, 0) + 1
        return f

    def is_prime(n):
        return n > 1 and factor(n) == {n: 1}

    def prod_mod(n, top):
        """product of the k in [1, top] with gcd(k, n) = 1, reduced mod n (n >= 1)."""
        ps = list(factor(n)) if n > 1 else []
        r = 1 % n
        for k in range(1, top + 1):
            if all(k % p for p in ps):
                r = r * k % n
        return r

    def G(n):
        return prod_mod(n, n // 2)

    def P(n):
        return prod_mod(n, n)

    # theorem 1
    t1 = 0
    for n in range(2, 3001):
        f = factor(n)
        odd = [p for p in f if p % 2]
        cyc = n in (2, 4) or (len(odd) == 1 and f.get(2, 0) <= 1)
        v = P(n)
        assert v in (1 % n, n - 1) and ((v == n - 1) == cyc), n
        t1 += 1
    counts["theorem 1 (Gauss), 2 <= n <= 3000 (n = 0 checked by hand: empty product)"] = t1

    # theorems 2 and 5 (second part), and the route data
    t2 = t5 = route = 0
    for n in range(1, 12001):
        f = factor(n)
        odd = [p for p in f if p % 2]
        if len(odd) >= 3:
            assert G(n) == 1, n
            t2 += 1
        if n % 8 == 0 and odd:
            assert G(n) == 1 % n, n
            t5 += 1
    for n in range(3, 4001):
        phi = sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)
        g = G(n)
        assert P(n) == ((-1) ** (phi // 2) * g * g) % n
        for p, e in factor(n).items():             # residues of G(n) modulo prime powers
            q = p ** e
            assert g * g % q in (1 % q, q - 1)
        route += 1
    for k in range(1, 21):
        if k >= 4:
            assert G(2 ** k) == 2 ** (k - 1) + 1, k
            t5 += 1
    counts["theorem 2 (at least three odd primes), n <= 12,000"] = t2
    counts["theorem 5 (8 | n with an odd prime, n <= 12,000; 2^k with 4 <= k <= 20)"] = t5

    # theorem 3
    t3 = 0
    for n in range(15, 12001, 2):
        f = factor(n)
        if len(f) != 2:
            continue
        (p, a), (q, b) = sorted(f.items())
        g = G(n)
        assert g * g % n == 1 and ((g in (1, n - 1)) == (p % 4 == 1 and q % 4 == 1)), n
        t3 += 1
    counts["theorem 3 (two odd primes), n = p^a q^b <= 12,000"] = t3

    # theorem 4
    t4 = 0
    for p in range(5, 20001, 4):
        if not is_prime(p):
            continue
        q = p
        while 2 * q <= 20000:
            for n in (q, 2 * q):
                g = G(n)
                assert (g * g + 1) % n == 0, n
                t4 += 1
            q *= p
    counts["theorem 4 (p = 1 mod 4), n = p^a, 2 p^a <= 20,000"] = t4
    counts["golden-route data (P(n) = (-1)^(phi/2) G(n)^2, G(n)^2 = +-1 mod each p^e)"] = route

    # witnesses
    w = 0
    assert P(1) == 0 and not (1 in (2, 4))              # thm 1, n = 1: 0 = 1 - 1 but 1 is excluded
    w += 1
    assert G(15) != 1                                    # thm 2, two odd primes
    w += 1
    g45 = G(45)                                          # thm 3: p = 9 or q = 9 (not prime)
    assert g45 * g45 % 45 == 1 and g45 not in (1, 44) and 9 % 4 == 1 and 5 % 4 == 1
    assert G(10) ** 2 % 10 != 1                          # p = 2 or q = 2: n = 10
    assert G(25) ** 2 % 25 != 1                          # p = q = 5: n = 25
    assert G(5) ** 2 % 5 != 1                            # a = 0 or b = 0: n = 5
    w += 7
    assert (G(9) ** 2 + 1) % 9 != 0                      # thm 4, p = 9 (not prime)
    assert (G(3) ** 2 + 1) % 3 != 0                      # p = 3 (3 mod 4), or n = 3 for p = 5
    w += 3
    assert G(8) != 2 ** 2 + 1                            # thm 5, k = 3
    assert G(12) != 1 and G(16) != 1                     # 8 does not divide 12; 16 has no odd prime
    w += 3
    counts["witnesses for the 15 hypotheses (each one false when dropped)"] = w
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

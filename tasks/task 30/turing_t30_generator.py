#!/usr/bin/env python3
"""Project Turing, task 30 generator (proof writing): Dedekind sums, Knopp's Hecke identity,
denominators, Rademacher's congruence modulo 8, and the vanishing and equality criteria
(Dedekind 1892, Rademacher 1954 and Rademacher and Grosswald 1972, Knopp 1980, Jabuka, Robins
and Wang 2011).

s(h, k) = sum_{r=1}^{k-1} ((r/k)) ((h r/k)), ((x)) = x - floor x - 1/2 off the integers and 0
on them, s(h, 0) = 0.
Theorems:
  1. sum_{d | n} sum_{b < d} s((n/d) h + b k, d k) = sigma(n) s(h, k)        (all h, k, n)
  2. 2 gcd(3, k) k s(h, k) is an integer                                    (all h, k)
  3. k odd, gcd(h, k) = 1: 12 k s(h, k) = k + 1 - 2 J(h | k) mod 8
  4. k >= 1, gcd(h, k) = 1: s(h, k) = 0  <->  k | h^2 + 1
  5. k prime, a, b coprime to k: s(a, k) = s(b, k)  <->  a = b or a b = 1 mod k

Writes, next to this script:
  task30_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact rational arithmetic (fractions.Fraction), s computed from the
Lean formula sum_{0 <= r < k} (r/k - 1/2) * (if h r % k = 0 then 0 else (h r % k)/k - 1/2)
and compared with the sawtooth definition:
  - theorem 1 for k <= 24, h <= 2k + 1, n <= 14 (no hypotheses);
  - theorem 2 for k <= 200 and h <= 3k (no hypotheses);
  - theorem 3 for odd k <= 301 and h < 2k coprime to k;
  - theorem 4 for k <= 300 and h < 2k coprime to k;
  - theorem 5 for every prime k <= 199 and all a, b < 2k coprime to k;
  - the data of the planned golden route: the reciprocity law
    s(h, k) + s(k, h) = (h^2 + k^2 + 1 - 3 h k) / (12 h k), the congruence
    12 h k s(h, k) = h^2 + 1 mod gcd(3, k) k, the symmetries s(h', k) = s(h, k) for
    h h' = 1 mod k and s(k - h, k) = -s(h, k), the reduction s(g h, g k) = s(h, k) and the
    multiplication formula sum_{j < d} ((x + j/d)) = ((d x));
  - a numeric witness for every hypothesis: dropping it makes the statement false.
There is no finite search space: h, k, n are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t30_generator.py
"""

TASK = 30
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

S_BINDERS = (
    "(s : Nat -> Nat -> Rat)\n"
    "    (hs : forall x y : Nat, s x y = Finset.sum (Finset.range y) (fun r =>\n"
    "      ((r : Rat) / y - 1 / 2) *\n"
    "        (if x * r % y = 0 then 0 else ((x * r % y : Nat) : Rat) / y - 1 / 2)))")

THEOREMS = [
    ("sum_divisors_sum_dedekind_eq_sigma_mul",
     S_BINDERS + "\n    (h k n : Nat)",
     "    Finset.sum (Nat.divisors n) (fun d =>\n"
     "        Finset.sum (Finset.range d) (fun b => s (n / d * h + b * k) (d * k))) =\n"
     "      (ArithmeticFunction.sigma 1 n : Rat) * s h k"),
    ("exists_int_eq_two_mul_gcd_mul_dedekind",
     S_BINDERS + "\n    (h k : Nat)",
     "    exists m : Int, ((2 * Nat.gcd 3 k * k : Nat) : Rat) * s h k = m"),
    ("dedekind_modEq_eight",
     S_BINDERS + "\n    (h k : Nat) (hk : k % 2 = 1) (hhk : Nat.Coprime h k)",
     "    exists m : Int, (12 * k : Rat) * s h k = k + 1 - 2 * jacobiSym h k + 8 * m"),
    ("dedekind_eq_zero_iff",
     S_BINDERS + "\n    (h k : Nat) (hk : 0 < k) (hhk : Nat.Coprime h k)",
     "    s h k = 0 <-> (h ^ 2 + 1) % k = 0"),
    ("dedekind_eq_iff",
     S_BINDERS + "\n    (a b k : Nat) (hk : k.Prime) (ha : Nat.Coprime a k) (hb : Nat.Coprime b k)",
     "    s a k = s b k <-> (a % k = b % k \\/ a * b % k = 1)"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. For a real number $x$ let $((x)) = x - \lfloor x \rfloor - \frac{1}{2}$ if $x$ is not an integer and $((x)) = 0$ if $x$ is an integer. For natural numbers $h$ and $k \ge 1$, the Dedekind sum is $s(h, k) = \sum_{r=1}^{k-1} \left(\left(\frac{r}{k}\right)\right) \left(\left(\frac{h r}{k}\right)\right)$, and $s(h, 0) = 0$. Write $\sigma(n)$ for the sum of the divisors of $n$ and $\left(\frac{h}{k}\right)$ for the Jacobi symbol, which Mathlib calls `jacobiSym h k`. All variables are natural numbers.

1. For all $h, k, n$, $\sum_{d \mid n} \sum_{b=0}^{d-1} s\left(\frac{n}{d} h + b k, d k\right) = \sigma(n)\, s(h, k)$.
2. For all $h, k$, the number $2 \gcd(3, k)\, k\, s(h, k)$ is an integer.
3. If $k$ is odd and $\gcd(h, k) = 1$, then $12 k\, s(h, k) - k - 1 + 2 \left(\frac{h}{k}\right)$ is $8$ times an integer.
4. If $k \ge 1$ and $\gcd(h, k) = 1$, then $s(h, k) = 0$ if and only if $k$ divides $h^2 + 1$.
5. If $k$ is prime and $a, b$ are coprime to $k$, then $s(a, k) = s(b, k)$ if and only if $a \equiv b \pmod k$ or $a b \equiv 1 \pmod k$.

Lean statement. Each theorem takes the Dedekind sum as a function `s : Nat -> Nat -> Rat` together with the hypothesis `hs`, which fixes its value at every pair of arguments. In `hs` the sum over `Finset.range y` runs over $0 \le r < y$. For $r \ge 1$ the first factor `(r : Rat) / y - 1 / 2` equals $((r/y))$ and the second factor equals $((x r/y))$. The term with $r = 0$ vanishes because its second factor is $0$. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    from fractions import Fraction as F
    from math import gcd, isqrt

    counts = {}
    memo = {}

    def s(h, k):
        """the Lean formula of hs, exactly"""
        key = (h % k, k) if k else (0, 0)
        if key in memo:
            return memo[key]
        if k == 0:
            v = F(0)
        else:
            t = 0
            for r in range(k):
                m = h * r % k
                if m:
                    t += (2 * r - k) * (2 * m - k)
            v = F(t, 4 * k * k)
        memo[key] = v
        return v

    def saw(x):
        if x.denominator == 1:
            return F(0)
        return x - (x.numerator // x.denominator) - F(1, 2)

    def s_def(h, k):
        return sum((saw(F(r, k)) * saw(F(h * r, k)) for r in range(1, k)), F(0))

    def sigma(n):
        return sum(d for d in range(1, n + 1) if n % d == 0)

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

    def is_prime(m):
        return m > 1 and all(m % q for q in range(2, isqrt(m) + 1))

    # the Lean formula equals the sawtooth definition
    c0 = 0
    for k in range(1, 70):
        for h in range(0, 2 * k + 2):
            assert s(h, k) == s_def(h, k), (h, k)
            c0 += 1
    counts["Lean formula = sawtooth definition (k < 70, h <= 2k + 1)"] = c0

    # theorem 1
    c1 = 0
    for k in range(0, 25):
        for h in range(0, 2 * k + 2):
            for n in range(0, 15):
                lhs = sum((s((n // d) * h + b * k, d * k) for d in range(1, n + 1) if n % d == 0
                           for b in range(d)), F(0))
                assert lhs == sigma(n) * s(h, k), (h, k, n)
                c1 += 1
    counts["theorem 1, k <= 24, h <= 2k + 1, n <= 14"] = c1

    # theorem 2
    c2 = 0
    for k in range(0, 201):
        for h in range(0, 3 * k + 1):
            assert (2 * gcd(3, k) * k * s(h, k)).denominator == 1, (h, k)
            c2 += 1
    counts["theorem 2, k <= 200, h <= 3k"] = c2

    # theorem 3
    c3 = 0
    for k in range(1, 302, 2):
        for h in range(0, 2 * k):
            if gcd(h, k) != 1:
                continue
            t = 12 * k * s(h, k) - (k + 1 - 2 * jac_odd(h, k))
            assert t.denominator == 1 and t.numerator % 8 == 0, (h, k)
            c3 += 1
    counts["theorem 3, odd k <= 301, h < 2k coprime"] = c3

    # theorem 4
    c4 = 0
    for k in range(1, 301):
        for h in range(0, 2 * k):
            if gcd(h, k) != 1:
                continue
            assert (s(h, k) == 0) == ((h * h + 1) % k == 0), (h, k)
            c4 += 1
    counts["theorem 4, k <= 300, h < 2k coprime"] = c4

    # theorem 5
    c5 = 0
    for k in range(2, 200):
        if not is_prime(k):
            continue
        A = [a for a in range(1, 2 * k) if a % k]
        for a in A:
            for b in A:
                assert (s(a, k) == s(b, k)) == (a % k == b % k or a * b % k == 1), (a, b, k)
                c5 += 1
    counts["theorem 5, primes k < 200, a, b < 2k coprime"] = c5

    # data of the golden route
    route = 0
    for h in range(1, 120):
        for k in range(1, 120):
            if gcd(h, k) != 1:
                continue
            assert s(h, k) + s(k, h) == F(h * h + k * k + 1 - 3 * h * k, 12 * h * k)
            t = 12 * h * k * s(h, k)
            assert t.denominator == 1 and (t.numerator - h * h - 1) % (gcd(3, k) * k) == 0
            hinv = pow(h, -1, k) if k > 1 else 0
            assert s(hinv, k) == s(h, k) and s(k - h % k, k) == -s(h, k)
            route += 1
    for h in range(0, 40):
        for k in range(1, 40):
            for g in range(1, 6):
                assert s(g * h, g * k) == s(h, k)
                route += 1
    for d in range(1, 13):
        for num in range(-40, 41):
            for den in range(1, 13):
                x = F(num, den)
                assert sum((saw(x + F(j, d)) for j in range(d)), F(0)) == saw(d * x)
                route += 1
    counts["golden-route data (reciprocity, congruence, symmetries, multiplication formula)"] = route

    # witnesses
    w = 0
    # theorem 3: k = 2 (even), h = 1: 12 * 2 * s(1, 2) - 3 + 2 J(1|2) = -1, J(1|2) = 1 in Mathlib
    assert s(1, 2) == 0 and (0 - (2 + 1 - 2 * 1)) % 8 != 0
    # theorem 3: h = k = 3 (not coprime): s(3, 3) = 0 and J(3|3) = 0
    assert s(3, 3) == 0 and jac_odd(3, 3) == 0 and (0 - (3 + 1 - 0)) % 8 != 0
    w += 2
    # theorem 4: k = 0, h = 1: s(1, 0) = 0 but (1 + 1) % 0 = 2 in Lean
    assert s(1, 0) == 0 and (1 * 1 + 1) != 0
    # theorem 4: h = k = 2 (not coprime): s(2, 2) = 0 but 2 does not divide 5
    assert s(2, 2) == 0 and (2 * 2 + 1) % 2 != 0
    w += 2
    # theorem 5: k = 25 (not prime): s(4, 25) = s(9, 25) = 4/25 with 4 != 9, 36 != 1 mod 25
    assert s(4, 25) == s(9, 25) == F(4, 25) and 4 * 9 % 25 != 1
    # theorem 5: a = 5 not coprime to k = 5, b = 2: s(5, 5) = s(2, 5) = 0
    assert s(5, 5) == s(2, 5) == 0 and 5 % 5 != 2 and 5 * 2 % 5 != 1
    assert s(2, 5) == s(5, 5) == 0 and 2 % 5 != 5 % 5 and 2 * 5 % 5 != 1
    w += 3
    counts["witnesses for the 7 hypotheses (each one false when dropped)"] = w
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

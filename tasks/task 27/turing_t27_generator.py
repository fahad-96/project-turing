#!/usr/bin/env python3
"""Project Turing, task 27 generator (proof writing): the number of representations of n by the
binary quadratic forms x^2 + xy + y^2, x^2 + 3y^2, x^2 + 2y^2, x^2 + xy + 2y^2 and x^2 + 7y^2,
as divisor sums of a quadratic character (Dirichlet 1840, Lorenz 1871, Hall 1940).

Theorems (n >= 1; r(n) = number of integer pairs (x, y), counted in the box |x|, |y| <= n):
  x^2 + xy + y^2:  r(n) = 6 sum_{d | n} (d/3)
  x^2 + 3 y^2:     r(n) = 2 sum_{d | n} (d/3) + 4 sum_{d | n, 4 | d} ((d/4)/3)
  x^2 + 2 y^2:     r(n) = 2 sum_{d | n} (-2/d)
  x^2 + xy + 2y^2: r(n) = 2 sum_{d | n} (d/7)
  x^2 + 7 y^2:     r(n) = 2 sum_{d | n} (d/7) - 4 sum_{d | n, d odd, n/d even} (d/7)
(Jacobi symbols, Mathlib `jacobiSym`).

Writes, next to this script:
  task27_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic:
  - r(n) by enumeration for every n <= 20000 (all solutions found with a generous bound lie in
    the box |x|, |y| <= n used in Lean), compared with the five divisor sums;
  - the literal Lean counts (pairs in Finset.Icc (-n) n squared) for every n <= 60;
  - the data of the planned golden route: the splitting of every prime p < 10^4 (number of
    representations 0, w, 2w according to the character), the multiplicativity of r(n) / w for
    the three maximal orders on all coprime pairs with product <= 20000, and the index
    relations r_{x^2+3y^2}(n) = r_{x^2+xy+y^2}(n) / 3 (n odd), 0 (n = 2 mod 4),
    r_{x^2+xy+y^2}(n / 4) (4 | n), and r_{x^2+7y^2}(n) = r_{x^2+xy+2y^2}(n) for odd n;
  - n = 0 makes every statement false (the box contains the solution (0, 0), the divisor
    sums are empty), so 0 < n is needed.
There is no finite search space: n is unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t27_generator.py
"""

TASK = 27
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

BOX = "(Finset.product (Finset.Icc (-(n : Int)) n) (Finset.Icc (-(n : Int)) n))"


def _card(expr):
    return ("    ((Finset.filter (fun v : Prod Int Int => " + expr + " = (n : Int))\n"
            "        " + BOX + ").card : Int) =\n")


THEOREMS = [
    ("card_sq_add_mul_add_sq",
     "(n : Nat) (hn : 0 < n)",
     _card("v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2")
     + "      6 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 3)"),
    ("card_sq_add_three_mul_sq",
     "(n : Nat) (hn : 0 < n)",
     _card("v.1 ^ 2 + 3 * v.2 ^ 2")
     + "      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 3) +\n"
     + "        4 * Finset.sum (Finset.filter (fun d => d % 4 = 0) (Nat.divisors n))\n"
     + "          (fun d => jacobiSym ((d / 4 : Nat) : Int) 3)"),
    ("card_sq_add_two_mul_sq",
     "(n : Nat) (hn : 0 < n)",
     _card("v.1 ^ 2 + 2 * v.2 ^ 2")
     + "      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (-2) d)"),
    ("card_sq_add_mul_add_two_mul_sq",
     "(n : Nat) (hn : 0 < n)",
     _card("v.1 ^ 2 + v.1 * v.2 + 2 * v.2 ^ 2")
     + "      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 7)"),
    ("card_sq_add_seven_mul_sq",
     "(n : Nat) (hn : 0 < n)",
     _card("v.1 ^ 2 + 7 * v.2 ^ 2")
     + "      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 7) -\n"
     + "        4 * Finset.sum (Finset.filter (fun d => d % 2 = 1 /\\ n / d % 2 = 0)\n"
     + "          (Nat.divisors n)) (fun d => jacobiSym (d : Int) 7)"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. For a positive definite binary quadratic form $f$ and an integer $n \ge 1$, let $r_f(n)$ be the number of pairs of integers $(x, y)$ with $f(x, y) = n$. Write $\left(\frac{a}{b}\right)$ for the Jacobi symbol. Mathlib calls it `jacobiSym a b`, and it equals $0$ when $\gcd(a, b) > 1$. For every $n \ge 1$:

1. $r_f(n) = 6 \sum_{d \mid n} \left(\frac{d}{3}\right)$ for $f = x^2 + x y + y^2$.
2. $r_f(n) = 2 \sum_{d \mid n} \left(\frac{d}{3}\right) + 4 \sum_{d \mid n,\ 4 \mid d} \left(\frac{d/4}{3}\right)$ for $f = x^2 + 3 y^2$.
3. $r_f(n) = 2 \sum_{d \mid n} \left(\frac{-2}{d}\right)$ for $f = x^2 + 2 y^2$.
4. $r_f(n) = 2 \sum_{d \mid n} \left(\frac{d}{7}\right)$ for $f = x^2 + x y + 2 y^2$.
5. $r_f(n) = 2 \sum_{d \mid n} \left(\frac{d}{7}\right) - 4 \sum_{d \mid n,\ d \text{ odd},\ n/d \text{ even}} \left(\frac{d}{7}\right)$ for $f = x^2 + 7 y^2$.

Lean statement. Every solution of $f(x, y) = n$ satisfies $|x| \le n$ and $|y| \le n$. Each Lean statement therefore counts the pairs `v : Prod Int Int` in the box `Finset.product (Finset.Icc (-n) n) (Finset.Icc (-n) n)` with $f(v.1, v.2) = n$ and compares this count, as an integer, with the divisor sums. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements and of the data of the planned proof."""
    from math import isqrt, gcd

    counts = {}
    NMAX = 20000

    def jacobi(a, n):
        """Mathlib's jacobiSym a n (n >= 1; product of Legendre symbols over the prime factors
        of n, Legendre symbol mod 2 = a mod 2 squared)."""
        res = 1
        m, p = n, 2
        while m > 1:
            if p * p > m:
                p = m
            while m % p == 0:
                m //= p
                if p == 2:
                    res *= (a % 2)
                else:
                    t = pow(a % p, (p - 1) // 2, p)
                    res *= (0 if a % p == 0 else (1 if t == 1 else -1))
            p += 1
        return res

    forms = [(1, 1, 1), (1, 0, 3), (1, 0, 2), (1, 1, 2), (1, 0, 7)]

    def reps(a, b, c, bound):
        """dict n -> count for n <= bound; also checks every solution lies in the box."""
        out = [0] * (bound + 1)
        disc = 4 * a * c - b * b
        ymax = isqrt(4 * a * bound // disc) + 2
        for y in range(-ymax, ymax + 1):
            # a x^2 + b x y + c y^2 = (2 a x + b y)^2 / (4 a) + disc y^2 / (4 a)
            rest = 4 * a * bound - disc * y * y
            if rest < 0:
                continue
            s = isqrt(rest)
            lo = (-s - b * y) // (2 * a) - 1
            hi = (s - b * y) // (2 * a) + 1
            for x in range(lo, hi + 1):
                v = a * x * x + b * x * y + c * y * y
                if 0 < v <= bound:
                    assert abs(x) <= v and abs(y) <= v, (a, b, c, x, y)
                    out[v] += 1
        return out

    R = [reps(a, b, c, NMAX) for (a, b, c) in forms]
    divs = [[] for _ in range(NMAX + 1)]
    for d in range(1, NMAX + 1):
        for m in range(d, NMAX + 1, d):
            divs[m].append(d)
    J3 = [0] + [jacobi(d, 3) for d in range(1, NMAX + 1)]
    J7 = [0] + [jacobi(d, 7) for d in range(1, NMAX + 1)]
    JM2 = [0] + [jacobi(-2, d) for d in range(1, NMAX + 1)]

    def formulas(n):
        D = divs[n]
        s3 = sum(J3[d] for d in D)
        s7 = sum(J7[d] for d in D)
        f1 = 6 * s3
        f2 = 2 * s3 + 4 * sum(J3[d // 4] for d in D if d % 4 == 0)
        f3 = 2 * sum(JM2[d] for d in D)
        f4 = 2 * s7
        f5 = 2 * s7 - 4 * sum(J7[d] for d in D if d % 2 == 1 and (n // d) % 2 == 0)
        return [f1, f2, f3, f4, f5]

    c1 = 0
    for n in range(1, NMAX + 1):
        fs = formulas(n)
        for t in range(5):
            assert R[t][n] == fs[t], (t + 1, n, R[t][n], fs[t])
            c1 += 1
    counts["theorems 1-5 for every n <= %d (enumeration vs divisor sums)" % NMAX] = c1

    lit = 0
    for n in range(1, 61):
        for t, (a, b, c) in enumerate(forms):
            cnt = sum(1 for x in range(-n, n + 1) for y in range(-n, n + 1)
                      if a * x * x + b * x * y + c * y * y == n)
            assert cnt == formulas(n)[t], (t + 1, n)
            lit += 1
    counts["literal Lean box counts for n <= 60"] = lit

    # golden-route data
    route = 0

    def is_prime(m):
        return m > 1 and all(m % q for q in range(2, isqrt(m) + 1))

    for p in range(2, 10 ** 4):
        if not is_prime(p):
            continue
        for t, (w, chi) in ((0, (6, J3)), (2, (2, JM2)), (3, (2, J7))):
            expect = w * (1 + chi[p])
            assert R[t][p] == expect, (t, p)
            route += 1
    for t, w in ((0, 6), (2, 2), (3, 2)):
        for a in range(1, 150):
            for b in range(a + 1, NMAX // a + 1):
                if gcd(a, b) == 1:
                    assert R[t][a * b] * w == R[t][a] * R[t][b], (t, a, b)
                    route += 1
    for n in range(1, NMAX + 1):
        if n % 2 == 1:
            assert 3 * R[1][n] == R[0][n] and R[4][n] == R[3][n]
        elif n % 4 == 2:
            assert R[1][n] == 0
        else:
            assert R[1][n] == R[0][n // 4]
        route += 1
    counts["golden-route data (prime splitting, multiplicativity, index relations)"] = route

    # witness: 0 < n is needed (Lean box at n = 0 is {(0, 0)}, divisor sums are empty)
    for (a, b, c) in forms:
        assert a * 0 + b * 0 + c * 0 == 0
    counts["witness n = 0 (count 1, divisor sums 0) for each theorem"] = 5
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

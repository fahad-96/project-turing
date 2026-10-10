#!/usr/bin/env python3
"""Project Turing, task 26 generator (proof writing): primes of the form x^2 + n y^2 for the
discriminants -20, -24, -52, -84 (one class in each genus), and Euler's product conjecture for
x^2 + 5 y^2 (Fermat, Euler, Lagrange, Gauss).

Theorems (p, q prime):  p = x^2 + 5 y^2 iff p = 5 or p = 1, 9 mod 20;  p, q = 3, 7 mod 20 imply
p q = x^2 + 5 y^2;  p = x^2 + 6 y^2 iff p = 1, 7 mod 24;  p = x^2 + 13 y^2 iff p = 13 or
p = 1, 9, 17, 25, 29, 49 mod 52;  p = x^2 + 21 y^2 iff p = 1, 25, 37 mod 84.

Writes, next to this script:
  task26_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic:
  - every number below 10^6 represented by x^2 + n y^2 (n = 5, 6, 13, 21) is marked, and
    theorems 1, 3, 4, 5 are checked, both directions, for every prime below 10^6;
  - theorem 2 for every pair of primes p, q < 3000 in the classes 3, 7 mod 20;
  - the data of the planned golden route: all reduced forms (|b| <= a <= c) of the
    discriminants -20, -24, -52, -84 (2, 2, 2 and 4 forms); for every prime below 2 * 10^5 not
    dividing the discriminant, it is represented by a form of the discriminant iff -n is a
    square mod p, by exactly one reduced form, and the residue of p mod 4n determines which
    one (genus separation); the composition identity behind theorem 2;
  - for each theorem, a witness showing that each hypothesis or case cannot be dropped
    (composite values, the primes 5 and 13, residue classes 1 mod 20 for theorem 2).
There is no finite search space: p, q, x, y are unbounded natural numbers.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t26_generator.py
"""

TASK = 26
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

THEOREMS = [
    ("prime_eq_sq_add_five_mul_sq_iff",
     "(p : Nat) (hp : p.Prime)", """\
    (exists x y : Nat, p = x ^ 2 + 5 * y ^ 2) <->
      (p = 5 \\/ Membership.mem ({1, 9} : Finset Nat) (p % 20))"""),
    ("mul_eq_sq_add_five_mul_sq",
     "(p q : Nat) (hp : p.Prime) (hq : q.Prime)\n"
     "    (hp20 : Membership.mem ({3, 7} : Finset Nat) (p % 20))\n"
     "    (hq20 : Membership.mem ({3, 7} : Finset Nat) (q % 20))", """\
    exists x y : Nat, p * q = x ^ 2 + 5 * y ^ 2"""),
    ("prime_eq_sq_add_six_mul_sq_iff",
     "(p : Nat) (hp : p.Prime)", """\
    (exists x y : Nat, p = x ^ 2 + 6 * y ^ 2) <->
      Membership.mem ({1, 7} : Finset Nat) (p % 24)"""),
    ("prime_eq_sq_add_thirteen_mul_sq_iff",
     "(p : Nat) (hp : p.Prime)", """\
    (exists x y : Nat, p = x ^ 2 + 13 * y ^ 2) <->
      (p = 13 \\/ Membership.mem ({1, 9, 17, 25, 29, 49} : Finset Nat) (p % 52))"""),
    ("prime_eq_sq_add_twenty_one_mul_sq_iff",
     "(p : Nat) (hp : p.Prime)", """\
    (exists x y : Nat, p = x ^ 2 + 21 * y ^ 2) <->
      Membership.mem ({1, 25, 37} : Finset Nat) (p % 84)"""),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. All variables are natural numbers, and $p$ and $q$ are primes.

1. $p = x^2 + 5 y^2$ for some $x, y$ if and only if $p = 5$ or $p \equiv 1, 9 \pmod{20}$.
2. If $p \equiv 3$ or $7 \pmod{20}$ and $q \equiv 3$ or $7 \pmod{20}$, then $p q = x^2 + 5 y^2$ for some $x, y$.
3. $p = x^2 + 6 y^2$ for some $x, y$ if and only if $p \equiv 1, 7 \pmod{24}$.
4. $p = x^2 + 13 y^2$ for some $x, y$ if and only if $p = 13$ or $p \equiv 1, 9, 17, 25, 29, 49 \pmod{52}$.
5. $p = x^2 + 21 y^2$ for some $x, y$ if and only if $p \equiv 1, 25, 37 \pmod{84}$.

Lean statement. In Lean, a residue condition such as $p \equiv 1, 9 \pmod{20}$ appears as `Membership.mem ({1, 9} : Finset Nat) (p % 20)`, which says that the remainder of $p$ modulo $20$ lies in $\{1, 9\}$. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""

FORM_DATA = {}


def self_check() -> dict:
    """Exact tests of the five statements and of the data of the planned proof."""
    from math import isqrt, gcd

    counts = {}
    N = 10 ** 6

    def sieve(n):
        s = bytearray([1]) * (n + 1)
        s[0] = s[1] = 0
        for i in range(2, isqrt(n) + 1):
            if s[i]:
                s[i * i::i] = bytearray(len(s[i * i::i]))
        return s

    isp = sieve(N)
    primes = [i for i in range(N + 1) if isp[i]]

    def marks(a, b, c, bound):
        """bytearray: m <= bound is a x^2 + b x y + c y^2 for integers x, y (positive definite)."""
        out = bytearray(bound + 1)
        disc = 4 * a * c - b * b
        ymax = isqrt(4 * a * bound // disc) + 1
        if a == 1 and b == 0:
            for y in range(0, ymax + 1):
                rest = bound - c * y * y
                if rest < 0:
                    break
                for x in range(0, isqrt(rest) + 1):
                    out[x * x + c * y * y] = 1
            return out
        for y in range(-ymax, ymax + 1):
            # a x^2 + b y x + c y^2 <= bound; x in a window around -b y / (2a)
            cx = -b * y / (2 * a)
            span = isqrt(max(0, bound // a)) + abs(b * y) + 2
            lo, hi = int(cx) - span, int(cx) + span
            for x in range(lo, hi + 1):
                v = a * x * x + b * x * y + c * y * y
                if 0 <= v <= bound:
                    out[v] = 1
        return out

    rep5, rep6, rep13, rep21 = (marks(1, 0, k, N) for k in (5, 6, 13, 21))
    S1, S3, S4, S5 = {1, 9}, {1, 7}, {1, 9, 17, 25, 29, 49}, {1, 25, 37}
    c1 = 0
    for p in primes:
        assert bool(rep5[p]) == (p == 5 or p % 20 in S1), p
        assert bool(rep6[p]) == (p % 24 in S3), p
        assert bool(rep13[p]) == (p == 13 or p % 52 in S4), p
        assert bool(rep21[p]) == (p % 84 in S5), p
        c1 += 4
    counts["theorems 1, 3, 4, 5, both directions, every prime below 10^6"] = c1

    Q = [p for p in primes if p < 3000 and p % 20 in (3, 7)]
    big = marks(1, 0, 5, 3000 * 3000)
    c2 = 0
    for p in Q:
        for q in Q:
            assert big[p * q], (p, q)
            c2 += 1
    counts["theorem 2, every pair of primes p, q < 3000 in the classes 3, 7 mod 20"] = c2

    # ---- golden-route data: reduced forms, Lagrange's step, genus separation
    def reduced_forms(D):
        out = []
        a = 1
        while 3 * a * a <= -D:
            for b in range(-a + 1, a + 1):
                if (b * b - D) % (4 * a):
                    continue
                c = (b * b - D) // (4 * a)
                if c < a or (b < 0 and a == c):
                    continue
                if gcd(gcd(a, abs(b)), c) == 1:
                    out.append((a, b, c))
            a += 1
        return out

    route = 0
    PB = 2 * 10 ** 5
    for n, expect in ((5, 2), (6, 2), (13, 2), (21, 4)):
        D = -4 * n
        forms = reduced_forms(D)
        assert len(forms) == expect, (n, forms)
        FORM_DATA[n] = forms
        reps = [marks(a, b, c, PB) for (a, b, c) in forms]
        classes = {}
        for p in primes:
            if p > PB:
                break
            if (4 * n) % p == 0:
                continue
            which = [i for i, r in enumerate(reps) if r[p]]
            has_root = any((t * t + n) % p == 0 for t in range(p)) if p < 2000 else None
            if has_root is not None:
                assert bool(which) == has_root, (n, p)
            assert len(which) <= 1, (n, p, which)
            if which:
                classes.setdefault(p % (4 * n), set()).add(which[0])
            route += 1
        assert all(len(v) == 1 for v in classes.values()), n
        principal = sorted(r for r, v in classes.items() if v == {0})
        target = {5: S1, 6: S3, 13: S4, 21: S5}[n]
        assert set(principal) == target, (n, principal)
    # composition behind theorem 2: (2a^2+2ab+3b^2)(2c^2+2cd+3d^2) = X^2 + 5 Y^2
    for a in range(-12, 13):
        for b in range(-12, 13):
            for c in range(-6, 7):
                for d in range(-6, 7):
                    X = 2 * a * c + a * d + b * c - 2 * b * d
                    Y = a * d + b * c + b * d
                    lhs = (2 * a * a + 2 * a * b + 3 * b * b) * (2 * c * c + 2 * c * d + 3 * d * d)
                    assert lhs == X * X + 5 * Y * Y
                    route += 1
    counts["golden-route data (reduced forms, Lagrange step, genus classes, composition)"] = route

    # ---- witnesses: each hypothesis and each case is needed
    wit = 0
    for n, k, S, M, extra in ((6, 5, S1, 20, 5), (10, 6, S3, 24, None), (14, 13, S4, 52, 13),
                              (22, 21, S5, 84, None)):
        rep = marks(1, 0, k, 100)
        assert rep[n] and n % M not in S and n != extra and not isp[n]   # composite n breaks it
        wit += 1
    assert rep5[5] and 5 % 20 not in S1                  # the case p = 5 in theorem 1
    assert rep13[13] and 13 % 52 not in S4               # the case p = 13 in theorem 4
    assert not big[3 * 41] and 41 % 20 == 1              # theorem 2 needs q = 3, 7 mod 20
    comp = [m for m in range(3, 3000) if not isp[m] and m % 20 in (3, 7)
            and not big[m * 3]]
    assert comp, "composite witness for theorem 2"
    COMP_WITNESS = comp[0]
    counts["witnesses (composite values, p = 5, p = 13, q = 41, composite %d)" % COMP_WITNESS] = (
        wit + 4)
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

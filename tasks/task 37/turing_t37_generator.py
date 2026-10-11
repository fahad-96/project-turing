#!/usr/bin/env python3
"""Project Turing, task 37 generator (proof writing): numerical semigroups and the Frobenius
coin problem (Sylvester 1884, Johnson 1960, Roberts 1956, Selmer 1977, Herzog 1970).

rep(n) = n is a sum of the generators with nonnegative integer multiplicities. Theorems:
  1. a, b >= 2 coprime, n <= ab - a - b: exactly one of n and ab - a - b - n is a nonnegative
     combination of a and b (Sylvester)
  2. if G is the largest integer that is not a combination of a, b, c and gcd(d, c) = 1, then
     d G + (d - 1) c is the largest one for d a, d b, c (Johnson)
  3. a >= 2, s >= 1, gcd(a, d) = 1: the largest integer that is not a combination of
     a, a + d, ..., a + s d is (floor((a - 2)/s) + 1) a + (d - 1)(a - 1) - 1 (Roberts)
  4. s >= 1, gcd(a, d) = 1: exactly sum_{m < a} ceil(m/s) + (d - 1)(a - 1)/2 integers are not
     combinations of a, a + d, ..., a + s d (Selmer)
  5. a, b, c minimal generators, g the largest non-combination: the semigroup is symmetric
     (n is a combination iff g - n is not) iff for some pair, say a, b, the gcd e = gcd(a, b) is
     > 1 and c is a combination of a/e and b/e (Herzog)

Writes, next to this script:
  task37_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic (dynamic programming over the representable
integers):
  - theorem 1 for every coprime 2 <= a, b <= 60 and every n <= ab - a - b;
  - theorem 2 for every a, b <= 14, c <= 16, d <= 8 with gcd(d, c) = 1 and a Frobenius number;
  - theorems 3 and 4 for every a <= 40, 1 <= d <= 15 with gcd(a, d) = 1 and 1 <= s <= 10;
  - theorem 5 for every minimally generated triple with entries <= 40 and a Frobenius number;
  - the data of the planned golden route: the Apery set of a, a + d, ..., a + s d with respect
    to a is {ceil(m/s) a + d m : m < a}, and Selmer's formulas (Frobenius number = max - a,
    genus = sum/a - (a - 1)/2) for every semigroup above;
  - a numeric witness for every hypothesis: dropping it makes the statement false.
There is no finite search space: the generators and n are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t37_generator.py
"""

TASK = 37
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

AS = "Finset.sum Finset.univ (fun i => x i * (a + i * d))"
ROB = "((a - 2) / s + 1) * a + (d - 1) * (a - 1) - 1"

THEOREMS = [
    ("exists_iff_not_exists_sub",
     "(a b n : Nat) (ha : 2 <= a) (hb : 2 <= b) (hab : Nat.Coprime a b)\n"
     "    (hn : n <= a * b - a - b)",
     "    (exists x y : Nat, n = a * x + b * y) <->\n"
     "      Not (exists x y : Nat, a * b - a - b - n = a * x + b * y)"),
    ("frobenius_mul_mul",
     "(a b c d G : Nat) (hdc : Nat.Coprime d c)\n"
     "    (hG : Not (exists x y z : Nat, G = a * x + b * y + c * z))\n"
     "    (hG' : forall n, G < n -> exists x y z : Nat, n = a * x + b * y + c * z)",
     "    Not (exists x y z : Nat, d * G + (d - 1) * c = d * a * x + d * b * y + c * z) /\\\n"
     "      forall n, d * G + (d - 1) * c < n ->\n"
     "        exists x y z : Nat, n = d * a * x + d * b * y + c * z"),
    ("frobenius_arith_seq",
     "(a d s : Nat) (ha : 2 <= a) (hs : 1 <= s) (had : Nat.Coprime a d)",
     "    Not (exists x : Fin (s + 1) -> Nat,\n"
     "        " + ROB + " =\n"
     "          " + AS + ") /\\\n"
     "      forall n, " + ROB + " < n ->\n"
     "        exists x : Fin (s + 1) -> Nat, n = " + AS),
    ("ncard_not_arith_seq",
     "(a d s : Nat) (hs : 1 <= s) (had : Nat.Coprime a d)",
     "    Set.ncard {n : Nat | Not (exists x : Fin (s + 1) -> Nat,\n"
     "        n = " + AS + ")} =\n"
     "      Finset.sum (Finset.range a) (fun m => (m + s - 1) / s) + (d - 1) * (a - 1) / 2"),
    ("symmetric_iff",
     "(a b c g : Nat)\n"
     "    (ha : Not (exists x y : Nat, a = b * x + c * y))\n"
     "    (hb : Not (exists x y : Nat, b = a * x + c * y))\n"
     "    (hc : Not (exists x y : Nat, c = a * x + b * y))\n"
     "    (hg : Not (exists x y z : Nat, g = a * x + b * y + c * z))\n"
     "    (hg' : forall n, g < n -> exists x y z : Nat, n = a * x + b * y + c * z)",
     "    (forall n, n <= g ->\n"
     "      ((exists x y z : Nat, n = a * x + b * y + c * z) <->\n"
     "        Not (exists x y z : Nat, g - n = a * x + b * y + c * z))) <->\n"
     "      (1 < Nat.gcd a b /\\\n"
     "          exists x y : Nat, c = a / Nat.gcd a b * x + b / Nat.gcd a b * y) \\/\n"
     "        (1 < Nat.gcd a c /\\\n"
     "          exists x y : Nat, b = a / Nat.gcd a c * x + c / Nat.gcd a c * y) \\/\n"
     "        (1 < Nat.gcd b c /\\\n"
     "          exists x y : Nat, a = b / Nat.gcd b c * x + c / Nat.gcd b c * y)"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. Below all numbers are nonnegative integers, and a combination of $a_1, \dots, a_k$ means a sum $a_1 x_1 + \dots + a_k x_k$ with integers $x_i \ge 0$. If all large integers are combinations of the $a_i$, the largest integer that is not one is the Frobenius number of $a_1, \dots, a_k$.

1. (Sylvester.) Let $a, b \ge 2$ be coprime and $0 \le n \le ab - a - b$. Then exactly one of $n$ and $ab - a - b - n$ is a combination of $a$ and $b$.
2. (Johnson.) Let $G$ be the Frobenius number of $a, b, c$, and let $d$ be coprime to $c$. Then the Frobenius number of $da, db, c$ is $dG + (d - 1)c$.
3. (Roberts.) Let $a \ge 2$, $s \ge 1$ and $\gcd(a, d) = 1$. The Frobenius number of the arithmetic progression $a, a + d, \dots, a + sd$ is $\big(\lfloor (a - 2)/s \rfloor + 1\big) a + (d - 1)(a - 1) - 1$.
4. (Selmer.) Let $s \ge 1$ and $\gcd(a, d) = 1$. Exactly $\sum_{m=0}^{a-1} \lceil m/s \rceil + (d - 1)(a - 1)/2$ integers $n \ge 0$ are not combinations of $a, a + d, \dots, a + sd$.
5. (Herzog.) Let $a, b, c$ be such that none of them is a combination of the other two, and let $g$ be their Frobenius number. Then the semigroup they generate is symmetric, meaning that for every $0 \le n \le g$ exactly one of $n$ and $g - n$ is a combination of $a, b, c$, if and only if for some pair, say $a, b$, the number $e = \gcd(a, b)$ is greater than $1$ and $c$ is a combination of $a/e$ and $b/e$.

Lean statement. In theorems 2 and 5 the Frobenius number appears through two hypotheses: it is not a combination, and every larger integer is one. In theorems 3 and 4 a function `x : Fin (s + 1) -> Nat` describes a combination of $a, a + d, \dots, a + sd$, and $\lceil m/s \rceil$ is `(m + s - 1) / s`. In theorem 4 the count is the `Set.ncard` of the set of non-combinations. In theorem 5 the statement lists the condition on a pair for each of the three pairs. Subtraction and division are those of `Nat`, so $(d - 1)(a - 1)/2$ is exact because $a$ and $d$ are not both even. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    from math import gcd

    counts = {}

    def reps(gens, N):
        r = [False] * (N + 1)
        r[0] = True
        gs = [g for g in gens if g > 0]
        for n in range(1, N + 1):
            r[n] = any(n >= g and r[n - g] for g in gs)
        return r

    def frob(gens):
        """(Frobenius number or None, number of non-combinations or None, table)."""
        g0 = 0
        for x in gens:
            g0 = gcd(g0, x)
        if g0 != 1:
            return None, None, None
        N = 2 * max(gens) ** 2 + 2 * max(gens) + 10
        r = reps(gens, N)
        non = [n for n in range(N + 1) if not r[n]]
        assert all(r[N - max(gens):])            # beyond the table everything is a combination
        return (max(non) if non else None), len(non), r

    # theorem 1
    t1 = 0
    for a in range(2, 61):
        for b in range(2, 61):
            if gcd(a, b) != 1:
                continue
            g = a * b - a - b
            r = reps([a, b], g)
            for n in range(0, g + 1):
                assert r[n] != r[g - n]
                t1 += 1
    counts["theorem 1 (Sylvester), triples (a, b, n)"] = t1

    # theorem 2
    t2 = 0
    for a in range(1, 15):
        for b in range(1, 15):
            for c in range(1, 17):
                G, _, _ = frob([a, b, c])
                if G is None:
                    continue
                for d in range(1, 9):
                    if gcd(d, c) != 1:
                        continue
                    G2, _, _ = frob([d * a, d * b, c])
                    assert G2 == d * G + (d - 1) * c, (a, b, c, d)
                    t2 += 1
    counts["theorem 2 (Johnson), tuples (a, b, c, d)"] = t2

    # theorems 3 and 4, and the Apery sets
    t34 = route = 0
    for a in range(1, 41):
        for d in range(1, 16):
            if gcd(a, d) != 1:
                continue
            for s in range(1, 11):
                gens = [a + i * d for i in range(s + 1)]
                G, cnt, r = frob(gens)
                genus = sum((m + s - 1) // s for m in range(a)) + (d - 1) * (a - 1) // 2
                assert (d - 1) * (a - 1) % 2 == 0 and cnt == genus, (a, d, s)
                if a >= 2:
                    assert G == ((a - 2) // s + 1) * a + (d - 1) * (a - 1) - 1, (a, d, s)
                    ap = [((m + s - 1) // s) * a + d * m for m in range(a)]
                    for w in ap:                # w is the least combination in its class mod a
                        assert r[w] and (w < a or not r[w - a])
                    assert sorted(w % a for w in ap) == list(range(a))
                    assert G == max(ap) - a and cnt * a == sum(ap) - a * (a - 1) // 2
                    route += 1
                t34 += 1
    counts["theorems 3 and 4 (Roberts, Selmer), triples (a, d, s)"] = t34

    # theorem 5
    def comb2(z, x, y):
        return reps([x, y], z)[z] if z >= 0 else False

    def minimal(a, b, c):
        return not comb2(a, b, c) and not comb2(b, a, c) and not comb2(c, a, b)

    def ci(a, b, c):
        out = False
        for (x, y, z) in ((a, b, c), (a, c, b), (b, c, a)):
            e = gcd(x, y)
            if e > 1 and comb2(z, x // e, y // e):
                out = True
        return out

    def symmetric(r, g):
        return all(r[n] != r[g - n] for n in range(g + 1))

    t5 = 0
    for a in range(1, 41):
        for b in range(a, 41):
            for c in range(b, 41):
                if not minimal(a, b, c):
                    continue
                g, _, r = frob([a, b, c])
                if g is None:
                    continue
                assert symmetric(r, g) == ci(a, b, c), (a, b, c)
                t5 += 1
    counts["theorem 5 (Herzog), minimally generated triples"] = t5
    counts["golden-route data (Apery sets of arithmetic sequences, Selmer's formulas)"] = route

    # witnesses
    w = 0
    def nsub(x, y):                            # subtraction of natural numbers
        return max(x - y, 0)
    # theorem 1: (a, b, n) = (1, 2, 0), (2, 1, 0): n and nsub(ab - a - b, n) = 0 are both
    # combinations; (2, 4, 1): neither 1 nor 2 - 1 = 1 is; (2, 3, 2) with n > ab - a - b = 1:
    # 2 and nsub(1, 2) = 0 are both combinations
    for (x, y, n, both) in ((1, 2, 0, True), (2, 1, 0, True), (2, 4, 1, False), (2, 3, 2, True)):
        r = reps([x, y], 20)
        m = nsub(nsub(nsub(x * y, x), y), n)
        assert r[n] == r[m] == both
    w += 4
    G, _, _ = frob([3, 5, 2])                  # thm 2: G = 1 for 3, 5, 2
    assert G == 1 and frob([6, 10, 2])[0] is None        # d = c = 2: no Frobenius number
    assert reps([9, 15, 2], 20)[3 * 2 + 2 * 2]           # G = 2 (a combination): 10 = 2 * 5
    rr = reps([4, 6, 3], 20)
    assert not rr[2] and not rr[5]             # G = 2 is not the largest non-combination
    r2 = reps([8, 12, 3], 40)
    assert not r2[2 * 2 + 3] and not r2[13]    # 7 is no combination, but neither is 13 > 7
    w += 3
    assert reps([1, 1 + 1], 5)[0]              # thm 3, a = 1: formula gives 0, a combination
    assert frob([3])[0] is None                # s = 0: only multiples of a
    assert frob([2, 4])[0] is None             # a = d = 2: only even numbers
    w += 3
    assert sum((m - 1) // 1 for m in range(0)) == 0          # thm 4, s = 0, a = 3, d = 2:
    assert frob([3])[1] is None and (2 - 1) * (3 - 1) // 2 == 1   # infinite set, ncard 0 != 1
    assert frob([2, 4])[1] is None and sum((m + 0) // 1 for m in range(2)) == 1  # a = d = 2
    w += 2
    for (x, y, z) in ((2, 3, 5), (5, 2, 3), (2, 5, 3)):     # thm 5: one generator not minimal
        g, _, r = frob([x, y, z])
        assert g == 1 and symmetric(r, g) and not ci(x, y, z)
    # g replaced by g + 1 (a combination) and by a smaller non-combination
    found_up = found_down = False
    for (x, y, z) in ((3, 4, 5), (3, 5, 7), (4, 5, 6), (5, 6, 7), (4, 6, 9), (6, 9, 10)):
        if not minimal(x, y, z):
            continue
        g, _, r = frob([x, y, z])
        if symmetric(r, g + 1) != ci(x, y, z) and r[g + 1]:
            found_up = True
        smaller = [h for h in range(g) if not r[h]]
        if any(symmetric(r, h) != ci(x, y, z) for h in smaller):
            found_down = True
    assert found_up and found_down
    w += 5
    counts["witnesses for the 17 hypotheses (each one false when dropped)"] = w
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

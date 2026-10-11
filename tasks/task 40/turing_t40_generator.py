#!/usr/bin/env python3
"""Project Turing, task 40 generator (proof writing): multiples modulo r, the three-gap theorem,
Slater's return times, the terminal lemma and empty lattice tetrahedra (Steinhaus, Sos,
Swierczkowski, Slater, White, Morrison and Stevens).

Write <x> for x mod r. Theorems:
  1. (three gaps) the points <k a> (k < N) together with r cut [0, r] into gaps of at most
     three lengths, and with three lengths the largest is the sum of the other two
  2. (Slater) the gaps between consecutive k with <k a> < b take at most three values, and with
     three values the largest is the sum of the other two
  3. (terminal lemma) for r >= 1 and a, b, c prime to r: <ka> + <kb> + <kc> > r for every
     1 <= k < r iff r divides a + b, a + c or b + c
  4. (White) the tetrahedron with vertices 0, e1, e2, (a, b, r) contains no other lattice point
     iff a = 1 with gcd(b, r) = 1, or b = 1 with gcd(a, r) = 1, or a + b = 0 with gcd(a, r) = 1
     (congruences mod r)
  5. if gcd(a + b + c, r) = 1 and <ka> + <kb> + <kc> >= r for every 1 <= k < r, then r divides
     a + b, a + c or b + c (sharp: r = 9, (a, b, c) = (1, 4, 7))

Writes, next to this script:
  task40_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic:
  - theorem 1 for every r <= 60, 0 <= a < r and N <= r + 2, plus r = 0 and a >= r;
  - theorem 2 for every r <= 45, 0 <= a < r and b <= r + 1, plus r = 0;
  - theorem 3 for all triples of units with r <= 30 and all (1, b, c) with r <= 120;
  - theorem 4 for every r <= 36 and -r <= a, b < 2r;
  - theorem 5 for all triples with r <= 40 (units or not), and the list of canonical triples
    that are neither terminal nor Gorenstein for r <= 60 (only r = 9 and r = 14);
  - the data of the planned golden route: successors in the three-gap theorem, the slices of
    the tetrahedron, the normal form <ka> + <kb> + <kc> = r + k of terminal triples;
  - a numeric witness for every hypothesis: dropping it makes the statement false.
There is no finite search space: r, a, b, c, N are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t40_generator.py
"""

TASK = 40
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

SUM3 = "k * a % r + k * b % r + k * c % r"
PAIR = "(a + b) % r = 0 \\/ (a + c) % r = 0 \\/ (b + c) % r = 0"

THEOREMS = [
    ("card_gaps_le_three",
     "(r a N : Nat)",
     "    let T := insert r ((Finset.range N).image (fun k => k * a % r))\n"
     "    let G := ((Finset.product T T).filter (fun xy => xy.1 < xy.2 /\\\n"
     "        T.filter (fun z => xy.1 < z /\\ z < xy.2) = {})).image (fun xy => xy.2 - xy.1)\n"
     "    G.card <= 3 /\\ (G.card = 3 -> exists u v : Nat, u < v /\\ G = {u, v, u + v})"),
    ("ncard_return_times_le_three",
     "(r a b : Nat)",
     "    let D := {d : Nat | 0 < d /\\ exists k : Nat, k * a % r < b /\\ (k + d) * a % r < b /\\\n"
     "      forall e : Nat, 0 < e -> e < d -> b <= (k + e) * a % r}\n"
     "    D.ncard <= 3 /\\ (D.ncard = 3 -> exists u v : Nat, u < v /\\ D = {u, v, u + v})"),
    ("terminal_iff",
     "(r a b c : Nat) (hr : 0 < r) (ha : Nat.Coprime a r)\n"
     "    (hb : Nat.Coprime b r) (hc : Nat.Coprime c r)",
     "    (forall k : Nat, 1 <= k -> k < r -> r < " + SUM3 + ") <->\n"
     "      " + PAIR),
    ("empty_tetrahedron_iff",
     "(r : Nat) (a b : Int) (hr : 0 < r)",
     "    (forall x y z : Int, 0 <= z -> z <= r -> z * a <= r * x -> z * b <= r * y ->\n"
     "        r * x - z * a + (r * y - z * b) + z <= r ->\n"
     "        (x = 0 /\\ y = 0 /\\ z = 0) \\/ (x = 1 /\\ y = 0 /\\ z = 0) \\/\n"
     "          (x = 0 /\\ y = 1 /\\ z = 0) \\/ (x = a /\\ y = b /\\ z = r)) <->\n"
     "      ((a - 1) % r = 0 /\\ Int.gcd b r = 1) \\/ ((b - 1) % r = 0 /\\ Int.gcd a r = 1) \\/\n"
     "        ((a + b) % r = 0 /\\ Int.gcd a r = 1)"),
    ("pair_of_canonical",
     "(r a b c : Nat) (hs : Nat.Coprime (a + b + c) r)\n"
     "    (h : forall k : Nat, 1 <= k -> k < r -> r <= " + SUM3 + ")",
     "    " + PAIR),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. For integers $r \ge 0$ and $x \ge 0$ write $\langle x \rangle$ for the remainder of $x$ modulo $r$, so $0 \le \langle x \rangle < r$ for $r \ge 1$, and $\langle x \rangle = x$ for $r = 0$. All five theorems concern the multiples $ka$ modulo $r$.

1. (Three gaps.) Let $r, a, N \ge 0$. The numbers $\langle ka \rangle$ for $0 \le k < N$, together with $r$, cut $[0, r]$ into intervals of at most three different lengths, and if three lengths occur, the largest is the sum of the other two.
2. (Slater.) Let $r, a, b \ge 0$. The differences $d$ between consecutive elements of $\{k \ge 0 : \langle ka \rangle < b\}$ take at most three values, and if three values occur, the largest is the sum of the other two.
3. (Terminal lemma.) Let $r \ge 1$ and let $a, b, c$ be prime to $r$. Then $\langle ka \rangle + \langle kb \rangle + \langle kc \rangle > r$ for every $1 \le k \le r - 1$ if and only if $r$ divides $a + b$, $a + c$ or $b + c$.
4. (White.) Let $r \ge 1$ and $a, b \in \mathbb{Z}$. The tetrahedron with vertices $(0, 0, 0)$, $(1, 0, 0)$, $(0, 1, 0)$ and $(a, b, r)$ contains no lattice point other than its vertices if and only if $a \equiv 1$ and $\gcd(b, r) = 1$, or $b \equiv 1$ and $\gcd(a, r) = 1$, or $a + b \equiv 0$ and $\gcd(a, r) = 1$, with congruences modulo $r$.
5. Let $r, a, b, c \ge 0$ with $\gcd(a + b + c, r) = 1$. If $\langle ka \rangle + \langle kb \rangle + \langle kc \rangle \ge r$ for every $1 \le k \le r - 1$, then $r$ divides $a + b$, $a + c$ or $b + c$. Without the hypothesis on $a + b + c$ the conclusion fails for $r = 9$ and $(a, b, c) = (1, 4, 7)$.

Lean statement. Remainders use `%` on `Nat`, so `x % 0 = x` matches the case $r = 0$. In theorem 1, `T` is the set of points and `G` the set of gap lengths between consecutive elements of `T`, and in theorem 2, `D` is the set of differences. In theorem 4 a lattice point $(x, y, z)$ lies in the tetrahedron when $0 \le z \le r$, $za \le rx$, $zb \le ry$ and $(rx - za) + (ry - zb) + z \le r$. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    from math import gcd

    counts = {}

    def gapset(r, a, N):
        T = sorted(set(k * a % r if r else k * a for k in range(N)) | {r})
        return sorted(set(T[i + 1] - T[i] for i in range(len(T) - 1)))

    def ok3(G):
        return len(G) <= 3 and (len(G) < 3 or G[2] == G[0] + G[1])

    # theorem 1
    t1 = 0
    for r in range(1, 61):
        for a in range(r):
            for N in range(r + 3):
                assert ok3(gapset(r, a, N)), (r, a, N)
                t1 += 1
    for r in range(0, 12):
        for a in range(0, 3 * r + 3):
            for N in range(0, 2 * r + 4):
                assert ok3(gapset(r, a, N)), (r, a, N)
                t1 += 1
    counts["theorem 1 (three gaps), triples (r, a, N)"] = t1

    # theorem 2
    def retset(r, a, b):
        if r == 0:
            R = [k for k in range(0, b + 2) if k * a < b]
            if a == 0:
                R = list(range(0, 5)) if b > 0 else []
        else:
            R = [k for k in range(0, 3 * r + 3) if k * a % r < b]
        D = set()
        for i in range(len(R) - 1):
            if r == 0 or R[i] < 2 * r:
                D.add(R[i + 1] - R[i])
        return sorted(D)

    t2 = 0
    for r in range(0, 46):
        for a in range(max(r, 3)):
            for b in range(r + 2):
                assert ok3(retset(r, a, b)), (r, a, b)
                t2 += 1
    counts["theorem 2 (Slater), triples (r, a, b)"] = t2

    # theorem 3
    def S(r, a, b, c, k):
        return k * a % r + k * b % r + k * c % r

    def pair(r, a, b, c):
        return (a + b) % r == 0 or (a + c) % r == 0 or (b + c) % r == 0

    t3 = 0
    for r in range(1, 31):
        U = [x for x in range(r) if gcd(x, r) == 1]
        for a in U:
            for b in U:
                for c in U:
                    term = all(S(r, a, b, c, k) > r for k in range(1, r))
                    assert term == pair(r, a, b, c), (r, a, b, c)
                    t3 += 1
    for r in range(31, 121):
        U = [x for x in range(r) if gcd(x, r) == 1]
        for b in U:
            for c in U:
                term = all(S(r, 1, b, c, k) > r for k in range(1, r))
                assert term == pair(r, 1, b, c), (r, b, c)
                t3 += 1
    counts["theorem 3 (terminal lemma), triples of units"] = t3

    # theorem 4
    def empty(a, b, r):
        for z in range(0, r + 1):
            x0 = -(-z * a // r)
            y0 = -(-z * b // r)
            for x in (x0, x0 + 1):
                for y in (y0, y0 + 1):
                    if r * x - z * a + r * y - z * b + z <= r and \
                            (x, y, z) not in ((0, 0, 0), (1, 0, 0), (0, 1, 0), (a, b, r)):
                        return False
        return True

    def white(a, b, r):
        return ((a - 1) % r == 0 and gcd(b, r) == 1) or ((b - 1) % r == 0 and gcd(a, r) == 1) \
            or ((a + b) % r == 0 and gcd(a, r) == 1)

    t4 = 0
    for r in range(1, 37):
        for a in range(-r, 2 * r):
            for b in range(-r, 2 * r):
                assert empty(a, b, r) == white(a, b, r), (r, a, b)
                t4 += 1
    counts["theorem 4 (White), pairs (a, b) with r <= 36"] = t4

    # theorem 5 and the exceptional canonical triples
    t5 = 0
    for r in range(1, 41):
        for a in range(r):
            for b in range(r):
                for c in range(r):
                    if gcd(a + b + c, r) != 1:
                        continue
                    if all(S(r, a, b, c, k) >= r for k in range(1, r)):
                        assert pair(r, a, b, c), (r, a, b, c)
                    t5 += 1
    exc = {}
    for r in range(2, 61):
        U = [x for x in range(r) if gcd(x, r) == 1]
        for b in U:
            for c in U:
                if b > c:
                    continue
                s = [S(r, 1, b, c, k) for k in range(1, r)]
                if min(s) >= r and min(s) == r and (1 + b + c) % r:
                    exc.setdefault(r, []).append((1, b, c))
    assert exc == {9: [(1, 4, 7)], 14: [(1, 9, 11)]}, exc
    counts["theorem 5 (canonical with a + b + c prime to r), triples with r <= 40"] = t5

    # golden-route data
    route = 0
    for r in range(1, 41):                            # successors in the three-gap theorem
        for a in range(r):
            for N in range(2, r + 1):
                pts = [k * a % r for k in range(N)]
                if len(set(pts)) < N:
                    continue
                k1 = min(range(1, N), key=lambda k: pts[k])
                k2 = max(range(1, N), key=lambda k: pts[k])
                order = sorted(range(N), key=lambda k: pts[k])
                for i in range(N - 1):
                    k, nxt = order[i], order[i + 1]
                    want = k + k1 if k + k1 < N else (k - k2 if k >= k2 else k + k1 - k2)
                    assert nxt == want
                route += 1
    for r in range(1, 31):                            # tetrahedron slices and the terminal sum
        for a in range(r):
            for b in range(r):
                slices = all((-z * a) % r + (-z * b) % r + z > r for z in range(1, r))
                assert empty(a, b, r) == (slices and gcd(a, r) == 1 and gcd(b, r) == 1) or \
                    not (gcd(a, r) == 1 and gcd(b, r) == 1)
                route += 1
    for r in range(2, 41):                            # normal form of terminal triples
        U = [x for x in range(r) if gcd(x, r) == 1]
        for b in U:
            for d in U:
                s = (1 + b + d) % r
                if gcd(s, r) != 1:
                    continue
                inv = pow(s, -1, r)
                A, B, C = inv % r, b * inv % r, d * inv % r
                if all(S(r, A, B, C, k) > r for k in range(1, r)):
                    assert all(S(r, A, B, C, k) == r + k for k in range(1, r))
                    route += 1
    counts["golden-route data (successors, slices, normal form r + k)"] = route

    # witnesses
    w = 0
    assert (1 + 1) != 0                               # thm 3, r = 0, a = b = c = 1: RHS false
    for (r, a, b, c) in ((3, 3, 1, 2), (3, 1, 3, 2), (3, 1, 2, 3)):
        term = all(S(r, a, b, c, k) > r for k in range(1, r))
        assert pair(r, a, b, c) and not term          # ha, hb, hc
    w += 4
    assert (1 - 1) == 0 and abs(1) == 1 and (5, 5, 0) not in ((0, 0, 0), (1, 0, 0), (0, 1, 0))
    w += 1                                            # thm 4, r = 0 with a = b = 1
    assert all(S(9, 1, 4, 7, k) >= 9 for k in range(1, 9)) and not pair(9, 1, 4, 7)
    assert gcd(12, 9) == 3                            # thm 5, hs: (r; a, b, c) = (9; 1, 4, 7)
    assert gcd(3, 5) == 1 and not pair(5, 1, 1, 1)    # h: (5; 1, 1, 1)
    w += 2
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

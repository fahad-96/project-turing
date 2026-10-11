#!/usr/bin/env python3
"""Project Turing, task 36 generator (proof writing): Stern's diatomic sequence (Stern 1858,
Lucas 1878, Lehmer 1929, Carlitz 1964, Calkin and Wilf 2000, Northshield 2010).

s(0) = 0, s(1) = 1, s(2n) = s(n), s(2n + 1) = s(n) + s(n + 1). Theorems:
  1. s(n), s(n + 1) are coprime for n >= 1, and every coprime pair (a, b) of positive integers
     is (s(n), s(n + 1)) for exactly one n >= 1 (Stern, Calkin and Wilf)
  2. n <= 2^(k+1): s(n) <= F_(k+2), with equality iff 3n = 2^(k+2) - (-1)^k or
     3n = 5 * 2^k + (-1)^k (Lucas)
  3. t <= k + 1: exactly phi(t) numbers n with 2^k <= n < 2^(k+1) have s(n) = t
  4. s(n + 1) is the number of hyperbinary representations of n (digits 0, 1, 2)
  5. s(n') = s(n) for odd n, n' the binary reversal of n

Writes, next to this script:
  task36_prompt.txt              the prompt to paste into the platform
  TuringTask/Basic.lean          the five statements with `sorry`
  StatementAndAxiomsCheck.lean   used later to check submitted projects (worker check.lean)

Self-verifying with exact integer arithmetic (table of s up to 2^21):
  - theorem 1: coprimality for n < 2^21, the pairs (s(n), s(n + 1)) for n < 2^21 are pairwise
    distinct, and every coprime pair with a, b <= 150 is reached (the index n is found by
    descent and s is evaluated at n, which can exceed 2^100, from its binary digits);
  - theorem 2 for every k <= 19 and every n <= 2^(k+1);
  - theorem 3 for every k <= 20 and every t <= k + 1, and the threshold is sharp (t = k + 2
    fails for 3 <= t <= 21);
  - theorem 4 for n <= 100,000 against a direct count of the digit strings;
  - theorem 5 for every odd n < 2^21;
  - the data of the planned golden route: the matrix form of (s(n), s(n + 1)) along the binary
    digits, the descent of the Calkin-Wilf tree, and the depth of t/b in that tree;
  - a numeric witness for every hypothesis: dropping it makes the statement false (the zero
    function, the identity, the indicator of the powers of 2, the odd part of n, n > 2^(k+1),
    t > k + 1).
There is no finite search space: n, k, t, a, b are unbounded.
Asserts pure ASCII and Lean lines <= 100 characters.
Run:  python turing_t36_generator.py
"""

TASK = 36
COUNT_WORD = "five"
KEEP = "and the names and statements of the five theorems"
CHECK_KIND = "exact"

PRELUDE = ""

SEQ = ("(s : Nat -> Nat) (h1 : s 1 = 1)\n"
       "    (he : forall n, s (2 * n) = s n) (ho : forall n, s (2 * n + 1) = s n + s (n + 1))")

THEOREMS = [
    ("coprime_and_existsUnique_eq",
     SEQ,
     "    (forall n, 0 < n -> Nat.Coprime (s n) (s (n + 1))) /\\\n"
     "      forall a b, 0 < a -> 0 < b -> Nat.Coprime a b ->\n"
     "        ExistsUnique (fun n => 0 < n /\\ s n = a /\\ s (n + 1) = b)"),
    ("le_fib_and_eq_fib_iff",
     SEQ + "\n    (k n : Nat) (hn : n <= 2 ^ (k + 1))",
     "    s n <= Nat.fib (k + 2) /\\\n"
     "      (s n = Nat.fib (k + 2) <->\n"
     "        (3 * n : Int) = 4 * 2 ^ k - (-1) ^ k \\/ (3 * n : Int) = 5 * 2 ^ k + (-1) ^ k)"),
    ("card_filter_eq_totient",
     SEQ + "\n    (t k : Nat) (htk : t <= k + 1)",
     "    (Finset.filter (fun n => s n = t) (Finset.Ico (2 ^ k) (2 ^ (k + 1)))).card =\n"
     "      Nat.totient t"),
    ("eq_card_hyperbinary",
     SEQ + "\n    (n : Nat)",
     "    s (n + 1) =\n"
     "      (Finset.filter\n"
     "        (fun c : Fin (n + 1) -> Fin 3 =>\n"
     "          Finset.sum Finset.univ (fun i => (c i : Nat) * 2 ^ (i : Nat)) = n)\n"
     "        Finset.univ).card"),
    ("eq_of_reverse_digits",
     "(s : Nat -> Nat)\n"
     "    (he : forall n, s (2 * n) = s n) (ho : forall n, s (2 * n + 1) = s n + s (n + 1))\n"
     "    (n : Nat) (hn : n % 2 = 1)",
     "    s (Nat.ofDigits 2 (Nat.digits 2 n).reverse) = s n"),
]

DEF_CHECK = ""

PROMPT_BODY = r"""Create a Lean 4 project and prove the five theorems below in `@FILE@`. This is a proof-writing task.

Mathematical statement. Define Stern's diatomic sequence by $s(0) = 0$, $s(1) = 1$, $s(2n) = s(n)$ and $s(2n + 1) = s(n) + s(n + 1)$ for $n \ge 0$, so it begins $0, 1, 1, 2, 1, 3, 2, 3, 1, 4, \dots$. Let $F_j$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$) and $\varphi$ Euler's function.

1. (Stern, Calkin and Wilf.) For $n \ge 1$ the numbers $s(n)$ and $s(n + 1)$ are coprime, and for every pair of coprime integers $a, b \ge 1$ there is exactly one $n \ge 1$ with $s(n) = a$ and $s(n + 1) = b$.
2. (Lucas.) If $0 \le n \le 2^{k+1}$, then $s(n) \le F_{k+2}$, with equality if and only if $3n = 2^{k+2} - (-1)^k$ or $3n = 5 \cdot 2^k + (-1)^k$.
3. If $0 \le t \le k + 1$, then exactly $\varphi(t)$ integers $n$ with $2^k \le n < 2^{k+1}$ satisfy $s(n) = t$.
4. For $n \ge 0$, $s(n + 1)$ is the number of ways to write $n = \sum_{i \ge 0} c_i 2^i$ with all digits $c_i \in \{0, 1, 2\}$.
5. If $n$ is odd and $n'$ is the number whose binary digits are those of $n$ in reverse order, then $s(n') = s(n)$.

Lean statement. The sequence is a function `s : Nat -> Nat` with the hypotheses `h1`, `he` and `ho`, which determine it (they force $s(0) = 0$). Theorem 5 omits `h1`, since its conclusion holds for every multiple of $s$ as well. In theorem 1, `ExistsUnique` expresses "exactly one". In theorem 3, $\varphi$ is `Nat.totient`. In theorem 4 the digit strings are the functions `c : Fin (n + 1) -> Fin 3`, which suffices because $2^i > n$ for $i > n$. In theorem 5 the reversal of $n$ is `Nat.ofDigits 2 (Nat.digits 2 n).reverse`. Copy the five theorems below into `@FILE@` exactly as they appear, and replace each `sorry` with a complete proof.
"""

EXTRA_RULE = """Do not declare anything inside the namespace `@NS@` that shadows a Mathlib name. Every name in the five statements must keep its Mathlib meaning.
"""


def self_check() -> dict:
    """Exact tests of the five statements, of the data of the planned proof and of the
    witnesses for the hypotheses."""
    from math import gcd

    counts = {}
    N = 1 << 21
    s = [0] * (N + 2)
    s[1] = 1
    for n in range(1, (N + 2) // 2):
        if 2 * n < N + 2:
            s[2 * n] = s[n]
        if 2 * n + 1 < N + 2:
            s[2 * n + 1] = s[n] + s[n + 1]

    def stern(n):
        """s(n) and s(n + 1) from the binary digits of n (any size)."""
        a, b = 0, 1                              # (s(0), s(1))
        for bit in bin(n)[2:] if n else "":
            if bit == "0":                       # m -> 2m
                a, b = a, a + b
            else:                                # m -> 2m + 1
                a, b = a + b, b
        return a, b

    fib = [0, 1]
    for _ in range(80):
        fib.append(fib[-1] + fib[-2])

    route = 0
    for n in range(0, 1 << 16):                  # matrix form along the binary digits
        assert stern(n) == (s[n], s[n + 1])
        route += 1

    # theorem 1
    seen = set()
    for n in range(1, N):
        assert gcd(s[n], s[n + 1]) == 1
        key = (s[n], s[n + 1])
        assert key not in seen
        seen.add(key)
    t1 = N - 1
    for a in range(1, 151):
        for b in range(1, 151):
            if gcd(a, b) != 1:
                continue
            x, y, bits = a, b, []
            while (x, y) != (1, 1):              # descent in the Calkin-Wilf tree
                if x < y:
                    bits.append("0")
                    y -= x
                else:
                    bits.append("1")
                    x -= y
                route += 1
            n = int("1" + "".join(reversed(bits)), 2)
            assert stern(n) == (a, b)
            t1 += 1
    counts["theorem 1 (coprime, distinct pairs below 2^21, every coprime pair <= 150 reached)"] = t1

    # theorem 2
    t2 = 0
    for k in range(0, 20):
        for n in range(0, 2 ** (k + 1) + 1):
            eq = 3 * n == 4 * 2 ** k - (-1) ** k or 3 * n == 5 * 2 ** k + (-1) ** k
            assert s[n] <= fib[k + 2] and (s[n] == fib[k + 2]) == eq
            t2 += 1
    counts["theorem 2 (Lucas), pairs (k, n)"] = t2

    # theorem 3
    def totient(m):
        return sum(1 for j in range(1, m + 1) if gcd(j, m) == 1)
    t3 = 0
    for k in range(0, 21):
        cnt = {}
        for n in range(2 ** k, 2 ** (k + 1)):
            cnt[s[n]] = cnt.get(s[n], 0) + 1
        for t in range(0, k + 2):
            assert cnt.get(t, 0) == totient(t), (k, t)
            t3 += 1
        if 3 <= k + 2 <= 21:
            assert cnt.get(k + 2, 0) != totient(k + 2)
    counts["theorem 3 (phi(t) occurrences), pairs (k, t), and sharpness at t = k + 2"] = t3

    # theorem 4: direct count of the digit strings
    M = 100000
    h = [0] * (M + 1)
    h[0] = 1
    for n in range(1, M + 1):
        h[n] = sum(h[(n - c) // 2] for c in (0, 1, 2) if c <= n and (n - c) % 2 == 0)
    for n in range(0, M + 1):
        assert h[n] == s[n + 1]
    counts["theorem 4 (hyperbinary representations), n <= 100,000"] = M + 1

    # theorem 5
    t5 = 0
    for n in range(1, N, 2):
        r = int(bin(n)[2:][::-1], 2)
        assert s[r] == s[n]
        t5 += 1
    counts["theorem 5 (binary reversal), odd n < 2^21"] = t5
    counts["golden-route data (matrix form, Calkin-Wilf descent steps)"] = route

    # witnesses: functions satisfying all but one hypothesis
    zero = lambda n: 0                                   # he, ho; not h1
    ident = lambda n: n                                  # h1, ho; not he
    pow2 = lambda n: 1 if n > 0 and n & (n - 1) == 0 else 0      # h1, he; not ho
    oddpart = lambda n: n // (n & -n) if n else 0        # he; not ho
    for f in (zero, ident, pow2, oddpart):
        assert f(0) == 0
    assert all(zero(2 * n) == zero(n) and zero(2 * n + 1) == zero(n) + zero(n + 1)
               for n in range(100))
    assert ident(1) == 1 and all(ident(2 * n + 1) == ident(n) + ident(n + 1) for n in range(100))
    assert pow2(1) == 1 and all(pow2(2 * n) == pow2(n) for n in range(1, 100))
    assert all(oddpart(2 * n) == oddpart(n) for n in range(1, 100))
    assert ident(4) != ident(2) and pow2(3) != pow2(1) + pow2(2) and oddpart(3) != 2
    w = 0
    # theorem 1: zero (gcd(0, 0) = 0), identity and pow2 (the pair (2, 1) is never reached)
    assert gcd(zero(1), zero(2)) != 1
    assert not any((ident(n), ident(n + 1)) == (2, 1) for n in range(1, 100))
    assert not any((pow2(n), pow2(n + 1)) == (2, 1) for n in range(1, 1000))
    w += 3
    # theorem 2: zero at the maximum (k = 2, n = 5), identity (k = 3, n = 16 > F_5),
    # pow2 at the maximum (k = 2, n = 5), and n = 3 > 2^(0 + 1) with s(3) = 2 > F_2
    assert 3 * 5 == 4 * 4 - 1 and zero(5) != fib[4] and pow2(5) != fib[4]
    assert ident(16) > fib[5] and s[3] > fib[2]
    w += 4
    # theorem 3: zero and pow2 (t = 2, k = 1), identity (t = 3, k = 2), t = 5 with k = 3
    assert sum(1 for n in range(2, 4) if zero(n) == 2) != totient(2)
    assert sum(1 for n in range(2, 4) if pow2(n) == 2) != totient(2)
    assert sum(1 for n in range(4, 8) if ident(n) == 3) != totient(3)
    assert sum(1 for n in range(8, 16) if s[n] == 5) != totient(5)
    w += 4
    # theorem 4: n = 2 has two representations (2 = 2 * 1 = 1 * 2)
    assert h[2] == 2 and zero(3) != 2 and ident(3) != 2 and pow2(3) != 2
    w += 3
    # theorem 5: n = 11 (binary 1011) reverses to 13 (1101)
    assert int(bin(11)[2:][::-1], 2) == 13 and ident(13) != ident(11)
    assert oddpart(13) != oddpart(11)
    w += 2
    counts["witnesses for the 16 hypotheses (each one false when dropped)"] = w
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

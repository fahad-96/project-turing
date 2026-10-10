#!/usr/bin/env python3
"""humanize_scan.py - mechanical part of the Humanize_AI line check (HUMANIZE_AI_CHECKLIST.md).

Run it on every text that goes into a Project Turing submission field (task prompt, golden
explanation, rubric criteria, replies to reviewers) right after the text is generated:

    python humanize_scan.py task26_prompt.txt [more files ...]

or import it in a generator:  from humanize_scan import scan;  errors, warnings = scan(text)

What it checks (prose only: fenced ``` blocks, inline `code` and $...$ math are skipped, so Lean
syntax such as ->, /\\, | and ; inside code is never flagged):
  ERRORS (hard bans, must be rewritten):
    em dash, en dash, semicolon, vertical bar, arrows, in-line dots, a spaced hyphen used as a
    pause, contrast frames ("not just", "rather than", "X, not Y", "isn't just"), "e.g." together
    with "etc.", more than one colon in a sentence, the AI words of Section 6 and the
    hand-waving words of mathematical writing ("clearly", "obviously", "trivially", ...).
  WARNINGS (need a human decision; fix them or allow them explicitly with a reason):
    possible passive voice (is/are/was/were/be/been/being + participle), word/word slashes,
    filler openers ("Note that", "Moreover", "Furthermore", ...), "we"/"let us" narration.
The script cannot judge meaning. After it reports no errors, still read every line against the
twelve questions of Section 8 of the checklist.
"""
import re
import sys

AI_WORDS = [
    "delve", "delves", "delving", "tapestry", "landscape", "realm", "robust", "seamless",
    "seamlessly", "cutting-edge", "game-changer", "pivotal", "crucial", "crucially", "unlock",
    "unlocks", "unleash", "elevate", "empower", "harness", "leverage", "leverages", "leveraging",
    "synergy", "synergies", "holistic", "holistically", "ecosystem", "journey", "transformative",
    "paradigm", "spearhead", "bolster", "underscore", "underscores", "testament",
    "ever-evolving", "in today's fast-paced world", "it's worth noting", "it is worth noting",
    "plays a key role", "value-led", "step-up", "next-generation", "broad-based",
    "best-in-class", "industry-leading", "iconic", "tailwind", "headwind", "is in place",
    "key insight", "remarkably", "notably", "intricate", "meticulous", "meticulously",
    "showcase", "showcases", "navigate the", "in the realm of", "a myriad of", "plethora",
]
HANDWAVE = [
    "clearly", "obviously", "trivially", "it is easy to see", "it is clear that",
    "straightforward", "it follows easily", "one can easily", "simply note", "of course",
    "needless to say", "without loss of generality it is clear",
]
FILLER_OPENERS = [
    "note that", "moreover,", "furthermore,", "additionally,", "in conclusion,", "importantly,",
    "interestingly,", "in summary,", "overall,", "let us", "we now", "in this section",
    "it should be noted",
]
PARTICIPLE_EXCEPTIONS = {
    "even", "open", "seven", "eleven", "often", "ten", "then", "when", "own", "between",
    "golden", "need", "seed", "indeed", "speed", "red", "bed", "fed", "hundred", "kindred",
    "sacred", "naked", "wicked", "ragged", "rugged",
}
PASSIVE_RE = re.compile(
    r"\b(is|are|was|were|be|been|being)\s+(?:\w+ly\s+)?"
    r"(\w+ed|\w+en|built|made|done|shown|set|put|kept|known|seen|proved|found|left|held|"
    r"met|paid|sent|told|won|bought|brought|caught|taught|thought|run|sold|cut|read|split)\b",
    re.IGNORECASE)


def prose_only(text: str) -> str:
    """Blank out fenced code, inline code and $...$ math, keeping line structure."""
    out_lines = []
    in_fence = False
    for line in text.split("\n"):
        if line.strip().startswith("```"):
            in_fence = not in_fence
            out_lines.append("")
            continue
        if in_fence:
            out_lines.append("")
            continue
        line = re.sub(r"`[^`]*`", " CODE ", line)
        line = re.sub(r"\$\$[^$]*\$\$", " MATH ", line)
        line = re.sub(r"\$[^$]*\$", " MATH ", line)
        line = re.sub(r"https?://\S+", " URL ", line)
        out_lines.append(line)
    return "\n".join(out_lines)


def sentences(line: str):
    return [s for s in re.split(r"(?<=[.!?])\s+", line) if s.strip()]


def scan(text: str, allow=()):
    """Return (errors, warnings): lists of (line number, message, excerpt)."""
    errors, warnings = [], []
    prose = prose_only(text)
    allow = [a.lower() for a in allow]

    def add(kind, n, msg, excerpt):
        ex = excerpt.strip()
        if any(a in ex.lower() for a in allow):
            return
        (errors if kind == "E" else warnings).append((n, msg, ex[:110]))

    for n, line in enumerate(prose.split("\n"), 1):
        low = line.lower()
        if not line.strip():
            continue
        for ch, name in (("—", "em dash"), ("–", "en dash"), (";", "semicolon"),
                         ("|", "vertical bar"), ("→", "arrow"), ("•", "in-line dot"),
                         ("·", "in-line dot")):
            if ch in line:
                add("E", n, name, line)
        if re.search(r"(?<![-<])(-{1,2}>|=>)", line):
            add("E", n, "arrow", line)
        if re.search(r"\w\s+-\s+\w", line) and not re.search(r"\d\s+-\s+\d", line):
            add("E", n, "spaced hyphen used as a pause", line)
        for pat, name in ((r"\bnot just\b", "contrast frame 'not just'"),
                          (r"\brather than\b", "contrast frame 'rather than'"),
                          (r"\bisn't just\b", "contrast frame"),
                          (r",\s+not\s+(?:a|an|the|only|just|merely)\b", "contrast frame 'X, not Y'"),
                          (r"\bnot only\b.*\bbut also\b", "contrast frame 'not only ... but also'")):
            if re.search(pat, low):
                add("E", n, name, line)
        if "e.g." in low and "etc." in low:
            add("E", n, "'e.g.' together with 'etc.'", line)
        for s in sentences(line):
            core = re.sub(r"^\s*(?:[-*]|\d+\.)\s+", "", s)
            if core.count(":") > 1:
                add("E", n, "colon chain", s)
        for w in AI_WORDS:
            if re.search(r"(?<![\w-])" + re.escape(w) + r"(?![\w-])", low):
                add("E", n, "AI word '%s'" % w, line)
        for w in HANDWAVE:
            if re.search(r"(?<![\w-])" + re.escape(w) + r"(?![\w-])", low):
                add("E", n, "hand-waving '%s'" % w, line)
        for w in FILLER_OPENERS:
            if re.search(r"(?<![\w-])" + re.escape(w) + r"(?![\w-])", low):
                add("W", n, "filler or narration '%s'" % w, line)
        for m in PASSIVE_RE.finditer(line):
            word = m.group(2).lower()
            if word in PARTICIPLE_EXCEPTIONS:
                continue
            add("W", n, "possible passive '%s'" % m.group(0), line)
        for m in re.finditer(r"\b([A-Za-z]{2,})/([A-Za-z]{2,})\b", line):
            add("W", n, "slash '%s'" % m.group(0), line)
    return errors, warnings


def main(paths):
    bad = 0
    for p in paths:
        text = open(p, encoding="utf-8").read()
        errors, warnings = scan(text)
        print("== %s: %d errors, %d warnings" % (p, len(errors), len(warnings)))
        for n, msg, ex in errors:
            print("  ERROR   line %d: %s: %s" % (n, msg, ex))
        for n, msg, ex in warnings:
            print("  WARNING line %d: %s: %s" % (n, msg, ex))
        bad += len(errors)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

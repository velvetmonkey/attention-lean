#!/usr/bin/env python3
"""CI gate: fail if any `sorry` survives outside comments.

A bare  grep -rE '\\bsorry\\b' *.lean  false-fails on this repo: docstrings
legitimately contain the prose "no `sorry`" / "no sorry" (and English "admit",
which is why the guard never matched `admit` either). So this check strips
Lean comments first — `--` line comments and nested `/- ... -/` block comments
(including `/-- ... -/` docstrings) — and only then searches for the `sorry`
token. String literals are preserved verbatim so comment markers inside them
don't desynchronise the scanner.

Usage: check_no_sorry.py [path ...]   (default: AttentionLean/ AttentionLean.lean)
Exit 0 = clean, 1 = sorry found (offenders printed as file:line).
"""

import re
import sys
from pathlib import Path

SORRY = re.compile(r"\bsorry\b")


def strip_comments(text: str) -> str:
    """Remove Lean comments, preserving newlines (line numbers survive)."""
    out = []
    i, n = 0, len(text)
    depth = 0  # block-comment nesting
    in_string = False
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        c = text[i]
        if in_string:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if c == '"':
                in_string = False
            i += 1
            continue
        if c == '"':
            in_string = True
            out.append(c)
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(c)
        i += 1
    return "".join(out)


def lean_files(roots):
    for root in roots:
        p = Path(root)
        if p.is_dir():
            yield from sorted(p.rglob("*.lean"))
        elif p.suffix == ".lean":
            yield p


def main() -> int:
    roots = sys.argv[1:] or ["AttentionLean", "AttentionLean.lean"]
    bad = []
    for f in lean_files(roots):
        stripped = strip_comments(f.read_text(encoding="utf-8"))
        for lineno, line in enumerate(stripped.splitlines(), 1):
            if SORRY.search(line):
                bad.append(f"{f}:{lineno}: {line.strip()}")
    if bad:
        print("::error::sorry found outside comments:")
        print("\n".join(bad))
        return 1
    print(f"no sorry outside comments ({len(list(lean_files(roots)))} files checked)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

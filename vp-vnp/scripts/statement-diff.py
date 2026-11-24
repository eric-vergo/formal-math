# Released under Apache 2.0 license as described in the file LICENSE.
# SPDX-License-Identifier: Apache-2.0
"""Compare the statements of the Lean development between two Git revisions.

Usage, from this project's folder:

    python3 -I scripts/statement-diff.py [OLD [NEW]]

OLD defaults to `upstream/vp-vnp` and NEW to `HEAD`; NEW may be `WORKTREE` for the files on disk.

The files compared are Statement.lean, the Comparator challenge and solution, Paper.lean and every file
under Paper/. A challenge or solution at the project root in one revision is paired with the one under
Comparator/VpVnp/ in the other.

Comments are removed and runs of white space are made one space. Then each declaration is compared by
its full name (with its namespace):

- `theorem` and `lemma`: the text from the keyword to the first `:=` (the statement, without the proof);
- `def`, `abbrev`, `structure`, `class`, `inductive`, `instance` and `opaque`: the whole declaration,
  body included, since a definition's body is part of what a statement means;

and the other commands at the top level of a file (`import`, `open`, `variable`, `universe`, `namespace`,
`attribute`, `notation`, `set_option`, ...) are compared as a sequence per file. Every declaration and
file is listed as `same`, `changed` (with both texts), `only in OLD` or `only in NEW`.

Mathlib removed `MvPolynomial.coeff m p` (the coefficient of the monomial `m` in `p`); the same
coefficient is now written `p.coeff m`. A changed declaration is listed as `changed only in the spelling
of the coefficient` when its OLD text, with every `coeff A B` and `MvPolynomial.coeff A B` (not after
another `.`, with two arguments, each a name, a numeral or a bracketed group) rewritten to `B.coeff A`,
equals its NEW text; scripts/StatementSpelling.lean is the argument that the two spellings mean the
same. The exit status is 0 when everything is the same, 2 when every change is one of the coefficient's
spelling, and 1 otherwise.
"""

import re
import subprocess
import sys
from pathlib import Path

PROJECT = Path(__file__).resolve().parent.parent
MOVED = {
    "Challenge.lean": "Comparator/VpVnp/Challenge.lean",
    "Solution.lean": "Comparator/VpVnp/Solution.lean",
}
STATEMENT_KINDS = {"theorem", "lemma"}
DEFINITION_KINDS = {"def", "abbrev", "structure", "class", "inductive", "instance", "opaque"}
MODIFIERS = {"private", "protected", "noncomputable", "nonrec", "partial", "unsafe", "scoped", "local"}


def git(*args):
    return subprocess.run(["git", "-C", str(PROJECT), *args], check=True, capture_output=True,
                          text=True).stdout


def prefix():
    """The project folder relative to the repository root, ending in `/` (empty at the root)."""
    return git("rev-parse", "--show-prefix").strip()


def list_files(rev):
    if rev == "WORKTREE":
        names = [str(p.relative_to(PROJECT)) for p in PROJECT.rglob("*.lean")
                 if ".lake" not in p.parts]
    else:
        names = [n[len(prefix()):] for n in git("ls-tree", "-r", "--name-only", "--full-name", rev).splitlines()
                 if n.startswith(prefix())]
    wanted = []
    for n in names:
        if n in ("Statement.lean", "Paper.lean", "Challenge.lean", "Solution.lean") \
                or n in MOVED.values() or (n.startswith("Paper/") and n.endswith(".lean")):
            wanted.append(n)
    return sorted(wanted)


def read(rev, name):
    if rev == "WORKTREE":
        return (PROJECT / name).read_text(encoding="utf-8")
    return git("show", f"{rev}:{prefix()}{name}")


def strip_comments(text):
    """Remove `--` comments and nested `/- -/` comments, keeping string literals."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def norm(s):
    return " ".join(s.split())


def top_level_chunks(text):
    """Split comment-free text into commands: a command starts at a non-blank line in column 0 that does
    not begin with `|` (an alternative of the command above)."""
    chunks, cur = [], []
    for line in text.split("\n"):
        starts = line[:1] not in ("", " ", "\t", "|", ")", "]", "}")
        if starts and cur and not cur[-1].rstrip().endswith((" in", "@[")) \
                and not re.match(r"^\s*@\[[^\]]*\]\s*$", cur[-1]):
            chunks.append("\n".join(cur))
            cur = []
        cur.append(line)
    if cur:
        chunks.append("\n".join(cur))
    return [c for c in chunks if c.strip()]


DECL = re.compile(r"^((?:open [^\n]* in\s+)*(?:@\[[^\]]*\]\s*)*(?:(?:%s)\s+)*)(%s)\b\s*([^\s:({\[]*)"
                  % ("|".join(MODIFIERS), "|".join(sorted(STATEMENT_KINDS | DEFINITION_KINDS))))


def until_assign(s):
    """`s` up to the first `:=` outside brackets."""
    depth = 0
    for i, ch in enumerate(s):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and s.startswith(":=", i):
            return s[:i]
    return s


ATOM = re.compile(r"[^\s()\[\]{}⟨⟩,:=]+")
OPENERS, CLOSERS = "([{⟨", ")]}⟩"


def coeff_arg(s, i):
    """The argument of an application starting at `s[i]` (after spaces): its span, or None."""
    while i < len(s) and s[i] == " ":
        i += 1
    if i >= len(s):
        return None
    if s[i] in OPENERS:
        depth = 0
        for j in range(i, len(s)):
            if s[j] in OPENERS:
                depth += 1
            elif s[j] in CLOSERS:
                depth -= 1
                if depth == 0:
                    return i, j + 1
        return None
    m = ATOM.match(s, i)
    if not m or m.group(0) in ("fun", "if", "then", "else", "by", "with", "from", "at", "↔", "∧", "∨", "→"):
        return None
    return i, m.end()


def respell_coeff(s):
    """`s` with every `coeff A B` (old `MvPolynomial.coeff`) written `B.coeff A`."""
    out, i = [], 0
    pat = re.compile(r"(?<![\w.'])(?:MvPolynomial\.)?coeff(?![\w'])")
    while (m := pat.search(s, i)):
        a = coeff_arg(s, m.end())
        b = coeff_arg(s, a[1]) if a else None
        if not b:
            out.append(s[i:m.end()])
            i = m.end()
            continue
        A, B = s[a[0]:a[1]], s[b[0]:b[1]]
        if B[0] not in OPENERS and not re.fullmatch(r"[^\W\d][\w'.]*", B):
            B = "(" + B + ")"
        out.append(s[i:m.start()] + f"{B}.coeff {A}")
        i = b[1]
    out.append(s[i:])
    return "".join(out)


def parse(text):
    decls, context, ns = {}, [], []
    for chunk in top_level_chunks(strip_comments(text)):
        flat = norm(chunk)
        m = DECL.match(flat)
        if m:
            kind, name = m.group(2), m.group(3)
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            elif name:
                full = ".".join(ns + [name])
            else:
                full = ".".join(ns + [f"<{kind} at {norm(flat)[:60]}>"])
            body = until_assign(flat) if kind in STATEMENT_KINDS else flat
            key = full
            while key in decls:
                key += "'"
            decls[key] = (kind, body)
            continue
        word = flat.split(" ", 1)[0]
        if word == "namespace":
            ns.extend(flat.split(" ", 1)[1].split("."))
        elif word == "end" and len(flat.split()) > 1 and ns:
            for _ in flat.split()[1].split("."):
                if ns:
                    ns.pop()
        context.append(flat)
    return decls, context


def main():
    old = sys.argv[1] if len(sys.argv) > 1 else "upstream/vp-vnp"
    new = sys.argv[2] if len(sys.argv) > 2 else "HEAD"
    old_files, new_files = list_files(old), list_files(new)
    pairs, seen = [], set()
    for f in old_files:
        g = f if f in new_files else MOVED.get(f, f)
        if g not in new_files:
            g = next((k for k, v in MOVED.items() if v == f and k in new_files), g)
        pairs.append((f, g if g in new_files else None))
        seen.add(g)
    pairs += [(None, g) for g in new_files if g not in seen]

    counts = {"same": 0, "changed only in the spelling of the coefficient": 0, "changed": 0,
              "only in OLD": 0, "only in NEW": 0}
    print(f"OLD = {old}  NEW = {new}")
    for f, g in pairs:
        label = f if f == g else f"{f} -> {g}"
        if f is None or g is None:
            print(f"FILE only in {'NEW' if f is None else 'OLD'}: {g or f}")
            counts["only in NEW" if f is None else "only in OLD"] += 1
            continue
        d_old, c_old = parse(read(old, f))
        d_new, c_new = parse(read(new, g))
        lines = []
        for key in list(d_old) + [k for k in d_new if k not in d_old]:
            a, b = d_old.get(key), d_new.get(key)
            if a is None or b is None:
                where = "NEW" if a is None else "OLD"
                counts[f"only in {where}"] += 1
                lines.append(f"  only in {where}: {(a or b)[0]} {key}\n      {(a or b)[1]}")
            elif a == b:
                counts["same"] += 1
            elif (a[0], respell_coeff(a[1])) == b:
                counts["changed only in the spelling of the coefficient"] += 1
                lines.append(f"  changed only in the spelling of the coefficient: {a[0]} {key}\n"
                             f"    OLD: {a[1]}\n    NEW: {b[1]}")
            else:
                counts["changed"] += 1
                lines.append(f"  changed: {a[0]} {key}\n    OLD: {a[1]}\n    NEW: {b[1]}")
        if c_old != c_new:
            counts["changed"] += 1
            lines.append("  changed: top-level commands\n    OLD: " + " | ".join(c_old)
                         + "\n    NEW: " + " | ".join(c_new))
        else:
            counts["same"] += 1
        n = len(d_old.keys() | d_new.keys())
        print(f"{label}: {n} declarations" + (", all the same" if not lines else ""))
        for line in lines:
            print(line)
    print("summary: " + ", ".join(f"{v} {k}" for k, v in counts.items())
          + " (declarations, plus one entry per file for its top-level commands)")
    if counts["changed"] + counts["only in OLD"] + counts["only in NEW"]:
        return 1
    return 2 if counts["changed only in the spelling of the coefficient"] else 0


if __name__ == "__main__":
    sys.exit(main())

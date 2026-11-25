#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Eric Vergo, GPT-6.2 (OpenAI)
"""Measure proof source at each handback using the inventory's Lean lexer."""

from collections import Counter
import subprocess

from compare import PROOF_LIBRARIES, table
from inventory import DECL_COMMAND, IMPORT, ROOT, category, lean_stats, tracked


CHECKPOINTS = [
    ("Lean 4.36 port", "9fd368ad"),
    ("First Codex cleanup", "eeff2161"),
    ("Fable handback", "46be9c22"),
    ("Post-handback structural cleanup", "b80177f5"),
    ("Finite joint laws, circuit bounds and import reductions", "9476013c"),
    ("Frozen proof", "34a07262"),
]


def measure(revision, seen):
    full, tree = tracked(revision)
    result = Counter()
    modules = [entry for entry in tree if entry[0].startswith("vp-vnp/")
               and entry[0].endswith(".lean") and category(entry[0][7:])[0] in PROOF_LIBRARIES]
    missing = list(dict.fromkeys(oid for _, _, _, oid, _ in modules if oid not in seen))
    if missing:
        blobs = subprocess.run(["git", "-C", ROOT, "cat-file", "--batch"], input="".join(
            f"{oid}\n" for oid in missing).encode(), capture_output=True, check=True).stdout
        offset = 0
        for oid in missing:
            end = blobs.index(b"\n", offset)
            name, kind, length = blobs[offset:end].split()
            assert name.decode() == oid and kind == b"blob"
            raw = blobs[end + 1:end + 1 + int(length)]
            source = raw.decode()
            loc, masked = lean_stats(source, len(source))
            imports = IMPORT.findall(masked)
            seen[oid] = Counter(**loc, files=1, bytes=len(raw), declarations=len(DECL_COMMAND.findall(masked)),
                                imports=len(imports), umbrella=imports.count("Mathlib"))
            offset = end + 2 + len(raw)
    for _, _, _, oid, _ in modules:
        result.update(seen[oid])
    return full, result


def main():
    seen, rows, previous = {}, [], None
    for stage, revision in CHECKPOINTS:
        full, result = measure(revision, seen)
        rows.append([stage, f"`{full[:12]}`", *[f"{result[key]:,}" for key in (
            "files", "physical", "code", "comment", "mixed", "blank", "bytes", "declarations", "imports", "umbrella")],
                     "—" if previous is None else f"{result['physical'] - previous:+,}"])
        previous = result["physical"]
    print("# Proof source by round\n")
    print("Counts cover Nc, NS1, Ov and Paper, including Paper.lean. Mixed lines appear in both code and "
          "comment columns. Imports count written import commands matched by the inventory lexer. "
          "The umbrella column counts direct imports of the module named Mathlib. "
          "The last column compares consecutive rows.\n")
    table(["Stage", "Revision", "Files", "Physical", "Code", "Comment", "Mixed", "Blank", "Bytes",
           "Declaration commands", "Imports", "Umbrella", "Physical Δ"], rows)


if __name__ == "__main__":
    main()

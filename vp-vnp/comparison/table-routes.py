#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Eric Vergo, GPT-6.2 (OpenAI)
"""Audit each Table 3 declaration against InventoryKernel's compiled export closures."""
import argparse
import json
import re
import sys
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("kernel", type=Path)
parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
args = parser.parse_args()
data = json.loads(args.kernel.read_text())
exports = {
    letter: dict(data["exports"]["Solution." + name])
    for letter, name in zip("MSACR", ("mainTheorem", "separation", "mainTheoremApprox",
                                      "separationClosure", "permanent_over_real"))
}
modules = {name: mod for mod, names in data["localDeclarations"].items() for name in names}
table = args.root / "blueprint/VpVnpBlueprint/Chapters/TableThree.lean"
docs = "\n".join(path.read_text() for path in (args.root / "blueprint").rglob("*.lean")
                 if "Generated" not in path.parts)
nodes = set(re.findall(r'^:{3,}\w+ "([^"]+)"', docs, re.M))
generated_part = args.root / "blueprint/VpVnpBlueprint/Generated/Part.lean"
tags = set(re.findall(r'tag := "([^"]+)"', docs + generated_part.read_text()))
errors = []
for kind, target in re.findall(r'\{(bpref|ref) "([^"]+)"', table.read_text()):
    if target not in (nodes if kind == "bpref" else tags):
        errors.append(f"Unresolved {kind} target in Table 3: {target}")
for path in re.findall(r'\{repoFile "([^"]+)"', docs):
    if not (args.root.parent / path).exists():
        errors.append(f"Missing linked source: {path}")
paper_rows = set()
print("row\tdeclaration\tsource\texports\tprinted_label")
for block in re.findall(r"^:::table \+header\n(.*?)^:::$", table.read_text(), re.M | re.S):
    for row in re.split(r"^\*\n", block, flags=re.M)[2:]:
        cells = re.findall(r"^  \* (.*)$", row, re.M)
        if len(cells) == 6:
            title = cells[0].split("[", 1)[-1].rstrip("]")
            names_cell, label = cells[2], cells[4]
            if title in paper_rows:
                errors.append(f"Repeated paper row: {title}")
            paper_rows.add(title)
        elif len(cells) == 4:
            title, names_cell, label = "unnumbered", cells[0], cells[2]
        else:
            raise ValueError(f"Unexpected columns: {cells}")
        names = re.findall(r"\{InlineLean.name\}`([^`]+)`", names_cell)
        if not names:
            if names_cell != "not formalized" or label != "—":
                raise ValueError(cells)
            print(title, "—", "—", "—", label, sep="\t")
        for i, name in enumerate(names):
            source = Path(modules[name].replace(".", "/") + ".lean")
            flags = " ".join(letter for letter, closure in exports.items() if name in closure)
            expected = {"all five": "M S A C R", "yes": "M S A C R",
                        "none": "", "no": ""}.get(label, label.removeprefix("yes: "))
            if not (args.root / source).is_file():
                errors.append(f"{title}: {source} does not exist")
            if i == 0 and label != "definition" and flags != expected:
                errors.append(f"{title}, {name}: printed {label!r}, compiled {flags or 'none'!r}")
            print(title, name, source, flags or "none", label if i == 0 else "secondary", sep="\t")
if len(paper_rows) != 72:
    errors.append(f"Expected 70 numbered rows and two displays, found {len(paper_rows)} rows")
for error in errors:
    print(error, file=sys.stderr)
raise SystemExit(int(bool(errors)))

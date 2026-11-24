#!/usr/bin/env python3
"""Audit each Table 3 declaration against InventoryKernel's compiled export closures."""
import argparse
import json
import re
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
failed = False
print("row\tdeclaration\tsource\texports\tprinted_label")
for block in re.findall(r"^:::table \+header\n(.*?)^:::$", table.read_text(), re.M | re.S):
    for row in re.split(r"^\*\n", block, flags=re.M)[2:]:
        cells = re.findall(r"^  \* (.*)$", row, re.M)
        if len(cells) == 6:
            title = cells[0].split("[", 1)[-1].rstrip("]")
            names_cell, label = cells[2], cells[4]
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
            failed |= not (args.root / source).is_file()
            failed |= i == 0 and label != "definition" and flags != expected
            print(title, name, source, flags or "none", label if i == 0 else "secondary", sep="\t")
raise SystemExit(int(failed))

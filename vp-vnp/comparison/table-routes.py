#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Eric Vergo, GPT-6.2 (OpenAI)
"""Audit each Table 3 declaration against InventoryKernel's compiled export closures."""
import argparse
import hashlib
import json
import re
import sys
from runpy import run_path
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("kernel", type=Path)
parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
parser.add_argument("--baseline-root", type=Path,
                    help="compare primary paper-row declaration texts with the pinned port tree")
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
tags = set(re.findall(r'tag := "([^"]+)"', docs + (generated_part.read_text() if generated_part.exists() else "")))
if not generated_part.exists():
    generator = (args.root / "blueprint/scripts/GenerateNodes.lean").read_text()
    if r'tag := \"part-generated\"' in generator:
        tags.add("part-generated")
errors = []
for kind, target in re.findall(r'\{(bpref|ref) "([^"]+)"', table.read_text()):
    if target not in (nodes if kind == "bpref" else tags):
        errors.append(f"Unresolved {kind} target in Table 3: {target}")
for path in re.findall(r'\{repoFile "([^"]+)"', docs):
    if not (args.root.parent / path).exists():
        errors.append(f"Missing linked source: {path}")
paper_rows = set()

def public_declarations(root):
    parse = run_path(str(args.root / "scripts/statement-diff.py"))["parse"]
    declarations = {}
    for path in [*(root / "Paper").rglob("*.lean"), *(root / "NS1").rglob("*.lean")]:
        for name, (_, body) in parse(path.read_text())[0].items():
            short = name.rsplit(".", 1)[-1]
            declarations.setdefault(short, []).append(body)
    return declarations

# Fingerprints cover the normalized primary statements whose signatures changed.
# The prose beside each row explains the mathematical difference.
changed = {
    "Lemma A.3": ("lem_hubs", "f04c9afcd662ba4850ed"),
    "Proposition E.5": ("prop_flat_lower", "c1d2319b6189954f8ae5"),
    "Proposition J.2": ("prop_pieces", "2d933af81f82d6904bf8"),
    "Lemma K.3": ("lem_circuit", "3c1dc8cd7c79fc5ca802"),
    "Proposition K.5": ("prop_next", "adcb36c55d32125fc52f"),
    "Lemma N.2": ("lem_transfer_approx", "e3b55fc98d5fa2f31b33"),
}
boundaries = {"Proposition E.5": "partial", "Theorem H.2": "partial",
              "Lemma K.3": "approximate analogue", "Proposition K.5": "approximate analogue",
              "Remark N.6": "no Lean counterpart"}
if args.baseline_root:
    before = public_declarations(args.baseline_root)
    after = public_declarations(args.root)
print("row\tdeclaration\tsource\texports\tprinted_label\tcoverage")
for block in re.findall(r"^:::table \+header\n(.*?)^:::$", table.read_text(), re.M | re.S):
    for row in re.split(r"^\*\n", block, flags=re.M)[2:]:
        cells = re.findall(r"^  \* (.*)$", row, re.M)
        if len(cells) == 6:
            title = cells[0].split("[", 1)[-1].rstrip("]")
            names_cell, coverage, label = cells[2:5]
            if (coverage in boundaries.values() or title in boundaries) and boundaries.get(title) != coverage:
                errors.append(f"{title}: incorrect scope {coverage!r}")
            if title in paper_rows:
                errors.append(f"Repeated paper row: {title}")
            paper_rows.add(title)
        elif len(cells) == 4:
            title, names_cell, label, coverage = "unnumbered", cells[0], cells[2], "working form"
        else:
            raise ValueError(f"Unexpected columns: {cells}")
        names = re.findall(r"\{InlineLean.name\}`([^`]+)`", names_cell)
        if not names:
            if names_cell != "not formalized" or label != "—":
                raise ValueError(cells)
            print(title, "—", "—", "—", label, coverage, sep="\t")
        if args.baseline_root and len(cells) == 6 and names:
            primary = names[0]
            short = primary.rsplit(".", 1)[-1]
            original = changed.get(title, (short, ""))[0]
            if title == "Definition K.1":
                original = "def_acc"
            if len(before.get(original, [])) != 1 or len(after.get(short, [])) != 1:
                errors.append(f"{title}: cannot identify the statements for {original} and {primary}")
            elif title in changed:
                digest = hashlib.sha256(after[short][0].encode()).hexdigest()[:20]
                if digest != changed[title][1]:
                    errors.append(f"{title}: recheck the changed statement for {primary}")
            elif before.get(short) != after[short]:
                errors.append(f"{title}: changed primary declaration {primary}")
        for i, name in enumerate(names):
            if name not in modules:
                errors.append(f"{title}: missing declaration {name}")
                continue
            source = Path(modules[name].replace(".", "/") + ".lean")
            flags = " ".join(letter for letter, closure in exports.items() if name in closure)
            expected = {"all five": "M S A C R", "yes": "M S A C R",
                        "none": "", "no": ""}.get(label, label.removeprefix("yes: "))
            if not (args.root / source).is_file():
                errors.append(f"{title}: {source} does not exist")
            if i == 0 and flags != expected:
                errors.append(f"{title}, {name}: printed {label!r}, compiled {flags or 'none'!r}")
            print(title, name, source, flags or "none", label if i == 0 else "secondary", coverage, sep="\t")
counts = dict(zip(("1", "2", *"ABCDEFGHIJKLMN"), (4, 2, 8, 3, 4, 2, 11, 6, 2, 2, 2, 4, 7, 3, 4, 6)))
expected_rows = {f"{section}.{n}" for section, count in counts.items() for n in range(1, count + 1)}
expected_rows.update(("(B.2)", "(F.1)"))
actual_rows = {title.split()[-1] for title in paper_rows}
if actual_rows != expected_rows or len(paper_rows) != 72:
    errors.append(f"Paper directory mismatch: {sorted(expected_rows ^ actual_rows)}")
if args.baseline_root:
    for root, expected_layer_field in ((args.baseline_root, True), (args.root, False)):
        tree = (root / "Paper/Tree.lean").read_text()
        if bool(re.search(r"^  layers_le :", tree, re.M)) != expected_layer_field:
            errors.append(f"Theorem H.2: recheck the law-layer clause in {root}")
for error in errors:
    print(error, file=sys.stderr)
raise SystemExit(int(bool(errors)))

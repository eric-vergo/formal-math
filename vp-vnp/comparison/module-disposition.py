#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Eric Vergo, GPT-6.2 (OpenAI)
"""Relate every baseline proof module to its after source and documented review."""

import argparse
from collections import Counter
from pathlib import Path
import re
from urllib.parse import quote

from compare import PROOF_LIBRARIES, REPO, load, table


DISPOSITIONS = {
    "Nc/CaseI/Cube.lean": ("Combined", "`Nc/CaseI/Geo.lean`", "The opposite-corners argument lives with the geometric construction."),
    "Nc/Cat/Prod.lean": ("Combined", "`Nc/Cat/Core.lean`", "The product metric belongs with the CAT space primitives."),
    "Nc/Cat/Space.lean": ("Combined", "`Nc/Cat/Core.lean`", "The convexity, metric-depth and midpoint definitions share their core module."),
    "Nc/Cross/One.lean": ("Combined", "`Nc/Cross/Psi.lean`", "The determinant and ordered-tuple arguments live with the crossing polynomial that uses them."),
    "Nc/Cut/StartB.lean": ("Deleted", "Mathlib identities", "The cut uses the library sum and conjunction identities directly."),
    "Nc/Dl/Cost.lean": ("Combined", "`Nc/Dl/GrpCost.lean`, `Nc/Grp/Script.lean`", "Dealing uses the producer’s group evaluator cost model and defines its remaining costs at the caller."),
    "Nc/End/ApproxThm.lean": ("Deleted", "`Nc/Rate/Circuit.lean`", "The existing universe-polymorphic affine substitution theorem covers these callers."),
    "Nc/Flag/Cases.lean": ("Combined", "`Paper/Alternative.lean`", "`Paper.Flat` now states the geometric predicate directly."),
    "Nc/Flag/Num.lean": ("Moved", "`Paper/Groups.lean`", "The needed window decay estimate is proved at its application."),
    "Nc/G/RouteFacts.lean": ("Deleted", "`Nc/G/Move.lean`, `Nc/G/PlayThm.lean`", "The remaining caller uses `Plan.mem_seenAt_end`. Other duplicated membership facts were removed."),
    "Nc/Plus/UnitBits.lean": ("Combined", "`Nc/Cut/Units.lean`", "Packet-bit sizes live beside the packet encoding."),
}

SPLITS = {
    "Paper/Approximate.lean": (("Paper/BorderRate.lean",),
                               "The shared coefficientwise estimate lives below the separately stated approximate endpoint."),
    "Paper/Fields.lean": (("Paper/BorderRate.lean",),
                           "Exact bounds consume the common characteristic-dependent border estimate."),
    "Paper/Tree.lean": (("Paper/Tree/Network.lean", "Paper/Tree/Construction.lean", "Paper/Tree/Bounds.lean"),
                        "Assembly imports the specification, construction and quantitative estimates."),
}


def project_modules(inventory):
    blobs = {f["path"].removeprefix("vp-vnp/"): f["git_oid"] for f in inventory["tracked_files"]
             if f["path"].startswith("vp-vnp/")}
    return {f["path"]: {**f, "blob": blobs[f["path"]]} for f in inventory["project_files"]
            if f["library"] in PROOF_LIBRARIES and f["path"] != "Paper.lean"}


def read_reviews(directory, paths):
    contracting = (directory / "contracting.md").read_text()
    first, second = contracting.split("## Second cohort:", 1)
    contracting_names = set(re.findall(r"^## ([\w/]+\.lean)$", first, re.M))
    contracting_names.update(f"{p}.lean" for p in re.findall(r"^- ([\w/]+):", second, re.M))
    flat = (directory / "flat.md").read_text().split("## Complete baseline coverage", 1)[1]
    flat_names = set(re.findall(r"^([\w/]+\.lean)$", flat, re.M))
    groups = (directory / "groups.md").read_text()
    group_names = {p for p in paths if p.startswith("Nc/Grp/")}
    for dealing in re.findall(r"^- Dl/([\w, ]+) —", groups, re.M):
        group_names.update(f"Nc/Dl/{p}.lean" for p in dealing.split(", "))
    network = (directory / "network.md").read_text()
    network_levels = dict(re.findall(r"^- ([\w/]+\.lean) — ([^\n]+)$", network, re.M))
    transfer = directory / "comparison.md"
    if transfer.is_file():
        transferred = set(re.findall(r"^- ([\w/]+\.lean) — full proof-body read\b", transfer.read_text(), re.M))
        if len(transferred) != 17 or not transferred <= network_levels.keys():
            raise ValueError("transferred modules must match their entries in the network ledger")
        network_levels.update(dict.fromkeys(transferred, "full proof-body read"))
    ledger = {}
    for cohort, reviewed in (("Contracting", contracting_names), ("Flat/common", flat_names), ("Group/dealing", group_names)):
        for path in sorted(reviewed):
            if path in ledger:
                raise ValueError(f"overlapping full-review cohorts at {path}")
            ledger[path] = (cohort, "Full proof-body/definition read")
    for path, level in network_levels.items():
        depth = "Full proof-body/definition read" if level.startswith("full proof-body read") else level.capitalize()
        ledger.setdefault(path, ("Network/machine", depth))
    if set(ledger) != paths:
        raise ValueError(f"review paths differ; missing {sorted(paths - ledger.keys())}; extra {sorted(ledger.keys() - paths)}")
    return ledger


def url(inventory, path):
    return f"{REPO}/blob/{inventory['revision']}/vp-vnp/{quote(path)}"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ("before", "after", "reviews"):
        parser.add_argument(f"--{option}", required=True, type=Path)
    args = parser.parse_args()
    before, after = load(args.before), load(args.after)
    old, new = map(project_modules, (before, after))
    if len(old) != 319:
        raise ValueError("the baseline proof corpus must contain 319 modules excluding the Paper umbrella")
    reviewers = read_reviews(args.reviews, set(old))
    rows, decisions, coverage = [], Counter(), Counter()
    for path, baseline in sorted(old.items()):
        current = new.get(path)
        status, dest, note = DISPOSITIONS.get(path, (None, None, None))
        extensions, split_explanation = SPLITS.get(path, ((), None))
        if extensions and all(extension in new for extension in extensions):
            status, note = "Split", split_explanation
            dest = ", ".join(f"[`{target}`]({url(after, target)})" for target in (path, *extensions))
        if current is None and status not in {"Deleted", "Combined", "Moved"}:
            raise ValueError(f"removed module missing disposition: {path}")
        if current is not None and status in {"Deleted", "Combined", "Moved"}:
            raise ValueError(f"removed module still present: {path}")
        decision = status or ("Retained, edited" if current["blob"] != baseline["blob"] else "Retained, byte-identical")
        decisions[decision] += 1
        cohort, depth = reviewers[path]
        coverage[cohort, depth] += 1
        old_path = f"[`{path}`]({url(before, path)})"
        new_path = dest or f"[same path]({url(after, path)})"
        rows.append([old_path, decision, new_path, cohort, depth, note or "—"])
    print("# Disposition of the 319 baseline proof modules\n")
    print(f"Before `{before['revision']}`\n\nAfter `{after['revision']}`\n")
    print("The `Paper.lean` umbrella, public specification, Comparator, blueprint and report tooling have their own project inventory entries.\n")
    table(["Outcome", "Modules"], sorted(decisions.items()))
    table(["Review cohort", "Documented depth", "Modules"], [[*key, n] for key, n in sorted(coverage.items())])
    print("The review ledgers preserve mathematical decisions and focused checks. The cohort totals assign overlapping group/dealing files to the group/dealing reviewer and include the tower and cut transfer in the network/machine cohort. The two revision inventories provide exact blob IDs for the source dispositions.\n")
    print("- [Contracting](reviews/contracting.md)\n- [Flat and common](reviews/flat.md)\n- [Group and dealing](reviews/groups.md)\n- [Network and machine](reviews/network.md)")
    if (args.reviews / "comparison.md").is_file():
        print("- [Tower and cut proofs](reviews/comparison.md)")
    print()
    print("## Baseline proof modules\n")
    table(["Baseline source", "Outcome", "After location", "Review cohort", "Documented depth", "Retained mathematics"], rows)
    print("## Added proof module paths\n")
    for path in sorted(new.keys() - old.keys()):
        print(f"- [`{path}`]({url(after, path)})")
    print("\n## Other tracked additions in the measured project\n")
    for path in sorted({f["path"] for f in after["project_files"]} - {f["path"] for f in before["project_files"]} - new.keys()):
        print(f"- [`{path}`]({url(after, path)})")


if __name__ == "__main__":
    main()

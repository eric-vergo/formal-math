#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Eric Vergo, GPT-6.2 (OpenAI)
"""Render the reproducible tables for two pinned vp-vnp inventories."""

import argparse
from collections import Counter
from functools import cache
import gzip
import json
from math import ceil
from pathlib import Path
import statistics
from urllib.parse import quote


PROOF_LIBRARIES = {"Nc", "NS1", "Ov", "Paper"}
EXPORTS = {
    "M": "mainTheorem", "S": "separation", "A": "mainTheoremApprox",
    "C": "separationClosure", "R": "permanent_over_real",
}
REPO = "https://github.com/eric-vergo/formal-math"
EXAMPLES = [
    ("Real permanent bound", ["Paper.thm_main"], ["Paper.thm_main"]),
    ("Exact lower bound over every field", ["Paper.thm_allfields"], ["Paper.thm_allfields"]),
    ("Real polynomial and class corollaries", ["Paper.thm_simple", "Paper.cor_classes"],
     ["Paper.thm_simple", "Paper.cor_classes"]),
    ("Flat polynomial lower bound", ["Paper.thm_flat_simple"], ["Paper.thm_flat_simple"]),
    ("Flat displacement estimate", ["Paper.prop_flat_lower_lengths"], ["Paper.prop_flat_lower_lengths"]),
    ("One-cut assembly", ["Paper.thm_onecut"], ["Paper.thm_onecut"]),
    ("Tape automaton piece bounds", ["Paper.prop_pieces"], ["Paper.prop_pieces"]),
    ("Guarded sum of states", ["Nc.Dl.mem_execAll"], ["Nc.Dl.mem_execAll"]),
    ("Thin-tree existence", ["Paper.exists_thinTrees"], ["Paper.exists_thinTrees"]),
    ("Formula decoder inversion", [f"Nc.Uni.inv_{constructor}" for constructor in
                                  ("quote", "id", "hd", "tl", "cons", "ite", "run", "guess", "fail", "theta", "mul")],
     ["NS1.Fm.codeShape_of_decode"]),
    ("Permanent VNP witness", ["Paper.perm_mem_VNP"], ["Paper.perm_mem_VNP", "Nc.Hc.mem_VNP_of_quartic_witness"]),
]


def load(path):
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt") as stream:
        return json.load(stream)


def table(headers, rows):
    def line(items):
        return "| " + " | ".join(str(item) for item in items) + " |"

    print(line(headers))
    print(line(["---"] * len(headers)))
    for row in rows:
        print(line(row))
    print()


def change(before, after):
    return [f"{before:,}", f"{after:,}", f"{after - before:+,}" if before != after else "0"]


def paired(label, before, after):
    print(f"### {label}\n")
    table(["Measure", "Before", "After", "Δ"], [
        [metric, *change(before.get(metric, 0), after.get(metric, 0))]
        for metric in dict.fromkeys([*before, *after])
    ])


def scope(files):
    metrics = Counter({"Tracked files": len(files), "Bytes": sum(f["bytes"] for f in files)})
    for item in files:
        if "loc" not in item:
            metrics["Non-Lean text lines"] += item.get("physical_lines", 0)
            metrics["Non-Lean nonblank lines"] += item.get("nonblank_lines", 0)
            continue
        loc = item["loc"]
        metrics["Lean files"] += 1
        metrics["Lean physical lines"] += loc["physical"]
        metrics["Lean nonblank lines"] += loc["nonblank"]
        metrics["Lean code lines"] += loc["code"]
        metrics["Lean comment lines"] += loc["comment"]
        metrics["Lean mixed lines"] += loc["mixed"]
        metrics["Verso document lines"] += loc["document"]
    metrics["All text physical lines"] = metrics["Lean physical lines"] + metrics["Non-Lean text lines"]
    metrics["All text nonblank lines"] = metrics["Lean nonblank lines"] + metrics["Non-Lean nonblank lines"]
    return metrics


def file_type(item):
    path = Path(item["path"])
    return path.suffix or (path.name if path.name.startswith(".") else "(none)")


def tooling(item):
    return item["path"].startswith(("scripts/", "comparison/", "blueprint/scripts/"))


def file_types(files):
    result = {}
    for item in files:
        count, size = result.get(file_type(item), (0, 0))
        result[file_type(item)] = (count + 1, size + item["bytes"])
    return result


def declaration_commands(files):
    result = Counter()
    for item in files:
        result.update(item.get("declaration_commands", {}))
    return result


def source_link(inventory, path, line, name):
    return f"[`{name}`]({REPO}/blob/{inventory['revision']}/vp-vnp/{quote(path)}#L{line})"


def proof_sizes(inventory):
    proofs = {key: item for key, item in inventory["proofs"].items()
              if item["module"] != "Comparator.VpVnp.Challenge"}
    ordered = sorted(proofs.values(), key=lambda p: (-p["body_code_lines"], p["name"], p["module"]))
    lengths = sorted(p["body_code_lines"] for p in proofs.values())
    return {
        "Named proof commands": len(lengths), "Total body code lines": sum(lengths),
        "Median": statistics.median(lengths), "90th percentile": lengths[ceil(.90 * len(lengths)) - 1],
        "99th percentile": lengths[ceil(.99 * len(lengths)) - 1], "Maximum": max(lengths),
        **{f"Bodies over {n} lines": sum(x > n for x in lengths) for n in (50, 100, 200)},
        "Identical normalized bodies (groups, ≥5 lines)": len(inventory["exact_normalized_proof_body_duplicates"]),
    }, ordered[:10]


def proof_example(inventory, paths, names):
    records = {item["name"]: item for item in inventory["proofs"].values()}
    links, lines = [], 0
    for name in names:
        item = records[name]
        links.append(source_link(inventory, paths[item["module"]], item["source_line"], name))
        lines += item["body_code_lines"]
    return ", ".join(links), f"{lines:,}"


def graph_metrics(imports, root):
    @cache
    def height(module):
        return max((1 + height(dep) for dep in imports[module] if dep in imports), default=0)

    reachable = {root}
    frontier = [root]
    for module in frontier:
        for dependency in imports[module]:
            if dependency in imports and dependency not in reachable:
                reachable.add(dependency)
                frontier.append(dependency)
    reverse = Counter(dep for module in reachable for dep in set(imports[module]) if dep in reachable)
    leaders = ", ".join(sorted(name for name in reverse if reverse[name] == max(reverse.values()))) if reverse else "—"
    return [len(reachable), sum(reverse.values()), height(root), max(reverse.values(), default=0), leaders]


def blueprint_metrics(inventory, role):
    records = inventory["blueprint"][role]
    counts = inventory["blueprint_counts"][role]
    return {"Document files": counts["files"],
            **({**{f"{k.capitalize()} lines": sum(r["loc"][k] for r in records)
                   for k in ("physical", "nonblank", "code", "comment", "document")},
                "Bytes": sum(r["bytes"] for r in records)} if role == "generated" else {}),
            "Unique associated names": counts["names"], "Node association occurrences": counts["association_occurrences"],
            "Listed name entries": counts["listed"], **{f"`{k}` directives": v for k, v in counts["directives"].items()}}


def exposition(inventory):
    roots = set(inventory["blueprint_declared_roots"])
    exported = set().union(*map(set, inventory["export_project_names"].values()))
    closure = set(inventory["blueprint_project_closure"])
    source_proofs = {p["name"] for p in inventory["proofs"].values()
                     if p["module"] != "Comparator.VpVnp.Challenge"}
    candidates = set(inventory["proof_candidates_outside_export_and_blueprint_closures"])
    return {"Authored blueprint roots": len(roots), "Authored blueprint project closure": len(closure),
            "Authored blueprint closure outside all export closures (compiled constants)": len(closure - exported),
            "Directly cited source theorems/lemmas outside all export closures": len((roots - exported) & source_proofs),
            "All source theorems/lemmas in the authored closure outside all export closures":
                len((closure - exported) & source_proofs),
            "Source theorems/lemmas outside both closures": len(candidates),
            "Outside both closures with no recorded proof-source usages":
                len(inventory["proof_candidates_with_no_source_usages"])}


def exposition_proofs(inventory, paths):
    exported = set().union(*map(set, inventory["export_project_names"].values()))
    cited = set(inventory["blueprint_declared_roots"]) - exported
    return {p["name"]: source_link(inventory, paths[p["module"]], p["source_line"], p["name"])
            for p in inventory["proofs"].values()
            if p["name"] in cited and p["module"] != "Comparator.VpVnp.Challenge"}


def benchmark_rows(source, revisions):
    main_stage = {"clean": "proof", "warm": "proof", "foundation": "edited", "branch": "edited", "chapter": "edited"}
    conditions = None
    archive = load(source) if source.is_file() else None
    for scenario, stage in main_stage.items():
        for side, revision in zip(("before", "after"), revisions, strict=True):
            stages = []
            for trial in range(1, 4):
                path = f"{side}/{scenario}-{trial}.jsonl"
                if archive is None:
                    with (source / path).open() as stream:
                        metadata, *records = map(json.loads, stream)
                else:
                    metadata, *records = archive[path]
                expected = (revision, scenario, trial)
                identity = (metadata["revision"], metadata["scenario"], metadata["trial"])
                if identity != expected or any(r.get("exit_code", 0) for r in records):
                    raise ValueError(f"invalid benchmark result: {path}")
                settings = tuple(metadata[k] for k in ("host", "logical_cpus", "lake_version", "manifest_sha256", "threads"))
                if conditions is not None and conditions != settings:
                    raise ValueError(f"benchmarked under different conditions: {path}")
                conditions = settings
                stages.append(next(r for r in records if r.get("stage") == stage))
            wall = [r["wall_seconds"] for r in stages]
            cpu = [r["cpu_user_seconds"] + r["cpu_system_seconds"] for r in stages]
            rss = [r["max_rss_bytes"] / 2**30 for r in stages]
            raw = ", ".join(f"{x:.3f}" for x in wall)
            wall_range = f"{min(wall):.3f}–{max(wall):.3f}"
            yield [scenario, side, raw, f"{statistics.median(wall):.3f} ({wall_range})",
                   f"{statistics.median(cpu):.3f}", f"{statistics.median(rss):.3f}",
                   ", ".join(str(len(r["built_modules"])) for r in stages)]



def module_benchmarks(archive):
    modules = ("Paper.Pieces", "Nc.Dl.Cut", "Nc.Flag.Act", "Nc.Tow.Slp2", "Nc.Tow.Slp3", "Nc.Tow.Slp4", "Paper.Cuts")
    for module in modules:
        for side in ("before", "after"):
            readings = []
            for trial in range(1, 4):
                proof = next(row for row in archive[f"{side}/clean-{trial}.jsonl"] if row.get("stage") == "proof")
                readings.append(proof.get("module_elapsed_seconds", {}).get(module))
            yield [f"`{module}`", side,
                   ", ".join(f"{reading:g}" if reading is not None else "—" for reading in readings),
                   f"{statistics.median(readings):g}" if all(reading is not None for reading in readings) else "—"]

def verification(archive, revisions):
    def stages(side, name, revision):
        metadata, *rows = archive[f"{side}/{name}.jsonl"]
        if metadata["revision"] != revision or any(r.get("exit_code", 0) for r in rows):
            raise ValueError(f"invalid {side} {name} result")
        return {r["stage"]: r for r in rows if "stage" in r}

    sides = ("before", "after")
    replays = [stages(side, "replay", rev) for side, rev in zip(sides, revisions, strict=True)]
    print("### Fresh replay of the five judged roots\n")
    print("Each checker's stage is an executed command. The counts are the checkers' reported declaration totals.\n")
    table(["Revision", "Export records", "Export bytes", "Export wall (s)", "con-leche accepted", "con-leche wall (s)",
           "con-ron accepted", "con-ron wall (s)"], [
        [side, f"{result['export_records']:,}", f"{result['export_bytes']:,}", f"{runs['five-root-export']['wall_seconds']:.3f}",
         *(value for name in ("con-leche", "con-ron") for value in (
            f"{result['checkers'][name]['accepted_declarations']:,}", f"{runs[name]['wall_seconds']:.3f}"))]
        for side, runs in zip(sides, replays, strict=True) for result in [runs["five-root-results"]]
    ])

    checked = [stages(side, "verify", rev) for side, rev in zip(sides, revisions, strict=True)]
    sites = [runs["site-artifacts"] for runs in checked]
    for stage, label in (("proof-build", "Proof build warning lines"),
                         ("blueprint-build-and-replay", "Blueprint build warning lines")):
        paired(label, *(runs[stage]["warnings"] for runs in checked))

    artifacts = {"site_files": "Site files", "site_bytes": "Site bytes", "html_pages": "HTML pages",
                 "olean_files": "Project `.olean` files after site build", "proved_verdicts": "Proved challenge verdicts",
                 "omitted_neighbourhood_drawings": "Omitted graph neighbourhood drawings"}
    paired("Rendered artifacts", *({**{label: site[key] for key, label in artifacts.items()},
           "HTML cache entries checked": site["blueprint_check"]["htmlCacheEntries"],
           "Manifest entries checked": site["blueprint_check"]["manifestEntries"],
           "Consistency errors": len(site["blueprint_check"]["errors"]),
           **{f"`{path}` bytes": info["bytes"] for path, info in site["artifacts"].items()}} for site in sites))
    print("### Rendered Project Stats\n")
    for group, label in (("rendered_size", "Size tile"), ("rendered_progress", "Coverage statement"),
                         ("replay_coverage_details", "Replay caption")):
        before, after = (site.get(group, {}) for site in sites)
        if before or after:
            table([label, "Before", "After"], [[key, before.get(key, "—"), after.get(key, "—")]
                                                for key in dict.fromkeys([*before, *after])])
    for side, site in zip(sides, sites, strict=True):
        messages = site.get("replay_messages", [])
        if messages:
            print(f"{side.capitalize()} site replay\n")
            for message in messages:
                print(f"- {message}")
            print()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("before", "after"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    parser.add_argument("--timings", type=Path)
    parser.add_argument("--verification", type=Path, help="archive from capture-results.py with both verification runs")
    args = parser.parse_args()
    before, after = load(args.before), load(args.after)
    inventories = [before, after]
    print("# Comparison data\n")
    print(f"Before `{before['revision']}`  \nAfter `{after['revision']}`\n")
    scopes = [
        ("All tracked project files", lambda f: True),
        ("Proof libraries", lambda f: f["library"] in PROOF_LIBRARIES),
        ("Public statement", lambda f: f["library"] == "Statement"),
        ("Comparator", lambda f: f["library"] == "Comparator"),
        ("Authored blueprint", lambda f: f["library"] == "Blueprint" and not tooling(f)),
        ("Tooling and measurement inputs", tooling),
        ("Project metadata and static assets", lambda f: f["library"] == "Support" and not tooling(f)),
    ]
    for title, include in scopes:
        paired(title, *(scope([f for f in inv["project_files"] if include(f)]) for inv in inventories))
    for label, key in [("Repository", "tracked_files"), ("Project", "project_files")]:
        print(f"### {label} tracked file types\n")
        old, new = (file_types(inv[key]) for inv in inventories)
        order = sorted(old.keys() | new.keys(), key=lambda k: (-max(old.get(k, (0,))[0], new.get(k, (0,))[0]), k))
        table(["Suffix", "Files before", "Files after", "Bytes before", "Bytes after"],
              ([kind, f"{a[0]:,}", f"{b[0]:,}", f"{a[1]:,}", f"{b[1]:,}"]
               for kind in order for a, b in [(old.get(kind, (0, 0)), new.get(kind, (0, 0)))]))
    paired("Whole repository tree totals", *({"Paths": len(inv["tracked_files"]),
            "Bytes": sum(f["bytes"] for f in inv["tracked_files"])} for inv in inventories))
    print("### Proof libraries by subsystem\n")
    groups = sorted({name for inv in inventories for name in inv["groups"] if name.split("/")[0] in PROOF_LIBRARIES})
    table(["Scope", "Files before", "Files after", "Physical before", "Physical after", "Code before", "Code after",
           "Proofs before", "Proofs after"],
          ([name, *(f"{inv['groups'].get(name, {}).get(k, 0):,}" for k in ("files", "lean_physical", "lean_code", "proofs")
                    for inv in inventories)] for name in groups))
    paired("Declaration commands in the proof, statement and Comparator", *(
        declaration_commands(inv["project_files"]) for inv in inventories))
    (old, longest_old), (new, longest_new) = map(proof_sizes, inventories)
    paired("Named theorem and lemma bodies", old, new)
    paths = [{f.get("module"): f["path"] for f in inv["project_files"]} for inv in inventories]
    print("### Ten longest proof bodies\n")
    table(["Rank", "Before", "Lines", "After", "Lines"], [
        [n, *(item for k, p in enumerate((p0, p1)) for item in (
            source_link(inventories[k], paths[k][p["module"]], p["source_line"], p["name"]), p["body_code_lines"]))]
        for n, (p0, p1) in enumerate(zip(longest_old, longest_new, strict=True), start=1)
    ])
    if before["revision"] != after["revision"]:
        print("### Selected proof rewrites\n")
        print("Line counts cover the displayed bodies. Shared dependencies are measured in the kernel closure tables.\n")
        table(["Argument", "Before", "Body lines", "After", "Body lines"], [
            [title, *proof_example(before, paths[0], old_names), *proof_example(after, paths[1], new_names)]
            for title, old_names, new_names in EXAMPLES
        ])
    print("### Local import DAG\n")
    table(["Root", "Revision", "Reachable modules", "Edges", "Longest path", "Max reverse fanout", "Most imported"], [
        [f"`{root}`", side, *graph_metrics(inv["imports"], root)]
        for root in before["import_counts"] for side, inv in zip(("Before", "After"), inventories, strict=True)
    ])
    print("### Kernel dependency closures\n")
    print("Every closure includes its export. Project counts include compiler-generated constants.\n")
    keys = ("constants", "project_constants", "modules", "project_modules", "edges", "maxShortestDepth", "maxFanout")
    table(["Export", "Revision", "Constants", "Project constants", "Modules", "Project modules", "Edges",
           "Max shortest depth", "Max fanout"], [
        [f"{label} `{name}`", side, *(f"{inv['kernel_counts']['Solution.' + name][k]:,}" for k in keys)]
        for label, name in EXPORTS.items() for side, inv in zip(("Before", "After"), inventories, strict=True)
    ])
    paired("Union of the five exports", *({k.replace("_", " ").capitalize(): v
           for k, v in inv["export_union"].items()} for inv in inventories))
    paired("Compiled project proof files", *({f"`{kind}` {key}": value
           for kind, metrics in inv["compiled_proof_artifacts"].items() for key, value in metrics.items()}
           for inv in inventories))
    for role in ("authored", "generated"):
        paired(f"{role.capitalize()} blueprint directives", *(blueprint_metrics(inv, role) for inv in inventories))
    paired("Exposition and source proofs outside the exports", *map(exposition, inventories))
    print("### Named exposition proofs outside all five exports\n")
    print("Each row is a written Lean theorem or lemma command resolved from authored blueprint text. The export test uses the compiled closures.\n")
    old_exposition, new_exposition = (exposition_proofs(inv, path) for inv, path in zip(inventories, paths, strict=True))
    table(["Before", "After"], [[old_exposition.get(name, "—"), new_exposition.get(name, "—")]
                                 for name in sorted(old_exposition.keys() | new_exposition.keys())])
    if args.timings:
        print("### Local build benchmark\n")
        table(["Scenario", "Revision", "Wall trials (s)", "Wall median (range), s", "CPU median (s)",
               "OS peak RSS median (GiB)", "Project modules rebuilt per trial"],
              benchmark_rows(args.timings, [inv["revision"] for inv in inventories]))
        if args.timings.is_file():
            print("### Selected module job timings from the clean builds\n")
            print("The values are Lake’s reported elapsed job times, with its rounding and shared CPU load. "
                  "The whole-build timings above measure elapsed time for the project.\n")
            table(["Module", "Revision", "Lake elapsed trials (s)", "Median (s)"],
                  module_benchmarks(load(args.timings)))
    if args.verification:
        verification(load(args.verification), [inv["revision"] for inv in inventories])


if __name__ == "__main__":
    main()

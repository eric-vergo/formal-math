#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Eric Vergo, GPT-6.2 (OpenAI)
"""Produce the vp-vnp source and compiled-artifact inventory as JSON."""

import argparse
from collections import Counter, defaultdict
import gzip
import hashlib
import json
from pathlib import Path
import re
import statistics
import subprocess


LIBRARIES = {"Nc", "NS1", "Ov", "Paper", "Statement", "Comparator"}
ROOT = Path(__file__).resolve().parents[2]
PROOF = re.compile(r"\b(theorem|lemma|example)\s+([^\s{(:]+)?")
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([^\s]+)", re.M)
DECL_COMMAND = re.compile(
    r"^ *(?:@\[[^\n]*\] *)?(?:(?:private|protected|public|noncomputable|unsafe|partial|"
    r"local|scoped|nonrec) +)*(def|abbrev|opaque|structure|class|inductive|instance|"
    r"theorem|lemma|example|axiom)\b",
    re.M,
)
NODE = re.compile(r'^:{3,}\s*(definition|lemma_|theorem|corollary|proposition|proof|group|table)\b([^\n]*)', re.M)
ASSOCIATION = re.compile(r'lean := "([^"]*)"')
LISTED = re.compile(r'^\* `([^`]+)` \(\{repoFile "([^"]+)"\}\[source\]\)', re.M)
BUCKETS = ((1, "1"), (4, "2–4"), (9, "5–9"), (19, "10–19"), (49, "20–49"),
           (99, "50–99"), (199, "100–199"), (499, "200–499"))


def git(*args):
    return subprocess.check_output(["git", "-C", ROOT, *args])


def tracked(revision):
    revision = git("rev-parse", "--verify", revision).decode().strip()
    entries = []
    for row in git("ls-tree", "-rlz", revision).split(b"\0"):
        if not row:
            continue
        fields, path = row.split(b"\t", 1)
        mode, kind, oid, size = fields.decode().split()
        entries.append((path.decode(), mode, kind, oid, int(size)))
    return revision, entries


def category(path):
    if path == "BlueprintMain.lean" or path.startswith("blueprint/"):
        if path.startswith("blueprint/VpVnpBlueprint/Generated/"):
            return "Blueprint", "Blueprint/Generated"
        return "Blueprint", "Blueprint/Authored"
    parts = Path(path).with_suffix("").parts
    first = parts[0]
    if first in LIBRARIES:
        sub = "/".join(parts[:2]) if len(parts) >= 3 else first
        return first, sub
    return "Support", "Support"


def module_name(path):
    p = Path(path)
    if p.parts[0] == "blueprint":
        p = p.relative_to("blueprint")
    return ".".join(p.with_suffix("").parts)


def split_lean(text):
    """Preserve offsets while masking Lean block and line comments."""
    masked = list(text)
    is_comment = [False] * len(text)
    i = depth = 0
    in_string = in_line = False
    while i < len(text):
        pair = text[i:i + 2]
        ch = text[i]
        if in_line:
            if ch == "\n":
                in_line = False
                i += 1
                continue
        elif in_string:
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        elif depth:
            if pair == "/-":
                depth += 1
            elif pair == "-/":
                depth -= 1
            if pair in {"/-", "-/"}:
                masked[i:i + 2] = "  "
                is_comment[i:i + 2] = [True, True]
                i += 2
                continue
        elif pair == "/-":
            depth = 1
            masked[i:i + 2] = "  "
            is_comment[i:i + 2] = [True, True]
            i += 2
            continue
        elif pair == "--":
            in_line = True
        elif ch == "'":
            char_literal = re.match(r"'(?:\\.|[^'\n])'", text[i:i + 8])
            if char_literal:
                i += len(char_literal[0])
                continue
        elif ch == '"':
            in_string = True
            i += 1
            continue
        else:
            i += 1
            continue
        if ch != "\n":
            masked[i] = " "
            is_comment[i] = True
        i += 1
    return "".join(masked), is_comment


def line_stats(text, masked, comments):
    counts = Counter(physical=0, code=0, comment=0, mixed=0, blank=0)
    start = 0
    for line in text.splitlines(keepends=True):
        end = start + len(line)
        has_code = bool(masked[start:end].strip())
        has_comment = any(comments[start:end])
        counts["physical"] += 1
        counts["code"] += has_code
        counts["comment"] += has_comment
        counts["mixed"] += has_code and has_comment
        counts["blank"] += not (has_code or has_comment)
        start = end
    assert counts["physical"] == counts["code"] + counts["comment"] - counts["mixed"] + counts["blank"]
    return counts


def lean_stats(text, document_start):
    code = text[:document_start]
    masked, comments = split_lean(code)
    loc = line_stats(code, masked, comments)
    loc["document"] = len(text[document_start:].splitlines())
    loc["physical"] += loc["document"]
    loc["nonblank"] = sum(bool(line.strip()) for line in text.splitlines())
    return loc, masked


def separator(source):
    """Find a declaration value delimiter at bracket depth zero."""
    stack = []
    for m in re.finditer(r'"(?:\\.|[^"\\])*"|:=|\bwhere\b|[(){}\[\]⟨⟩]', source):
        token = m[0]
        if token in "({[⟨":
            stack.append(token)
        elif token in ")}]⟩":
            if stack:
                stack.pop()
        elif not stack and token in {":=", "where"}:
            return m.end(), token
    equation = re.search(r"(?m)^\s*\|", source)
    if equation:
        return equation.start(), "equations"
    return None, None


def column_index(line, utf16_column):
    return len(line.encode("utf-16-le")[:2 * utf16_column].decode("utf-16-le"))


def proof_ranges(text, masked_file, ilean, file):
    lines = text.split("\n")
    out = []
    seen = set()
    spans = dict(ilean["decls"])
    lexical_proofs = {masked_file.count("\n", 0, command.start()): command
                      for command in DECL_COMMAND.finditer(masked_file)
                      if command[1] in {"theorem", "lemma"}}
    covered = {span[4] for span in spans.values() if len(span) == 8}
    for key, item in ilean["references"].items():
        reference = json.loads(key).get("c")
        selection = item.get("definition")
        if not reference or reference["m"] != ilean["module"] or selection is None:
            continue
        line = selection[0]
        if line not in lexical_proofs or line in covered or reference["n"] in spans:
            continue
        # Lean's definition identifier may be present even when it omits the command range.
        # The fallback is limited to an inline declaration and refuses continuation lines.
        next_line = lines[line + 1] if line + 1 < len(lines) else ""
        if (not separator(lines[line])[0] or (next_line.strip() and next_line.startswith(" "))):
            continue
        end = len(lines[line].encode("utf-16-le")) // 2
        spans[reference["n"]] = [line, 0, line, end, *selection[:4]]
        covered.add(line)
    for name, span in spans.items():
        if len(span) != 8:
            continue
        start, first_col, end, end_col, name_line, name_col, _, _ = span
        start, end, name_line = start + 1, end + 1, name_line + 1
        first_col = column_index(lines[start - 1], first_col)
        end_col = column_index(lines[end - 1], end_col)
        name_col = column_index(lines[name_line - 1], name_col)
        if (name_line, name_col) in seen or name_line < 1 or name_line > len(lines):
            continue
        before = lines[name_line - 1][:name_col]
        prefix = re.search(r"\b(theorem|lemma)\s+$", before)
        if not prefix:
            continue
        # Compiler ranges give exact command boundaries and canonical names.
        parts = lines[start - 1:end]
        parts[-1] = parts[-1][:end_col]
        parts[0] = parts[0][first_col:]
        seen.add((name_line, name_col))
        src = "\n".join(parts)
        masked, _ = split_lean(src)
        keyword = PROOF.search(masked)
        if keyword is None:
            raise ValueError(f"missing theorem keyword: {file}:{name_line} {name}")
        proof = masked[keyword.end():]
        idx, token = separator(proof)
        if idx is None:
            raise ValueError(f"missing proof separator: {file}:{name_line} {name}")
        offset = keyword.end() + idx
        body = masked[offset:]
        out.append({
            "name": name, "source_line": name_line, "body_starts_on": start + masked.count("\n", 0, offset),
            "body_ends_on": end, "body_code_lines": sum(bool(line.strip()) for line in body.splitlines()),
            "style": "tactic" if re.match(r"\s*by\b", body) else "term" if token == ":=" else token,
            "sha256": hashlib.sha256(" ".join(body.split()).encode()).hexdigest(),
        })
    missing = set(lexical_proofs) - {entry["source_line"] - 1 for entry in out}
    if missing:
        raise ValueError(f"{file} has theorem or lemma commands without usable ranges: "
                         f"{[line + 1 for line in sorted(missing)]}")
    return sorted(out, key=lambda p: (p["source_line"], p["name"]))


def read_blueprint(path, text):
    nodes = []
    for match in NODE.finditer(text):
        kind, header = match.groups()
        names = [name.strip() for association in ASSOCIATION.findall(header)
                 for name in association.split(",") if name.strip()]
        nodes.append({"kind": kind, "header": header.strip(),
                      "line": text.count("\n", 0, match.start()) + 1, "lean": names})
    return {
        "path": path, "directives": nodes,
        "listed": [{"name": n, "source": p} for n, p in LISTED.findall(text)],
        "associated_names": sorted({name.strip() for assoc in ASSOCIATION.findall(text)
                                    for name in assoc.split(",") if name.strip()}),
    }


def reachable(graph, root):
    seen = set()
    pending = [root]
    while pending:
        current = pending.pop()
        if current in seen or current not in graph:
            continue
        seen.add(current)
        pending.extend(graph[current])
    return sorted(seen)


def graph_stats(graph, root):
    distances = {root: 0}
    queue = [root]
    for current in queue:
        for dep in graph.get(current, ()):
            if dep in graph and dep not in distances:
                distances[dep] = distances[current] + 1
                queue.append(dep)
    fanout = [len(set(graph.get(m, ())) & distances.keys()) for m in queue]
    return {"modules": len(queue), "local_edges": sum(fanout),
            "max_local_fanout": max(fanout), "median_local_fanout": statistics.median(fanout),
            "max_shortest_local_depth": max(distances.values())}


def analyze(args):
    revision, blobs = tracked(args.revision)
    kernel = json.loads(args.kernel.read_text())
    grouped = defaultdict(Counter)
    proof_lengths = defaultdict(list)
    proofs = {}
    files = []
    local_graph = {}
    blueprint = {"authored": [], "generated": []}
    modules = set(kernel["localDeclarations"])
    export_membership = {name for closure in kernel["exports"].values() for name, _ in closure}
    locally_used = set()
    proof_duplicates = defaultdict(list)
    source_modules = {}
    for relative, mode, kind, oid, size in blobs:
        if not relative.startswith("vp-vnp/"):
            continue
        path = relative.removeprefix("vp-vnp/")
        data = (args.source / path).read_bytes()
        digest = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        if oid != digest:
            raise ValueError(f"{relative} does not match {revision}: {oid} vs {digest}")
        lib, subsystem = category(path)
        entry = {"path": path, "bytes": size, "library": lib, "subsystem": subsystem}
        source = Path(path)
        if source.suffix == ".lean":
            text = data.decode()
            # Verso prose following #doc is accounted separately from Lean code.
            command_end = re.search(r"^#doc\b", text, re.M) if lib == "Blueprint" else None
            loc, masked = lean_stats(text, command_end.start() if command_end else len(text))
            entry["loc"] = loc
            mod = module_name(path)
            entry["module"] = mod
            local_graph[mod] = IMPORT.findall(masked)
            source_modules[mod] = path
            if mod in modules or mod == "Comparator.VpVnp.Challenge":
                ilean_file = args.compiled / source.with_suffix(".ilean")
                ilean = json.loads(ilean_file.read_text())
                if ilean["module"] != mod:
                    raise ValueError(f"wrong compiled artifacts for {mod}")
                local_graph[mod] = [entry[0] for entry in ilean["directImports"]]
                entry["declaration_commands"] = Counter(DECL_COMMAND.findall(masked))
                for group in {"total", lib, subsystem}:
                    grouped[group].update({f"declarations:{kind}": count
                                           for kind, count in entry["declaration_commands"].items()})
                for key, item in ilean["references"].items():
                    reference = json.loads(key).get("c")
                    if reference and item.get("usages"):
                        locally_used.add((reference["m"], reference["n"]))
                for p in proof_ranges(text, masked, ilean, path):
                    key = f"{mod}:{p['name']}"
                    length = p["body_code_lines"]
                    p["module"] = mod
                    p["bucket"] = "0" if length == 0 else next(
                        (label for bound, label in BUCKETS if length <= bound), "500+")
                    proofs[key] = p
                    if length >= 5 and lib != "Comparator":
                        proof_duplicates[p["sha256"]].append(key)
                    for group in {"total", lib, subsystem}:
                        grouped[group]["proof:" + p["bucket"]] += 1
                        grouped[group]["proof_body_code_lines"] += length
                        proof_lengths[group].append(length)
            if path.startswith("blueprint/"):
                item = read_blueprint(path, text)
                if command_end and path.startswith("blueprint/VpVnpBlueprint"):
                    blueprint["authored"].append(item)
        elif b"\0" not in data:
            lines = data.decode().splitlines()
            entry["physical_lines"] = len(lines)
            entry["nonblank_lines"] = sum(bool(line.strip()) for line in lines)
        files.append(entry)
        for group in {"total", lib, subsystem}:
            grouped[group]["files"] += 1
            grouped[group]["bytes"] += size
            for metric, value in entry.get("loc", {}).items():
                grouped[group]["lean_" + metric] += value

    for p in sorted(args.generated.rglob("*.lean")):
        path = str(p.relative_to(args.generated))
        text = p.read_text()
        item = read_blueprint(path, text)
        item["bytes"] = p.stat().st_size
        document = re.search(r"^#doc\b", text, re.M)
        loc, masked = lean_stats(text, document.start() if document else len(text))
        item["physical_lines"] = loc["physical"]
        item["loc"] = loc
        mod = "VpVnpBlueprint.Generated." + ".".join(Path(path).with_suffix("").parts)
        local_graph[mod] = IMPORT.findall(masked)
        blueprint["generated"].append(item)

    blueprint_counts = {}
    for role, records in blueprint.items():
        blueprint_counts[role] = {
            "files": len(records),
            "directives": Counter(d["kind"] for item in records for d in item["directives"]),
            "names": len({n for item in records for n in item["associated_names"]}),
            "association_occurrences": sum(len(d["lean"]) for item in records for d in item["directives"]),
            "listed": sum(len(item["listed"]) for item in records),
        }
    export_counts = {}
    for root, items in kernel["exports"].items():
        local = [(n, m) for n, m in items if m in modules]
        export_counts[root] = {
            "constants": len(items), "project_constants": len(local),
            "modules": len({m for _, m in items}),
            "project_modules": len({m for _, m in local}),
            **kernel.get("graphMetrics", {}).get(root, {}),
            "project_constants_by_library": Counter(category(source_modules[m])[0] for _, m in local),
        }
    unused = {
        key: p for key, p in proofs.items()
        if p["name"] not in export_membership
        and (p["module"], p["name"]) not in locally_used
        and p["module"] != "Comparator.VpVnp.Challenge"
    }
    for group, lengths in proof_lengths.items():
        grouped[group]["proofs"] = len(lengths)
        grouped[group]["median_proof_body_lines"] = statistics.median(lengths)
        grouped[group]["longest_proof_body_lines"] = max(lengths)
    export_project_names = {
        root: sorted(n for n, m in closure if m in modules)
        for root, closure in kernel["exports"].items()
    }
    union = {tuple(item) for items in kernel["exports"].values() for item in items}
    export_union = {
        "constants": len(union), "project_constants": sum(m in modules for _, m in union),
        "modules": len({m for _, m in union}), "project_modules": len({m for _, m in union if m in modules}),
    }
    blueprint_membership = set(kernel["blueprintProjectClosure"])
    import_roots = ["Comparator.VpVnp.Solution", "Paper", "BlueprintMain", "VpVnpBlueprint"]
    inactive = sorted(
        k for k, p in proofs.items() if p["module"] != "Comparator.VpVnp.Challenge"
        and p["name"] not in export_membership and p["name"] not in blueprint_membership
    )
    return {
        "revision": revision,
        "tracked_files": [{"path": p, "mode": m, "kind": k, "git_oid": o, "bytes": b}
                          for p, m, k, o, b in blobs],
        "project_files": files, "groups": dict(grouped), "proofs": proofs,
        "imports": local_graph,
        "import_reachability": {r: reachable(local_graph, r) for r in import_roots},
        "import_counts": {r: graph_stats(local_graph, r) for r in import_roots if r in local_graph},
        "blueprint": blueprint, "blueprint_counts": blueprint_counts,
        "kernel_counts": export_counts, "export_project_names": export_project_names, "export_union": export_union,
        "blueprint_declared_roots": kernel["blueprintDeclaredRoots"],
        "blueprint_project_closure": kernel["blueprintProjectClosure"],
        "proof_candidates_outside_export_and_blueprint_closures": inactive,
        "proof_candidates_with_no_source_usages": sorted(set(inactive) & unused.keys()),
        "proof_candidates_unreferenced_by_project_or_exports": sorted(unused),
        "exact_normalized_proof_body_duplicates": [v for v in proof_duplicates.values() if len(v) > 1],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--source", type=Path, required=True, help="vp-vnp source matching revision")
    parser.add_argument("--compiled", type=Path, required=True, help="directory of matching .ileans")
    parser.add_argument("--generated", type=Path, required=True, help="actual generated blueprint directory")
    parser.add_argument("--kernel", type=Path, required=True, help="output from InventoryKernel.lean")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--summary", type=Path, help="optional compact summary for reviewing differences")
    args = parser.parse_args()
    if not args.generated.is_dir():
        parser.error("the generated blueprint directory does not exist")
    result = analyze(args)
    raw = (json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode()
    if args.output.suffix == ".gz":
        args.output.write_bytes(gzip.compress(raw, mtime=0))
    else:
        args.output.write_bytes(raw)
    if args.summary:
        wanted = ["revision", "groups", "import_counts", "blueprint_counts", "kernel_counts", "export_union",
                  "proof_candidates_with_no_source_usages", "exact_normalized_proof_body_duplicates"]
        summary = {k: result[k] for k in wanted}
        summary["tracked_files"] = len(result["tracked_files"])
        args.summary.write_text(json.dumps(summary, indent=2, ensure_ascii=False, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()

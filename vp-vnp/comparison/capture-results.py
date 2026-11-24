#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Eric Vergo, GPT-6.2 (OpenAI)
"""Archive benchmark records with verifiable log hashes and rendered site coverage."""

import argparse
import gzip
import json
from pathlib import Path
import re

from benchmark import digest, omitted_drawings, rendered_stats, warning_counts


def record_file(path):
    records = [json.loads(line) for line in path.read_text().splitlines()]
    if not records or records[0].get("format_version") != 1:
        raise ValueError(f"unrecognized results format: {path}")
    for row in records:
        if "log" not in row:
            continue
        log = path.parent / row["log"]
        sha = digest(log)
        if row.get("log_sha256", sha) != sha:
            raise ValueError(f"log digest mismatch: {log}")
        row["log_sha256"] = sha
        clean_proof = records[0]["scenario"] == "clean" and row["stage"] == "proof"
        if clean_proof or "warnings" not in row:
            log_text = log.read_text(errors="replace")
        if "warnings" not in row:
            row["warnings"] = warning_counts(log_text)
        if clean_proof:
            module_names = set(row["built_modules"])
            row["module_elapsed_seconds"] = {
                name: float(seconds) for name, seconds in re.findall(
                    r"\[\d+/\d+\] Built (\S+) \(([\d.]+)s\)", log_text) if name in module_names
            }
    return records


def baseline_site_record(site, expected, replay_log):
    for relative, recorded in expected["artifacts"].items():
        path = site / relative
        if not path.is_file() or path.stat().st_size != recorded["bytes"] or digest(path) != recorded["sha256"]:
            raise ValueError(f"rendered baseline artefact differs from verification: {path}")
    files = [path for path in site.rglob("*") if path.is_file()]
    if len(files) != expected["site_files"] or sum(path.stat().st_size for path in files) != expected["site_bytes"]:
        raise ValueError(f"rendered baseline site totals differ from verification: {site}")
    return {
        **rendered_stats((site / "Project-Stats/index.html").read_text()),
        "html_pages": sum(path.suffix == ".html" for path in files),
        "replay_messages": re.findall(r"^Kernel replay: (.+)$", replay_log, re.M),
        "omitted_neighbourhood_drawings": omitted_drawings(replay_log),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runs", required=True, type=Path,
                        help="directory with before and after children containing official JSONL files")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--baseline-verification", type=Path,
                        help="completed baseline verify.jsonl if stored outside the official trial directory")
    parser.add_argument("--baseline-site", type=Path,
                        help="baseline html-multi root, for additional baseline Stats fields")
    args = parser.parse_args()
    result = {}
    for side in ("before", "after"):
        for path in sorted((args.runs / side).glob("*.jsonl")):
            result[f"{side}/{path.name}"] = record_file(path)
    if args.baseline_verification:
        if "before/verify.jsonl" in result:
            raise ValueError("two different baseline verification inputs")
        records = record_file(args.baseline_verification)
        if args.baseline_site:
            site = args.baseline_site
            artifacts = next(row for row in records if row.get("stage") == "site-artifacts")
            replay = next(row for row in records if row.get("stage") == "blueprint-build-and-replay")
            site_log = (args.baseline_verification.parent / replay["log"]).read_text(errors="replace")
            artifacts.update(baseline_site_record(site, artifacts, site_log))
        result["before/verify.jsonl"] = records
    if not result:
        raise ValueError("no benchmark records collected")
    raw = (json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n").encode()
    with args.output.open("xb") as stream:
        stream.write(gzip.compress(raw, mtime=0))


if __name__ == "__main__":
    main()

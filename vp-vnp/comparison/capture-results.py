#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Eric Vergo, GPT-6.2 (OpenAI)
"""Archive benchmark records with verifiable log hashes and rendered site coverage."""

import argparse
import gzip
import json
from pathlib import Path
import re

from benchmark import digest, rendered_stats, warning_counts


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
        if "warnings" not in row:
            row["warnings"] = warning_counts(log.read_text(errors="replace"))
    return records


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
            artifacts.update(rendered_stats((site / "Project-Stats/index.html").read_text()))
            artifacts["html_pages"] = sum(p.is_file() for p in site.rglob("*.html"))
            artifacts["replay_messages"] = re.findall(r"^Kernel replay: (.+)$", site_log, re.M)
        result["before/verify.jsonl"] = records
    if not result:
        raise ValueError("no benchmark records collected")
    raw = (json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n").encode()
    with args.output.open("xb") as stream:
        stream.write(gzip.compress(raw, mtime=0))


if __name__ == "__main__":
    main()

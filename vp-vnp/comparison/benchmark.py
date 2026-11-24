#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Eric Vergo, GPT-6.2 (OpenAI)
"""Measure vp-vnp builds in a disposable project copy with provisioned dependencies."""

import argparse
from collections import Counter
from contextlib import nullcontext
import datetime
import hashlib
import html
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile
import time


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True,
                        help="disposable vp-vnp directory; project build outputs are deleted")
    parser.add_argument("--revision", required=True, help="source revision recorded in the results")
    parser.add_argument("--output", type=Path, required=True, help="new JSON Lines result file")
    parser.add_argument("--scenario", choices=("clean", "warm", "foundation", "branch", "chapter", "verify", "replay"), required=True)
    parser.add_argument("--trial", type=int, default=1)
    parser.add_argument("--threads", type=int, default=4)
    return parser.parse_args()


def append_json(output, record):
    with output.open("a") as file:
        file.write(json.dumps(record, sort_keys=True) + "\n")


def warning_counts(output):
    warnings = Counter()
    for line in output.splitlines():
        if not line.startswith("warning: "):
            continue
        path = line.removeprefix("warning: ").split(":", 1)[0]
        project = path.split("/", 1)[0] in {"Nc", "NS1", "Ov", "Paper", "Comparator", "blueprint", "scripts"}
        project |= path in {"Paper.lean", "Statement.lean", "BlueprintMain.lean"}
        if "declaration uses `sorry`" in line:
            category = "challenge sorry" if path == "Comparator/VpVnp/Challenge.lean" else "other sorry"
        elif "designed for use with the module system" in line:
            category = "module-system import"
        elif "deprecated" in line.lower():
            category = "deprecation"
        elif any(marker in line.lower() for marker in ("unused", "linter", "not explicitly referenced")):
            category = "linter/unused"
        elif "docstring" in line.lower():
            category = "docstring"
        elif "exponentiation.threshold" in line:
            category = "exponentiation threshold"
        else:
            category = "other"
        warnings[f"{'project' if project else 'dependency or unscoped'}: {category}"] += 1
    return dict(warnings)


def measure(args, scenario, trial, name, command, *, environment=None, stdout=None):
    log = args.logs / f"{scenario}-{trial}-{name}.log"
    print(f"{scenario} {trial} {name}", flush=True)
    started = time.perf_counter()
    with log.open("wb") as file, (stdout.open("wb") if stdout else nullcontext(file)) as stream:
        run = subprocess.Popen(command, cwd=args.work, stdout=stream, stderr=file,
                               env={**os.environ, **(environment or {})})
        _, status, usage = os.wait4(run.pid, 0)
        run.returncode = os.waitstatus_to_exitcode(status)
    elapsed = time.perf_counter() - started
    output = log.read_text(errors="replace")
    built = re.findall(r"\[\d+/\d+\] Built ([^\s(]+)", output)
    libraries = {"Statement", "Paper", "NS1", "Nc", "Ov", "Comparator", "VpVnpBlueprint", "BlueprintMain"}
    modules = sorted({module for module in built if ":" not in module and module.split(".")[0] in libraries})
    append_json(args.output, {
        "scenario": scenario,
        "trial": trial,
        "stage": name,
        "command": command,
        "environment_overrides": environment or {},
        "cpu_user_seconds": usage.ru_utime,
        "cpu_system_seconds": usage.ru_stime,
        "max_rss_bytes": usage.ru_maxrss * (1 if platform.system() == "Darwin" else 1024),
        "built_modules": modules,
        "lake_built_jobs": len(built),
        "exit_code": run.returncode,
        "wall_seconds": round(elapsed, 6),
        "log": log.relative_to(args.output.parent).as_posix(),
        "log_sha256": digest(log),
        "warnings": warning_counts(output),
    })
    if run.returncode:
        raise SystemExit(f"{name} failed ({run.returncode}). See {log}")
    return log


def proof_builds(args):
    lake = ["lake", "--no-cache", "--no-ansi", "build"]
    def stage(label, command):
        return measure(args, args.scenario, args.trial, label, command)

    if args.scenario == "clean":
        build = args.work / ".lake/build"
        if build.exists():
            shutil.rmtree(build)
        stage("proof", lake)
    elif args.scenario == "warm":
        stage("proof", lake)
    else:
        edits = {
            "foundation": "Paper/Identity.lean",
            "branch": "Paper/Approximate.lean",
            "chapter": "blueprint/VpVnpBlueprint/Chapters/Assembly.lean",
        }
        relative = edits[args.scenario]
        source = args.work / relative
        original = source.read_bytes()
        edit = b"\n-- Representative incremental benchmark edit.\n"
        append_json(args.output, {"source": relative, "original_sha256": hashlib.sha256(original).hexdigest(),
                                  "appended": edit.decode()})
        command = [*lake, "VpVnpBlueprint.Chapters.Assembly"] if args.scenario == "chapter" else lake
        stage("prime", command)
        try:
            source.write_bytes(original + edit)
            stage("edited", command)
        finally:
            source.write_bytes(original)
        stage("restore", command)


def digest(path):
    with path.open("rb") as file:
        return hashlib.file_digest(file, "sha256").hexdigest()


def replay_exports(args):
    """Run the two shipped checkers directly on an export of the five judged roots."""
    config = json.loads((args.work / "Comparator/VpVnp/comparator.json").read_text())
    roots = config["theorem_names"]
    if len(set(roots)) != 5 or config["solution_module"] != "Comparator.VpVnp.Solution":
        raise SystemExit("Expected the five roots of Comparator.VpVnp.Solution")
    lean = ["lake", "env"]
    sysroot = Path(subprocess.check_output([*lean, "lean", "--print-prefix"], cwd=args.work, text=True).strip())
    programs = {}
    for name in ("con-leche", "con-ron"):
        variable = "VERSO_BLUEPRINT_" + name.upper().replace("-", "_")
        program = Path(os.environ.get(variable) or sysroot / "bin" / name).resolve()
        if not program.is_file() or not os.access(program, os.X_OK):
            raise SystemExit(f"Cannot run {program}; provision the pinned Lean toolchain's {name}")
        programs[name] = program
    with tempfile.TemporaryDirectory(prefix="five-root-export-", dir=args.work / ".lake") as temp:
        export = Path(temp) / "export.jsonl"
        measure(args, args.scenario, args.trial, "five-root-export",
                [*lean, "leanexport", config["solution_module"], "--", *roots], stdout=export)
        prefixes = (b'{"def":', b'{"thm":', b'{"opaque":', b'{"axiom":', b'{"inductive":')
        records = 0
        last = b""
        with export.open("rb") as stream:
            for last in stream:
                records += last.startswith(prefixes)
        if not records or not last.endswith(b"\n"):
            raise SystemExit("The five-root export is empty or truncated")
        checked = {}
        for name, program in programs.items():
            log = measure(args, args.scenario, args.trial, name,
                          [str(program), "--verified", f"--jobs={args.threads}", str(export)])
            count = re.search(r": accepted ([0-9]+) declarations?\b", log.read_text(errors="replace"))
            if count is None or int(count[1]) < records:
                raise SystemExit(f"{name} did not report accepting the complete export; see {log}")
            checked[name] = {"program_sha256": digest(program), "accepted_declarations": int(count[1])}
        append_json(args.output, {"scenario": args.scenario, "trial": args.trial, "stage": "five-root-results",
                                  "roots": roots, "export_records": records, "export_bytes": export.stat().st_size,
                                  "export_sha256": digest(export), "checkers": checked})


def rendered_stats(stats):
    def text(markup):
        return " ".join(html.unescape(re.sub(r"<[^>]+>", "", markup)).split())

    progress = re.findall(r'data-bp-progress="([^"]+)"[^>]*>(.*?)</p>', stats, re.S)
    details = re.findall(r'<details class="bp_stats_more bp_stats_replay_(\w+)"[^>]*>\s*<summary>(.*?)</summary>',
                         stats, re.S)
    size = re.findall(r'data-bp-stat="([^"]+)"[^>]*>\s*<span class="bp_stats_tile_value">(.*?)</span>',
                      stats, re.S)
    return {
        "proved_verdicts": len(re.findall(r'class="[^"]*bp_stats_verdict_proved', stats)),
        "accepted_replay_badges": len(re.findall(r'class="[^"]*bp_stats_replay_accepted', stats)),
        "rendered_progress": {kind: text(body) for kind, body in progress},
        "rendered_size": {kind: text(body) for kind, body in size},
        "replay_coverage_details": {kind: text(body) for kind, body in details},
    }


def omitted_drawings(log):
    result = re.search(r"^Blueprint graph: ([\d,]+) neighbourhood drawings left out", log, re.M)
    return int(result[1].replace(",", "")) if result else 0


def verify(args):
    lake = ["lake", "--no-cache", "--no-ansi"]

    def stage(name, *command, environment=None):
        return measure(args, "verification", 1, name, [*lake, *command], environment=environment)

    proof_log = stage("proof-build", "build").read_text(errors="replace")
    warnings = warning_counts(proof_log)
    if warnings.get("project: challenge sorry") != 5 or any(key.endswith(": other sorry") for key in warnings):
        raise SystemExit("Unexpected sorry warnings; see the proof build log")
    axioms = stage("axioms", "env", "lean", "scripts/PrintAxioms.lean").read_text()
    expected = {"mainTheorem", "mainTheoremApprox", "separation", "separationClosure", "permanent_over_real"}
    declarations = re.findall(r"^'Solution\.(\w+)' depends on axioms: \[([^\]]+)\]$", axioms, re.M)
    if len(declarations) != 5 or {name for name, _ in declarations} != expected or any(
        set(names.split(", ")) != {"propext", "Classical.choice", "Quot.sound"} for _, names in declarations
    ):
        raise SystemExit("Unexpected solution axioms; see the axioms log")
    stage("statement-spelling", "env", "lean", "scripts/StatementSpelling.lean")
    stage("build-vbp", "build", "vbp")
    stage("comparator-layout", "exe", "vbp", "comparator-check")
    stage("generate-nodes", "env", "lean", "--run", "blueprint/scripts/GenerateNodes.lean")
    replay_log = stage("blueprint-build-and-replay", "exe", "vbp", "build",
                       environment={"VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD": ""}).read_text(errors="replace")
    replay_checkers = re.findall(r"^Kernel replay: (con-leche|con-ron) ran for (.+)$", replay_log, re.M)
    if ({name for name, _ in replay_checkers} != {"con-leche", "con-ron"}
            or "was accepted by both checkers before" in replay_log
            or "Kernel replay: accepted by both checkers" not in replay_log):
        raise SystemExit("Expected fresh acceptance by both external checkers; see the blueprint build log")
    check = stage("blueprint-check", "exe", "vbp", "check").read_text()
    report = json.loads(check.splitlines()[-1])
    if report.get("ok") is not True:
        raise SystemExit(f"Blueprint consistency check failed: {report}")
    site = args.work / "_out/site/html-multi"
    stats = rendered_stats((site / "Project-Stats/index.html").read_text())
    if stats["proved_verdicts"] != 5 or not stats["accepted_replay_badges"]:
        raise SystemExit(f"Unexpected rendered theorem verdicts: {stats}")
    artifacts = {
        name: {"sha256": digest(site / name), "bytes": (site / name).stat().st_size}
        for name in [
            "index.html",
            "Project-Stats/index.html",
            "-verso-data/blueprint-manifest.json",
            "-verso-data/blueprint-html-cache.json",
        ]
    }
    site_bytes = sum(file.stat().st_size for file in site.rglob("*") if file.is_file())
    if site_bytes >= 1_000_000_000:
        raise SystemExit(f"Site exceeds the Pages size limit ({site_bytes} bytes)")
    append_json(args.output, {
        "scenario": "verification",
        "trial": 1,
        "stage": "site-artifacts",
        **stats,
        "fresh_replay_checkers": dict(replay_checkers),
        "replay_messages": re.findall(r"^Kernel replay: (.+)$", replay_log, re.M),
        "omitted_neighbourhood_drawings": omitted_drawings(replay_log),
        "blueprint_check": report,
        "site_bytes": site_bytes,
        "site_files": sum(f.is_file() for f in site.rglob("*")),
        "html_pages": sum(f.is_file() for f in site.rglob("*.html")),
        "olean_files": sum(1 for _ in (args.work / ".lake/build/lib/lean").rglob("*.olean")),
        "artifacts": artifacts,
    })


def main():
    args = parse_args()
    args.work = args.work.resolve()
    args.output = args.output.resolve()
    if not (args.work / ".lake/packages").is_dir() or not (args.work / "Statement.lean").is_file():
        raise SystemExit("--work must identify a provisioned vp-vnp directory")
    def git(*command):
        return subprocess.check_output(["git", "-C", args.work, *command], text=True).strip()

    args.revision = git("rev-parse", "--verify", args.revision + "^{commit}")
    if (args.work != Path(git("rev-parse", "--show-toplevel")) / "vp-vnp"
            or git("branch", "--show-current") or git("rev-parse", "HEAD") != args.revision
            or git("status", "--porcelain", "--untracked-files=no")):
        raise SystemExit("--work must be a clean detached project checkout at --revision")
    if (args.work / ".lake").is_symlink() or (args.work / ".lake/build").is_symlink():
        raise SystemExit("Use private project build outputs")
    if min(args.threads, args.trial) < 1:
        raise SystemExit("thread count and trial number must be positive")
    os.environ["LEAN_NUM_THREADS"] = str(args.threads)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.logs = args.output.with_suffix(".logs")
    args.logs.mkdir()
    args.output.touch(exist_ok=False)
    append_json(args.output, {
        "format_version": 1,
        "revision": args.revision,
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "host": platform.platform(),
        "logical_cpus": os.cpu_count(),
        "lake_version": subprocess.check_output(["lake", "--version"], cwd=args.work, text=True).strip(),
        "manifest_sha256": digest(args.work / "lake-manifest.json"),
        "trial": args.trial,
        "threads": args.threads,
        "scenario": args.scenario,
        "load_at_start": os.getloadavg(),
    })
    if args.scenario == "verify":
        verify(args)
    elif args.scenario == "replay":
        replay_exports(args)
    else:
        proof_builds(args)


if __name__ == "__main__":
    main()

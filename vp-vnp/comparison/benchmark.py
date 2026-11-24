#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Eric Vergo, GPT-6.2 (OpenAI)
"""Measure vp-vnp builds in a disposable project copy with provisioned dependencies."""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import time


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True,
                        help="disposable vp-vnp directory; project build outputs are deleted")
    parser.add_argument("--revision", required=True, help="source revision recorded in the results")
    parser.add_argument("--output", type=Path, required=True, help="new JSON Lines result file")
    parser.add_argument("--scenario", choices=("clean", "warm", "foundation", "branch", "chapter", "verify"), required=True)
    parser.add_argument("--trial", type=int, default=1)
    parser.add_argument("--threads", type=int, default=4)
    return parser.parse_args()


def append_json(output, record):
    with output.open("a") as file:
        file.write(json.dumps(record, sort_keys=True) + "\n")


def measure(args, scenario, trial, name, command):
    log = args.logs / f"{scenario}-{trial}-{name}.log"
    print(f"{scenario} {trial} {name}", flush=True)
    started = time.perf_counter()
    with log.open("wb") as file:
        run = subprocess.Popen(command, cwd=args.work, stdout=file, stderr=subprocess.STDOUT)
        _, status, usage = os.wait4(run.pid, 0)
        run.returncode = os.waitstatus_to_exitcode(status)
    elapsed = time.perf_counter() - started
    built = re.findall(r"\[\d+/\d+\] Built ([^\s(]+)", log.read_text(errors="replace"))
    libraries = {"Statement", "Paper", "NS1", "Nc", "Ov", "Comparator", "VpVnpBlueprint"}
    modules = sorted({name for name in built if name.split(".")[0] in libraries})
    append_json(args.output, {
        "scenario": scenario,
        "trial": trial,
        "stage": name,
        "command": command,
        "cpu_user_seconds": usage.ru_utime,
        "cpu_system_seconds": usage.ru_stime,
        "max_rss_bytes": usage.ru_maxrss * (1 if platform.system() == "Darwin" else 1024),
        "built_modules": modules,
        "lake_built_jobs": len(built),
        "exit_code": run.returncode,
        "wall_seconds": round(elapsed, 6),
        "log": log.relative_to(args.output.parent).as_posix(),
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
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(args):
    lake = ["lake", "--no-cache", "--no-ansi"]

    def stage(name, *command):
        return measure(args, "verification", 1, name, [*lake, *command])

    stage("proof-build", "build")
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
    stage("blueprint-build-and-replay", "exe", "vbp", "build")
    check = stage("blueprint-check", "exe", "vbp", "check").read_text()
    report = json.loads(check.splitlines()[-1])
    if report.get("ok") is not True:
        raise SystemExit(f"Blueprint consistency check failed: {report}")
    site = args.work / "_out/site/html-multi"
    stats = (site / "Project-Stats/index.html").read_text()
    proved = len(re.findall(r'class="[^"]*bp_stats_verdict_proved', stats))
    accepted = len(re.findall(r'class="[^"]*bp_stats_replay_accepted', stats))
    if proved != 5 or not accepted:
        raise SystemExit(f"Unexpected theorem verdicts: proved={proved}, accepted={accepted}")
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
        "proved_verdicts": proved,
        "accepted_replay_badges": accepted,
        "blueprint_check": report,
        "site_bytes": site_bytes,
        "site_files": sum(f.is_file() for f in site.rglob("*")),
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
    else:
        proof_builds(args)


if __name__ == "__main__":
    main()

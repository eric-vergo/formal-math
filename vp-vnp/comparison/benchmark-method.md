# Reproducing the build measurements

Use a provisioned detached worktree for each revision. Give each worktree a private `vp-vnp/.lake/build`; the same pinned dependency sources and compiled dependency artifacts may be provisioned in both. Provision the proof, vbp, and the generated blueprint sources before collecting the samples. The driver verifies the checked-out revision, refuses tracked changes, and refuses symlinked project build directories. Use one host and avoid overlapping builds, replay, publishing, or interactive Lean work during measurements.

Run this Bash driver from the repository root. Supply detached worktrees for the baseline, frozen proof, and integrated blueprint. Use the exact after revision of the source inventory for chapter and site measurements. Neither result directory may already contain records from another run.

```bash
set -euo pipefail
before_work=/absolute/path/to/baseline/worktree/vp-vnp
proof_work=/absolute/path/to/frozen-proof/worktree/vp-vnp
after_work=/absolute/path/to/integrated/worktree/vp-vnp
proof_rev=34a072623bbb19c9b6dbe15f48bd62e60c804618
before_rev=9fd368ad9bbb717511e76e5560d6c3803915f922
after_rev=246c5eac849a9e15ba429570c310686cf793d41a
runner="$PWD/vp-vnp/comparison/benchmark.py"
out="$PWD/vp-vnp/_out/comparison-timing"

run_pairs() {
  local trial scenario side work revision
  local -a sides
  for trial in 1 2 3; do
    sides=(before after)
    if [[ "$trial" == 2 ]]; then sides=(after before); fi
    for scenario in "$@"; do
      for side in "${sides[@]}"; do
        if [[ "$side" == before ]]; then
          work="$before_work"
          revision="$before_rev"
        elif [[ "$scenario" == chapter ]]; then
          work="$after_work"
          revision="$after_rev"
        else
          work="$proof_work"
          revision="$proof_rev"
        fi
        python3 "$runner" --work "$work" --revision "$revision" \
          --scenario "$scenario" --trial "$trial" --threads 4 \
          --output "$out/$side/$scenario-$trial.jsonl"
      done
    done
  done
}
run_pairs clean warm foundation branch
```

- Clean removes only the detached worktree's `vp-vnp/.lake/build` then runs the default proof targets with Lake cache downloads disabled. Dependency artifacts and the host's filesystem cache are retained. Warm repeats that command after clean.
- Foundation, branch and chapter append the same comment to `Paper/Identity.lean`, `Paper/Approximate.lean` and `blueprint/VpVnpBlueprint/Chapters/Assembly.lean`, respectively. Each target is primed before its edit. The captured `edited` stage runs the build that responds to that edit. The driver restores the original bytes and checks the restored build. Chapter builds the Assembly Lean module and its imports. It measures chapter elaboration. Site rendering, source highlighting and checker replay run in verification.
- `LEAN_NUM_THREADS=4` is fixed across the paired commands. This is the Lean runtime's task-pool setting. Lake can launch more than one Lean process, so it gives no global cap of four runnable threads. File cache, background system load, and differences in dependency preparation can influence timings. See the hardware, toolchain, dependency-manifest digest, recorded start load and trial rows in the raw data.
- The harness measures wall time around the timed subprocess. CPU time adds user and system time from the operating system's `wait4` resource usage, including descendant usage accounted to that subprocess. On macOS `ru_maxrss` is reported in bytes. On Linux the harness multiplies the reported KiB by 1,024. The resulting maximum resident set size is the OS-reported high-water figure for the waited command and usage propagated to it. It cannot give total memory held by concurrent descendants at one instant. CPU time can exceed elapsed wall time when processes run in parallel.
- Rebuilt modules are the distinct project Lean modules that Lake logs as `Built`. Cached diagnostic replays and build facets such as `:c.o` are excluded. `lake_built_jobs` retains the separate count of all `Built` jobs, including dependency jobs and non-module facets. Each stage includes its command, wall time, CPU times, RSS, exit code, log path and SHA-256. The outer JSON Lines rows retain all three edit phases and each individual sample.

The first baseline clean sample started at 22:40:53 UTC on November 24, 2026. Its after partner started at 13:59:07 UTC on November 25. The driver reused this completed baseline run after confirming its revision, scenario, trial, thread setting, completed stage and zero exit status. This pair has an overnight gap. The metadata retain the start load and timestamp of every sample.

The capture step archives Lake’s elapsed job times for project modules in the three clean logs. The report shows the trials and medians for selected rewrites. These figures retain Lake’s rounding and include contention from other jobs in the same build.

The checked-in JSON archive uses `$HOME` for the local home directory, `$VP_VNP_WORKTREE` for the project root of the recorded side, and `$EXPORT_RUN` for the temporary export directory suffix. The capture step leaves the original JSON Lines and logs untouched. The timings, tool fingerprints and SHA-256 digests cover the original runs.

## Verification runs

Run the following separately from the paired timing samples. A successful site run includes Lean proof compilation, the axioms of the five exports, the statement-spelling proofs, the Comparator layout check, generator, full site and replay, and `vbp check`. Before relying on the results, use `git diff --exit-code "$before_rev" "$after_rev" -- vp-vnp/Statement.lean vp-vnp/Comparator vp-vnp/paper.pdf` to check exact tracked bytes independently. The Linux upstream Comparator workflow is a separate check from `vbp comparator-check`, which checks the challenge layout.

```bash
python3 "$runner" --work "$after_work" --revision "$after_rev" \
  --scenario verify --threads 4 --output "$out/after/verify.jsonl"
python3 "$runner" --work "$proof_work" --revision "$proof_rev" \
  --scenario replay --threads 4 --output "$out/after/replay.jsonl"
```

The full site verification sets `VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD` to an empty string for the site command. At the pinned VersoBlueprint revision this disables reading and writing the acceptance record. The harness requires two fresh checker run lines and a combined acceptance. The separate `replay` scenario reads the five roots from the pinned Comparator JSON, exports their transitive terms with the toolchain's `leanexport`, and invokes `con-leche` and `con-ron` directly with `--verified --jobs=4`. It requires each process to report accepting at least all the exported declaration records. This run checks only the five roots and their dependencies. It uses a disposable export file and records its size, SHA-256, and declaration count along with each checker binary's fingerprint. The site replay has a wider scope because it also includes selected blueprint nodes.

The proof of each challenge theorem deliberately uses `sorry`. The proof build verifies that the five corresponding warnings come from `Comparator/VpVnp/Challenge.lean` and fails if it sees any other `sorry` warning. The complete project inventory and declaration command totals count the challenge declarations in their own source scope. The proof-body size distribution and the five solution kernel closures exclude the challenge proofs. The blueprint's rendered progress and external replay coverage reflect the rendered node set and checker policy. A checked Lean declaration and a paper-to-formal claim are different kinds of evidence. The site's informal claims and intentionally unchecked prose are reported separately.

After site verification, build the Assembly target once in each worktree before running the three chapter pairs. The preprime places both sides on a prepared chapter build. Every individual sample still performs and records its own prime, edited build and restore. Only the edited build contributes to the chapter timing comparison.

```bash
(cd "$before_work" && LEAN_NUM_THREADS=4 lake --no-cache --no-ansi build VpVnpBlueprint.Chapters.Assembly)
(cd "$after_work" && LEAN_NUM_THREADS=4 lake --no-cache --no-ansi build VpVnpBlueprint.Chapters.Assembly)
run_pairs chapter
```

For both baseline verification scenarios use the baseline revision and private worktree. In the historical baseline site run, the generator found an identical previously accepted export. The frozen five-root runs invoked both checker executables directly. The integrated site requires fresh execution of both checkers. The capture script accepts a baseline site directory only with its matching verification JSONL. It verifies the recorded sizes and hashes before extracting additional baseline page statistics. Each raw JSONL must remain beside its log directory. The compressed archive includes per-command log hashes, command lines, the reported start load, timings, tool fingerprints and checker results.

```bash
cd vp-vnp
python3 comparison/capture-results.py --runs "$out" --output comparison/benchmark-results.json.gz
python3 comparison/compare.py --before comparison/inventory-baseline.json.gz \
  --after comparison/inventory-after.json.gz --proof-after "$proof_rev" \
  --timings comparison/benchmark-results.json.gz --verification comparison/benchmark-results.json.gz
```

The renderer checks the recorded revision separately for each timing and replay scenario. When the after pins differ, it requires Git-tree equality across the proof libraries, public specification, Comparator, proof scripts, Lake configuration and manifest, toolchain pin and paper PDF. The chapter and full site require the integrated pin. The three trials are paired by index and order, with the second pair reversed. Ranges and medians describe the observed local runs. Background load and OS caching can move all three readings in one direction. Three trials do not establish a population speedup or attribute a change in time to an individual proof.

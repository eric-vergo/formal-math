# Reproducing the build measurements

Use a provisioned detached worktree for each revision. Give each worktree a private `vp-vnp/.lake/build`; the same pinned dependency sources and compiled dependency artifacts may be provisioned in both. Provision the proof, vbp, and the generated blueprint sources before collecting the samples. The driver verifies the checked-out revision, refuses tracked changes, and refuses symlinked project build directories. Use one host and avoid overlapping builds, replay, publishing, or interactive Lean work during measurements.

Run this Bash driver from the repository root. Supply the two absolute paths and the exact after revision used for the source inventory. Neither result directory may already contain records from another run.

```bash
set -euo pipefail
before_work=/absolute/path/to/baseline/worktree/vp-vnp
after_work=/absolute/path/to/cleanup/worktree/vp-vnp
before_rev=9fd368ad
after_rev=REPLACE_WITH_THE_REPORTS_AFTER_REVISION
runner="$PWD/vp-vnp/comparison/benchmark.py"
out="$PWD/vp-vnp/_out/comparison-timing"

for trial in 1 2 3; do
  sides=(before after)
  if [[ "$trial" == 2 ]]; then sides=(after before); fi
  for scenario in clean warm foundation branch chapter; do
    for side in "${sides[@]}"; do
      if [[ "$side" == before ]]; then
        work="$before_work"
        revision="$before_rev"
      else
        work="$after_work"
        revision="$after_rev"
      fi
      python3 "$runner" --work "$work" --revision "$revision" \
        --scenario "$scenario" --trial "$trial" --threads 4 \
        --output "$out/$side/$scenario-$trial.jsonl"
    done
  done
done
```

- Clean removes only the detached worktree's `vp-vnp/.lake/build` then runs the default proof targets with Lake cache downloads disabled. Dependency artifacts and the host's filesystem cache are retained. Warm repeats that command after clean.
- Foundation, branch and chapter append the same comment to `Paper/Identity.lean`, `Paper/Approximate.lean` and `blueprint/VpVnpBlueprint/Chapters/Assembly.lean`, respectively. Each target is primed before its edit. The captured `edited` stage runs the build that responds to that edit. The driver restores the original bytes and checks the restored build. Chapter builds the Assembly Lean module and its imports. It measures chapter elaboration. Site rendering, source highlighting and checker replay run in verification.
- `LEAN_NUM_THREADS=4` is fixed across the paired commands. This is the Lean runtime's task-pool setting. Lake can launch more than one Lean process, so it gives no global cap of four runnable threads. File cache, background system load, and differences in dependency preparation can influence timings. See the hardware, toolchain, dependency-manifest digest, recorded start load and trial rows in the raw data.
- The harness measures wall time around the timed subprocess. CPU time adds user and system time from the operating system's `wait4` resource usage, including descendant usage accounted to that subprocess. On macOS `ru_maxrss` is reported in bytes. On Linux the harness multiplies the reported KiB by 1,024. The resulting maximum resident set size is the OS-reported high-water figure for the waited command and usage propagated to it. It cannot give total memory held by concurrent descendants at one instant. CPU time can exceed elapsed wall time when processes run in parallel.
- Rebuilt modules are the distinct project Lean modules that Lake logs as `Built`. Cached diagnostic replays and build facets such as `:c.o` are excluded. `lake_built_jobs` retains the separate count of all `Built` jobs, including dependency jobs and non-module facets. Each stage includes its command, wall time, CPU times, RSS, exit code, log path and SHA-256. The outer JSON Lines rows retain all three edit phases and each individual sample.

## Verification runs

Run the following separately from the paired timing samples. A successful site run includes Lean proof compilation, the axioms of the five exports, the statement-spelling proofs, the Comparator layout check, generator, full site and replay, and `vbp check`. Before relying on the results, use `git diff --exit-code "$before_rev" "$after_rev" -- vp-vnp/Statement.lean vp-vnp/Comparator vp-vnp/paper.pdf` to check exact tracked bytes independently. The Linux upstream Comparator workflow is a separate check from `vbp comparator-check`, which checks the challenge layout.

```bash
python3 "$runner" --work "$after_work" --revision "$after_rev" \
  --scenario verify --threads 4 --output "$out/after/verify.jsonl"
python3 "$runner" --work "$after_work" --revision "$after_rev" \
  --scenario replay --threads 4 --output "$out/after/replay.jsonl"
```

The full site verification sets `VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD` to an empty string for the site command. At the pinned VersoBlueprint revision this disables reading and writing the acceptance record. The harness requires two fresh checker run lines and a combined acceptance. The separate `replay` scenario reads the five roots from the pinned Comparator JSON, exports their transitive terms with the toolchain's `leanexport`, and invokes `con-leche` and `con-ron` directly with `--verified --jobs=4`. It requires each process to report accepting at least all the exported declaration records. This run checks only the five roots and their dependencies. It uses a disposable export file and records its size, SHA-256, and declaration count along with each checker binary's fingerprint. The site replay has a wider scope because it also includes selected blueprint nodes.

The statement of each challenge theorem deliberately contains `sorry`. The proof build verifies that the five corresponding warnings come from `Comparator/VpVnp/Challenge.lean` and fails if it sees any other `sorry` warning. Challenge declarations are counted as written declarations in the project inventory, with their own source scope. The proof-body size distribution and the five kernel closures exclude the challenge stubs. The blueprint's rendered progress and exterior replay coverage reflect the rendered node set and checker policy. A checked Lean declaration and a paper-to-formal claim are different kinds of evidence. The site's informal claims and intentionally unchecked prose are reported separately.

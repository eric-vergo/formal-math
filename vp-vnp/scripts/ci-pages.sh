#!/usr/bin/env bash
# Build the development and its blueprint site for GitHub Pages (used by
# .github/workflows/vp-vnp-blueprint.yml). Run from the folder vp-vnp; the site is written to
# _out/site/html-multi/. Any failed step fails the script.

set -euo pipefail

# The development, the statement file, the challenge and the solution (the default targets).
lake build

# The axioms of the five theorems: nothing beyond Lean's standard three.
axioms=$(lake env lean scripts/PrintAxioms.lean)
echo "$axioms"
test "$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" <<<"$axioms")" -eq 5

# The layout of the Comparator challenge (Comparator/<Name>/), checked from the files alone.
lake exe vbp comparator-check

# The chapters generated from the compiled code: every declaration that no written chapter
# discusses yet, without an informal statement.
lake env lean --run blueprint/scripts/GenerateNodes.lean

# The site, with the kernel replay of the compiled modules by con-leche and con-ron.
lake exe vbp build

# The consistency check of the generated site prints a JSON report with "ok": true or false.
report=$(lake exe vbp check | tail -n 1)
echo "$report"
case "$report" in
  *'"ok":true'*) ;;
  *) echo "vbp check reported problems" >&2; exit 1 ;;
esac

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json

# The headline: every judged theorem is proved and both kernel checkers accepted the replay.
stats=_out/site/html-multi/Project-Stats/index.html
test "$(grep -Eo 'class="[^"]*bp_stats_verdict_proved' "$stats" | wc -l)" -ge 5
grep -Eq 'class="[^"]*bp_stats_replay_accepted' "$stats"

# GitHub Pages publishes sites of at most 1 GB.
size_kb=$(du -sk _out/site/html-multi | cut -f1)
echo "site size: ${size_kb} KiB"
test "$size_kb" -lt 1000000

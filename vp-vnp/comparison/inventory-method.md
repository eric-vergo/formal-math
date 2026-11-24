# Reproducing the vp-vnp inventory

The baseline is commit `9fd368ad`. The source measurements read a staged copy and verify each
`vp-vnp` file against its Git blob. The full repository tree inventory records tracked paths,
Git object IDs, types, modes and blob sizes. Detailed source measurements cover `vp-vnp`.
Run from the root of this repository:

```bash
revision=9fd368ad
work="$PWD/vp-vnp/_out/inventory-baseline"
mkdir -p "$work"
git archive "$revision" vp-vnp | tar -x -C "$work"

# Point at a local build of the same proof sources and dependency revisions.
build=/absolute/path/to/built/vp-vnp
ln -s "$build/.lake" "$work/vp-vnp/.lake"
lean_path=$(cd "$build" && lake env printenv LEAN_PATH)
lean_bin=$(cd "$build" && lake env which lean)
(
  cd "$work/vp-vnp"
  LEAN_PATH="$lean_path" "$lean_bin" --run blueprint/scripts/GenerateNodes.lean
)
vp-vnp/comparison/inventory-run.sh "$revision" "$work/vp-vnp" "$build" "$work"
python3 vp-vnp/comparison/inventory.py \
  --revision "$revision" --source "$work/vp-vnp" \
  --compiled "$build/.lake/build/lib/lean" \
  --generated "$work/vp-vnp/blueprint/VpVnpBlueprint/Generated" \
  --kernel "$work/kernel.json" \
  --output vp-vnp/comparison/inventory-baseline.json.gz \
  --summary vp-vnp/comparison/inventory-baseline-summary.json
```

For the baseline, the local build came from commit `83c8def`. All 323 proof and Comparator Lean
sources are byte-identical between it and `9fd368ad`, as is the Lean toolchain. The shared Lake
dependencies are pinned to the same revisions. The generated files came from running the
generator in the staged `9fd368ad` source tree against those compiled proofs. No site build is
required to count the artifacts emitted by the generator.

For an after measurement, use an exact Git revision and compiled proof build of that revision.
Use a separate output directory and change the output filenames. The expanded `kernel.json`
in the ignored output directory records complete closures including Mathlib and Lean.
`export_project_names` in the compact inventory maps each export to its project declarations,
including compiler-generated constants. Use those lists for per-export route flags.

## Counting rules

- **Source lines.** Physical lines include the last line even without a newline. A code line has
  nonwhitespace Lean text outside comments. A comment line includes a token of a line comment
  or a nested block comment. Mixed lines appear in both counts. Blank lines have neither.
  Lines beginning at the first top-level Verso `#doc` command are counted as document lines.
  Non-Lean tracked text has physical counts and binary data has byte counts.
- **Proof commands.** Use Lean's `.ilean` declaration ranges and selection ranges, in zero-based
  UTF-16 coordinates. Report one entry per distinct source command whose selection follows
  `theorem` or `lemma`. If the compiler records only the selection range of a single-line
  proof, take its command span from that line. Include the Comparator challenge stubs in proof counts, with their own
  module and file entries. Count non-comment lines in the body after the first top-level
  `:=` or `where`, or from the first equation arm. An inline body counts as one line. A `by`
  introducing a tactic block is part of the body. Declaration command totals use a separate
  source scan, which counts a mutual declaration once per written command. The exact-body
  duplicate report hashes the body after masking comments and collapsing whitespace. Matching
  bodies can be proofs of different statements.
- **Groups.** Proof and source aggregates are reported by library and by the immediate directory
  inside a library, when present. The statement, Comparator, authored blueprint and support
  records are identified separately. Generated blueprint files have their own inventory.
- **Imports.** Read proof imports from the compiler's `.ilean` data, and blueprint and support
  imports from source. Keep external imports in the adjacency map. Root metrics count local
  edges, including the root's own outgoing edges, and measure depth as the largest shortest
  distance from the root along local imports. Fanout counts distinct local imports.
- **Blueprint.** Count written and generated directives by kind, preserve source lines and
  declaration associations, and count listed-by-name entries separately from full nodes.
  Written names use the generator's association convention. The compiled pruning check also
  treats `InlineLean.name` roles and fully qualified names in authored blueprint text as roots
  when they resolve to a declaration. The source scan counts directives and listings in the
  emitted Lean sources. It does not count HTML pages, rendered fragments or HTML graph edges.
- **Kernel dependencies.** Traverse each export's compiled type and proof, recursively. Use
  Lean's `ConstantInfo.getUsedConstantsAsSet` to include definition and theorem bodies,
  opaque values, and the inductive metadata that Lean's helper includes. Each declaration
  is identified by its canonical name and defining module. Closures include their root.
  Count distinct non-self edges from each visited declaration. Depth is the largest shortest
  distance from the root. Max fanout is the largest distinct dependency count of any declaration
  in the closure. Project membership comes from the explicitly imported project module list.
- **Pruning candidates.** Report named source proofs outside both the export and authored
  blueprint kernel closures. The smaller list additionally requires zero explicit source
  usages from the project's `.ilean` files. These lists do not establish that removing a
  declaration preserves elaboration. Tactic attributes and other implicit consumers require
  a rebuild. Blueprint-generated listings are derived from whatever source is present and
  therefore do not make a declaration a pruning root.

## Checking the paper's concordance

Run the row audit against the kernel output and the matching source checkout:

```bash
python3 vp-vnp/comparison/table-routes.py "$work/kernel.json" --root "$work/vp-vnp"
```

The tab-separated report names each printed row, each associated Lean constant, its defining
source file, and its membership in the five export closures in the order M, S, A, C, R. The
numbered and display rows use their first declaration for the route label. Definition rows
keep their editorial label and report the computed membership of each name. The unnumbered
table is checked as well. A missing declaration, missing source file, unexpected table format,
or mismatch between a printed route label and the compiled membership fails the check.

Pass `--baseline-root PATH_TO_BASELINE_VP_VNP` to compare the primary declaration for each
formalized numbered or display row with the port. This reuses the comment and whitespace rules
of `statement-diff.py`, requires a unique declaration name in the Paper library on each side
and allows it to move between modules. It compares the written declaration, including definition
bodies. Surrounding section parameters and the meanings of referenced definitions are outside
this text comparison. The frozen specification check compares the files themselves.

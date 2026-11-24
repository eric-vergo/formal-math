/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Informal

#doc (Manual) "How to check this yourself" =>

%%%
tag := "chapter-checking"
file := "checking"
htmlSplit := .never
number := false
%%%

A reader need not take any report on this site on trust: everything a machine can check here can
be checked again with the commands of this chapter. They establish, in this order, that the
development compiles; that the five theorems rest on no axiom beyond Lean's standard three; that
the statements of this branch are those of the upstream development up to one spelling; that the
solution proves the statements of the challenge; and that checkers other than Lean's kernel
accept the proofs. None of them establishes that the statements mean what the paper claims. For
that there is no command, only {ref "chapter-statement"}[The statement to trust].

# Which build

The paper's development uses Lean 4.33.1 and Mathlib at commit `0df444a360e` (Section 3, page 11,
of {repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]). This site is built from the branch `blueprint` of
a fork of the repository, in which the development is ported to Lean 4.36.0 and Mathlib
`v4.36.0`, the versions the site's tools need. The files `lean-toolchain` and
`lake-manifest.json` in the folder {repoFile "vp-vnp"}[`vp-vnp`] name the versions, and
{repoFile "vp-vnp/PORTING.md"}[`PORTING.md`] lists every change the port made to a Lean file:
the spelling of a coefficient in four statements, and 28 repairs of proofs in 27 files, with the
reason for each. In its words: “No `sorry` was added, no axiom, no `native_decide`, and no
`maxHeartbeats` was raised”.

Every command below, and every report on this site, is about that build. The checks that the
paper reports (Section Q.1, page 66) were made on the original one.

# Building the proof and printing its axioms

With [elan](https://github.com/leanprover/elan) installed, in the folder `vp-vnp`:

```
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
lake env lean scripts/StatementSpelling.lean
```

The first command fetches Mathlib's compiled files; the second compiles the development with
Lean's kernel checking every proof. The README of the folder, on what to expect: “`lake build`
prints the five sorry warnings of Comparator/VpVnp/Challenge.lean and, besides them, deprecation
and linter warnings from the new toolchain and Mathlib”. The five warnings are the five theorems
of the challenge file, which states them without proof on purpose; a `sorry` warning from any
other file would mean an unproved statement.

{repoFile "vp-vnp/scripts/PrintAxioms.lean"}[`scripts/PrintAxioms.lean`] runs `#print axioms` on
the five theorems of `Solution.lean`. For each it must print

```
'Solution.mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

with the theorem's name, and no other axiom: these three are the axioms of Lean's standard logic,
and the list is computed over everything the theorem depends on. An unproved statement anywhere
below a theorem would appear in this list as `sorryAx`, and a proof by compiled evaluation
(`native_decide`) as a further axiom.

{repoFile "vp-vnp/scripts/StatementSpelling.lean"}[`scripts/StatementSpelling.lean`] prints
nothing when its proofs check. It is the machine-checked part of the argument that the one
respelled line of `Statement.lean` means what the printed line means
({ref "statement-spelling"}[The one line this build spells differently]).

For the writing of this chapter the last two commands were run on the build of this branch, with
the outputs just described.

# Comparing the statements with upstream

That this branch states what the upstream development states is checked from the texts. With a
Git remote `upstream` for `anthropics/formal-math` fetched:

```
python3 -I scripts/statement-diff.py upstream/vp-vnp HEAD
```

The script {repoFile "vp-vnp/scripts/statement-diff.py"}[`scripts/statement-diff.py`] compares,
between the two revisions, every declaration of `Statement.lean`, of the challenge and the
solution, of `Paper.lean` and of every file under `Paper/`: for a theorem the text up to the
first `:=`, that is, the statement without the proof; for a definition or structure the whole
declaration, since its body is part of what a statement means; comments removed. It lists each as
the same, changed, or present on one side only, and it classes a change as one of the
coefficient's spelling only when rewriting upstream's `coeff A B` to `B.coeff A` gives this
branch's text exactly. Its last line, when run for this chapter against the upstream commit
`918c8e2`:

```
summary: 733 same, 4 changed only in the spelling of the coefficient, 0 changed, 0 only in OLD, 0 only in NEW (declarations, plus one entry per file for its top-level commands)
```

and its exit status is 2 (0 would mean no change at all, 1 any other change). The four are
`Statement.Approximates`, `Paper.def_approx`, `Paper.approx_rate_closed` and
`Paper.lem_transfer_approx`. For `Statement.lean` alone, `git diff upstream/vp-vnp -- Statement.lean`
shows the one line.

The comparison covers the statement file, the judged theorems and the library `Paper`, whose
theorems state the paper's numbered statements. It does not cover the libraries `Nc`, `NS1` and
`Ov` underneath, where the port changed proofs and the same spelling in some auxiliary
statements; those are checked by the build, not by this script. And it compares two revisions of
Lean text: it is a check that nothing else was edited, not a proof that the two spellings agree,
which is the subject of the section cited above.

# The challenge file and Comparator

The file {repoFile "vp-vnp/Comparator/VpVnp/Challenge.lean"}[`Challenge.lean`] states the five
theorems with `sorry` in place of their proofs and imports nothing but `Statement.lean`;
{repoFile "vp-vnp/Comparator/VpVnp/Solution.lean"}[`Solution.lean`] proves them; and
{repoFile "vp-vnp/Comparator/VpVnp/comparator.json"}[`comparator.json`] names the five theorems
to be judged and the three axioms a proof may use. The tool Comparator, in the README's words
quoted below, “compares the statements with Challenge.lean and re-checks the proofs”. What such a
comparison is for is protection against a solution that proves something else under the same
name: a statement that silently differs, or a definition that was changed underneath it. What
exactly the tool compares is defined by the tool, not by this chapter.

The paper's account of the upstream run (Section Q.1, page 66): “Comparator accepted them against
`Challenge.lean`, rechecking the proofs with Lean's kernel and with the independently written
checker nanoda.” The README, in the part it shares with upstream, quoted: “The fuller check is the one this repository's CI
runs, bash ../.github/scripts/comparator-check.sh (Linux): Comparator compares the statements with
Challenge.lean and re-checks the proofs with a second, independently written kernel, nanoda.”

On this branch the three files lie in {repoFile "vp-vnp/Comparator/VpVnp"}[`Comparator/VpVnp`],
the layout the site's tools require; the two Lean files are unchanged, and the judged theorems
keep their names and statements. The script
{repoFile "vp-vnp/scripts/comparator-check.sh"}[`scripts/comparator-check.sh`] is upstream's
script adapted to this layout. The README of this branch says of it: “Linux only; not run on this
branch”. So for this branch the Comparator run with nanoda is a check a reader can make, not one
this site reports.

What the site does report is its own comparison, made from the compiled files when the site is
generated. The page _Comparator_, at the end of the table of contents, lists the challenge; the
challenge's page shows the challenge file and the solution file in full, the judged theorems with
their verdicts, the Lean statement of each as the challenge has it, the axioms each proof rests
on, and the paper's sentence beside it as the author's claim. The layout of the challenge files
is checked from the files alone by

```
lake exe vbp comparator-check
```

# The kernel replay

The site has the proofs checked again by programs other than Lean's kernel. The Project Stats
page gives the reason in these words: “A file can keep Lean's kernel from seeing a declaration, in
a project or in something it depends on, and only a replay notices.” When it is
generated, the Lean declarations of its nodes and the five judged theorems are exported together
with every constant they depend on, in this project, in Mathlib and in Lean's own library, and
the export is given to two checkers that ship with the Lean toolchain, `con-leche` and `con-ron`.
The README of the folder reports one such run for the five theorems: “the toolchain's exporter
`leanexport` wrote them with every constant they depend on (61,815 declarations), and the two
checkers that ship with Lean 4.36.0, `con-leche --verified` and `con-ron --verified`, each
accepted the export.”

The result for the build a reader is looking at is on the Project Stats page. For each judged
theorem its verdict is followed by a line that says which checks stand behind it, and the band
_Kernel replay_ says what was checked again while the site was generated, by which programs, with
which result, and what a replay leaves trusted. Those words are the tool's and are not restated
here; the marks and colours of the nodes on every page follow the same result, and the same page
explains each of them. Three things about what such a replay means are worth saying in advance,
since they hold whatever its result.

- A replay checks proofs, again: that each exported declaration is well typed from the exported
  constants and Lean's standard axioms. It reads no source text. The step from the source files
  to the compiled declarations is Lean's elaborator, which stays trusted, as do the exporter and
  the checkers themselves with the compilers they are built with.
- A replay is about one build. A port or an update is a different build, and the verdicts on
  this site are about the port.
- A replay says nothing about what a statement means. A proved Lean statement is a proved Lean
  statement.

# What stays trusted

After every check of this chapter a reader still relies on:

1. `Statement.lean`: that its 98 lines, with the Mathlib definitions they use, say what the
   paper's Theorems 1.1 and 1.4 and Corollary 1.2 say. No tool checks it.
2. The respelled line: that upstream's `coeff d q` and this build's `q.coeff d` are the same
   coefficient. Part of this is machine-checked and part is cited
   ({ref "statement-spelling"}[The one line this build spells differently]).
3. Lean's logic and its implementation: the type theory with the three axioms, the kernel, and
   for a replay the exporter, the two checkers and the elaborator.
4. Mathlib's definitions of the notions the statement file uses, in their documented meaning.

The proofs themselves are not on this list: none of the development's roughly 73,000 lines of
Lean below the statement file has to be read to know that the five statements are proved. That
is the point of the formalization, and it is why this blueprint asks its reader to spend the
effort on the first item.

# Building this site

From the folder `vp-vnp`, after `lake exe cache get` and `lake build`:

```
lake env lean --run blueprint/scripts/GenerateNodes.lean
lake exe vbp build
lake exe vbp check
```

The first command writes the chapters of the part {ref "part-generated"}[The Lean development,
declaration by declaration] from the compiled Lean code; the second builds the site into
`_out/site/html-multi/` (with `--serve` it also serves it) and makes the kernel replay; the third
checks the generated site. The script {repoFile "vp-vnp/scripts/ci-pages.sh"}[`scripts/ci-pages.sh`]
runs the whole sequence as the site's continuous integration does, and fails unless the Project
Stats page shows every judged theorem as proved with both checkers accepting the replay;
{repoFile "vp-vnp/blueprint/README.md"}[the blueprint's README] describes the files of the
blueprint.

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

# Building the proof

The README of the folder {repoFile "vp-vnp"}[`vp-vnp`] gives the commands. With
[elan](https://github.com/leanprover/elan) installed, in that folder:

```
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
```

In the README's words: “The build prints sorry warnings from Challenge.lean only, which states the
theorems without proofs for the fuller check. The last command should name no axiom other than
propext, Classical.choice and Quot.sound.” The file
{repoFile "vp-vnp/scripts/PrintAxioms.lean"}[`scripts/PrintAxioms.lean`] runs `#print axioms` on
the five theorems of `Solution.lean`.

The paper's development uses Lean 4.33.1 and Mathlib at commit `0df444a360e` (Section 3, page 11).
This site is built from the branch `blueprint` of a fork of the repository, in which the
development is ported to Lean 4.36.0 and Mathlib `v4.36.0`, the versions the site's tools need;
`lean-toolchain` and `lake-manifest.json` in the folder name the versions of the build, and the
file {repoFile "vp-vnp/PORTING.md"}[`PORTING.md`] lists every change the port made to the Lean
files, among them the spelling of a coefficient in four statements, `Statement.Approximates` among
them, with the argument that their meaning is unchanged. The site reports on
that build, not on the original one.

# The challenge file and Comparator

A challenge file states the theorems again, with `sorry` in place of their proofs and with no
import other than `Statement.lean`; a comparison then checks that `Solution.lean` proves exactly
these statements, with the same definitions, using no other axioms. The README, quoted: “The
fuller check is the one this repository's CI runs, bash ../.github/scripts/comparator-check.sh
(Linux): Comparator compares the statements with Challenge.lean and re-checks the proofs with a
second, independently written kernel, nanoda.” In this build the challenge, the solution and their
configuration lie in the folder {repoFile "vp-vnp/Comparator/VpVnp"}[`Comparator/VpVnp`], the
layout the site's tools require, and {repoFile "vp-vnp/scripts/comparator-check.sh"}[`scripts/comparator-check.sh`]
runs the same check for that layout.

The site makes its own comparison when it is built, from the compiled files: the page
*Comparator* at the end of the table of contents lists the challenge, and the challenge's page
shows the challenge file and the solution file in full, the judged theorems with their verdicts,
the axioms each proof rests on, and what the comparison is and is not. The layout of the
challenge files is checked from the files alone by

```
lake exe vbp comparator-check
```

# The site's checks

The Project Stats page gives the headline: for each judged theorem, its verdict, with the line
under it that says which checks stand behind it. Its band *Kernel replay* says what was checked
again while the site was generated, by which programs, with which result, and what stays trusted;
the words of that band are the tool's, and this chapter does not restate them. The marks and
colours of the nodes on every page follow the same result, and the Project Stats page explains
each of them.

# Building this site

From the folder `vp-vnp`, after the commands above:

```
lake env lean --run blueprint/scripts/GenerateNodes.lean
lake exe vbp build
lake exe vbp check
```

The first command writes the chapters of the part {ref "part-generated"}[The Lean development,
declaration by declaration] from the compiled Lean code; the second builds the site into
`_out/site/html-multi/` (with `--serve` it also serves it); the third checks the generated site.
The script {repoFile "vp-vnp/scripts/ci-pages.sh"}[`scripts/ci-pages.sh`] runs the whole sequence
as the site's continuous integration does, and {repoFile "vp-vnp/blueprint/README.md"}[the
blueprint's README] describes the files of the blueprint.

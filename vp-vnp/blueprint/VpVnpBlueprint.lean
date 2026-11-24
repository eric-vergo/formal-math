/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import VpVnpBlueprint.GraphCommand
import VpVnpBlueprint.Parts.Claim
import VpVnpBlueprint.Parts.Overview
import VpVnpBlueprint.Parts.Common
import VpVnpBlueprint.Parts.Flat
import VpVnpBlueprint.Parts.Contracting
import VpVnpBlueprint.Parts.Assembly
import VpVnpBlueprint.Parts.Reference
import VpVnpBlueprint.Generated.Part

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "VP ≠ VNP over every field: a blueprint" =>

This site is a blueprint of the paper _VP ≠ VNP over every field_, by Claude (Anthropic), and of
its Lean 4 formalization: the paper's statements in their order, each beside the Lean declaration
that states it, with the dependency graph of the Lean development. The paper is
{repoFile "vp-vnp/paper.pdf"}[`paper.pdf`] in the repository folder
{repoFile "vp-vnp"}[`vp-vnp`]; its full proof is its appendix.

The folder's README says, and this blueprint repeats without change:

> For every field, circuits for the Hamiltonian cycle polynomial, and for the permanent outside characteristic 2, need more than m^(c (log m)^(1/3)) gates for all large m. The same holds for approximating circuits. So VP is a proper subset of VNP, and VNP is not contained in the closure of VP. This does not settle P vs NP.
>
> The result was discovered by an internal research Claude model. This folder holds the paper and its Lean 4 formalization. Both were written by AI models, and no human mathematician has checked the proof.
>
> Research artifact. Not maintained and not accepting contributions.

*How to read this site.*

- {ref "chapter-claim"}[What is claimed] states the five theorems that the formalization proves,
  each with the paper's statement beside the Lean statement, and says what is not claimed.
- {ref "chapter-statement"}[The statement to trust] shows the file `Statement.lean`, which states
  them using Mathlib alone, definition by definition, each with a reading in standard notation.
  That this file says what the paper claims is the one link that no machine checks.
- {ref "chapter-checking"}[How to check this yourself] gives the commands that build the proof,
  print its axioms and run the comparison with the challenge file, and explains what the site's
  own checks establish.
- The parts after these follow the proof: its overview, the common part, the flat case, the
  contracting case and the assembly of the main theorems, each chapter citing the sections and
  pages of the paper it follows; a reference part maps the paper's statements to their Lean
  names. Where a chapter is not written yet, it says so, and the Lean declarations of that part of the proof appear in the last part,
  {ref "part-generated"}[The Lean development, declaration by declaration], which is generated
  from the Lean code and holds every declaration that no chapter discusses yet, without an
  informal statement.

In every node of this site, the text on the left is the paper's (quoted, or adapted where the
node says so) or this blueprint's reading of a Lean statement (marked as such); the Lean code on
the right is the formalization's. A Lean statement can be proved; a sentence of prose is the
paper's claim. What the marks and colours of the site mean, and which checks stand behind them,
is set out on the Project Stats page.

*Licence and attribution.* The paper and its Lean formalization are © 2026 Anthropic, PBC, and licensed under the Apache
License, Version 2.0 (see {repoFile "vp-vnp/LICENSE"}[`LICENSE`] and
{repoFile "vp-vnp/NOTICE"}[`NOTICE`]). This blueprint quotes and adapts statements and sentences
of the paper, cited by section and page, and shows the Lean files of the formalization; it is
released under the same licence. The paper's numbering is the paper's: this site does not number
statements of its own.

{include 0 VpVnpBlueprint.Parts.Claim}

{include 0 VpVnpBlueprint.Parts.Overview}

{include 0 VpVnpBlueprint.Parts.Common}

{include 0 VpVnpBlueprint.Parts.Flat}

{include 0 VpVnpBlueprint.Parts.Contracting}

{include 0 VpVnpBlueprint.Parts.Assembly}

{include 0 VpVnpBlueprint.Parts.Reference}

{include 0 VpVnpBlueprint.Generated.Part}

{vpvnp_graph}

{blueprint_summary}

/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic), GPT-6.2 (OpenAI)
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
that states it, with the idea of each proof and the dependency graph of the Lean development. The
paper is {repoFile "vp-vnp/paper.pdf"}[`paper.pdf`] in the repository folder
{repoFile "vp-vnp"}[`vp-vnp`]; its full proof is its appendix.

The folder's README says, and this blueprint repeats without change:

> For every field, circuits for the Hamiltonian cycle polynomial, and for the permanent outside characteristic 2, need more than m^(c (log m)^(1/3)) gates for all large m. The same holds for approximating circuits. So VP is a proper subset of VNP, and VNP is not contained in the closure of VP. This does not settle P vs NP.
>
> The result was discovered by an internal research Claude model. This folder holds the paper and its Lean 4 formalization. Both were written by AI models, and no human mathematician has checked the proof.
>
> Research artifact. Not maintained and not accepting contributions.

*The claim.* For arithmetic circuits with gates $`+` and $`\times` of fan-in two and arbitrary
constants, of size counted in gates, and with $`\log = \log_2`: there is an absolute constant
$`c > 0`, and for every characteristic $`p` a threshold $`m_0`, such that over every field of
characteristic $`p` and for every $`m \ge m_0`
$$`\text{every circuit for } \mathrm{HC}_m, \text{ and for } \mathrm{PERM}_m \text{ if } p \neq 2, \text{ has more than } m^{c(\log m)^{1/3}} = 2^{c(\log m)^{4/3}} \text{ gates,}`
and the same holds for circuits that approximate these polynomials in the sense of border
complexity. Hence $`\mathrm{VP} \subsetneq \mathrm{VNP}` and
$`\mathrm{VNP} \not\subseteq \overline{\mathrm{VP}}` over every field. The bound is
superpolynomial and quasi-polynomial. The Lean proof takes $`c = 1/1600^2`; no value of $`m_0` is
known. Nothing is claimed about Boolean circuits. {ref "chapter-claim"}[What is claimed] states
all of this precisely.

*What has been checked, and by what.* The formalization proves five Lean theorems, whose
statements are fixed by one file of 98 lines that imports only Mathlib. The original paper reports the checks on Lean 4.33.1. At the Lean 4.36 port
baseline (`9fd368ad`), two further checkers, `con-leche` and `con-ron`, accepted the export
of the five proofs. Eric Vergo and GPT-6.2 (OpenAI) revised the proofs and blueprint on the
fork, keeping the statement file and Comparator files byte for byte. The Project Stats page
reports the checks performed for this site build. No machine checks
that the 98 lines say what the paper claims, and no human mathematician has checked the proof,
the statement file, the Lean development or this blueprint.

*How to read this site.*

- {ref "chapter-claim"}[What is claimed] states the five theorems, each with the paper's
  statement beside the Lean statement, the structure of their quantifiers, what is not claimed,
  and who or what has checked which part.
- {ref "chapter-statement"}[The statement to trust] shows the file `Statement.lean` definition by
  definition, each with a reading in standard notation and a comparison with the definitions of
  the literature. That this file says what the paper claims is the one link that no machine
  checks, and this chapter is where a reader checks it.
- {ref "chapter-checking"}[How to check this yourself] gives the commands that build the proof,
  print its axioms, compare its statements with the upstream development and run the comparison
  with the challenge file, and says what each check establishes and what it leaves trusted.
- {ref "chapter-overview"}[The shape of the proof] is the map of the argument: a common part, a
  dichotomy, a flat case and a contracting case, and their assembly over all fields and for
  approximation. The parts after it follow the proof in the paper's order, each chapter citing
  the sections and pages it follows.
- The reference part holds {ref "chapter-table3"}[the paper's Table 3] with a verdict for every
  numbered statement, a {ref "chapter-glossary"}[glossary] of the paper's terms with their Lean
  names, and {ref "chapter-caveats"}[what a reader should keep in mind].
- The last part, {ref "part-generated"}[The Lean development, declaration by declaration], is
  generated from the Lean code and holds every declaration that no chapter discusses, without an
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

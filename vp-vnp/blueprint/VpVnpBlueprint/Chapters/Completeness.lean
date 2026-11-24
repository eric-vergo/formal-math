/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Generated.Part

open Verso.Genre Manual
open Informal

set_option verso.blueprint.numbering "none"
set_option verso.blueprint.autoDeps true

#doc (Manual) "Completeness gadgets" =>

%%%
tag := "chapter-completeness"
file := "completeness"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendix E (pages 31–33) and Appendix M (page 61) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out Proposition E.1, the clause sums and Corollary E.2 (page 32), Lemma E.3 (page 33), Proposition M.2 and the notion of completeness for grid sums (page 61), and the Lean theorems that put the permanent and the Hamiltonian cycle polynomial in VNP, each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

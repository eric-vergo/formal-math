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

#doc (Manual) "The flat case" =>

%%%
tag := "chapter-flat"
file := "flat-case"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendix E (pages 31–37) and Section N.2 (pages 62–63) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out Lemma E.4, Proposition E.5, Theorem E.6, Lemmas E.7 and E.8, Propositions E.9 and E.10, Theorem E.11, and Lemma N.3 with the flat case for approximating circuits, each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

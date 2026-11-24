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

#doc (Manual) "Tensors, spectral points and prices" =>

%%%
tag := "chapter-spectral"
file := "spectral-points"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendix A of the paper (pages 18–21) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out Definitions A.1 and A.4, Lemmas A.2 and A.3, Propositions A.5, A.7 and A.8, and Theorem A.6 (duality), each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

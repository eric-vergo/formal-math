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

#doc (Manual) "Two crossing wires and nonpositive curvature" =>

%%%
tag := "chapter-curvature"
file := "curvature"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendices B (pages 22–25), C (pages 25–29) and O (pages 64–65) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out Lemma B.1, Propositions B.2 and B.3 with the display (B.2), Theorem C.1, Lemma C.2, Proposition C.3 and Lemma C.4 with its proof in Appendix O, each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

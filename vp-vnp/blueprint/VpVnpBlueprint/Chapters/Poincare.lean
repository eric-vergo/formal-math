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

#doc (Manual) "A Poincaré inequality on unitriangular groups" =>

%%%
tag := "chapter-poincare"
file := "poincare"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendix F of the paper (pages 37–41) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out contracting length functions, Lemmas F.1 to F.5 with the display (F.1), and Theorem F.6, each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

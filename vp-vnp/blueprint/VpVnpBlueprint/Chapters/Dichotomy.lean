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

#doc (Manual) "The two cases" =>

%%%
tag := "chapter-dichotomy"
file := "two-cases"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendix D of the paper (pages 29–31) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out Definition D.1, Theorem D.2 (at least one of the two cases holds) and the remarks of Section D.3, each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

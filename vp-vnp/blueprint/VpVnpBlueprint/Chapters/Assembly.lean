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

#doc (Manual) "All fields and approximate computation" =>

%%%
tag := "chapter-assembly"
file := "assembly"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendices L (pages 59–60), M (pages 60–62) and N (pages 62–64) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out Theorems L.1 and L.2, Corollary L.3, Lemma M.1, Theorem M.3, Corollary M.4, Definition N.1, Lemma N.2, Theorem N.5 and Remark N.6, the one numbered statement of the paper without a Lean counterpart, each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

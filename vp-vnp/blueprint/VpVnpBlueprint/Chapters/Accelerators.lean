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

#doc (Manual) "Accelerators and the diagonal argument" =>

%%%
tag := "chapter-accelerators"
file := "accelerators"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendix K (pages 55–59) and Section N.3 (pages 63–64) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out Definition K.1, Lemmas K.2 to K.4, Proposition K.5, Theorems K.6 and K.7, and Proposition N.4, each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

The paper says (page 17) that the proof of Proposition N.4 can be verified only in the Lean development, and follows it with a formalization note that says so.

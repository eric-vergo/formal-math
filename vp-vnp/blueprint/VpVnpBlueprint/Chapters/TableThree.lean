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

#doc (Manual) "The paper's statements and their Lean names" =>

%%%
tag := "chapter-table3"
file := "lean-names"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendix Q of the paper (pages 66–70) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out Table 3, which names the Lean theorem of every numbered statement, and Section Q.3, which lists where the text and the Lean development differ, each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

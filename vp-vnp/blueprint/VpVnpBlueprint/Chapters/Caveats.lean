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

#doc (Manual) "What a reader should keep in mind" =>

%%%
tag := "chapter-caveats"
file := "caveats"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow the paper's own statements on what is and is not checked (Section 3, page 11; page 17; Section Q.1, page 66; Section Q.3, pages 66–70) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out the conventions of the statement file that a reader should know, the places where the printed proof defers to Lean, and the Lean statements that are variants of the printed ones, each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

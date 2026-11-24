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

#doc (Manual) "Glossary" =>

%%%
tag := "chapter-glossary"
file := "glossary"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendix P of the paper (pages 65–66) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out the terms the paper coins or uses in a special sense, and the other words the Lean development uses for them (Section Q.3, page 66), each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

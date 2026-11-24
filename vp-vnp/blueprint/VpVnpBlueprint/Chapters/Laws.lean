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

#doc (Manual) "Rerouting laws and tree networks" =>

%%%
tag := "chapter-laws"
file := "laws"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendices G (pages 41–43) and H (pages 44–48) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out Definition G.1, Theorem G.2, Proposition H.1 and Theorem H.2, each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

The paper says (page 17) that the proof of Theorem H.2(d), (e) can be verified only in the Lean development, and follows the theorem with a formalization note that says so.

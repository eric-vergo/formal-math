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

#doc (Manual) "Programs, automata and cutting" =>

%%%
tag := "chapter-programs"
file := "programs"
htmlSplit := .never
number := false
%%%

This chapter is not written yet. It will follow Appendices I (pages 48–51) and J (pages 51–55) ({repoFile "vp-vnp/paper.pdf"}[`paper.pdf`]) and set out the program model and tape automata, Proposition I.1, Lemma I.2, Definition J.1, Proposition J.2, and Theorems J.3 and J.4, each
beside its Lean declaration. Until it is written, the Lean declarations of this part of the proof appear, without informal statements, in the part {ref "part-generated"}[The Lean development, declaration by declaration].

The paper says (page 17) that the proofs of Proposition I.1 and Theorem J.3 can be verified only in the Lean development, and follows each of them with a formalization note that says so.

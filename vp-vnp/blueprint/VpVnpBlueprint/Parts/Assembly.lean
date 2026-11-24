/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Chapters.Assembly

open Verso.Genre Manual
open Informal

#doc (Manual) "The main theorems" =>

%%%
tag := "part-assembly"
%%%

{blueprint_part}

:::group "part-assembly"
The main theorems
:::

The main theorems over the real numbers, over every field, and for approximating circuits (Appendices L to N of the paper). In the paper's words (page 17): “Appendices A to K prove the lower bound for the permanent over the real numbers, and Appendix L assembles it. Appendix M passes to all fields and to the Hamiltonian cycle polynomial, and Appendix N to approximate computation.”

{include 0 VpVnpBlueprint.Chapters.Assembly}


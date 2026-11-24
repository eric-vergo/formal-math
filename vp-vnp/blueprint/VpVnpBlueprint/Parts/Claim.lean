/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Chapters.Claim
import VpVnpBlueprint.Chapters.Statement
import VpVnpBlueprint.Chapters.Checking

open Verso.Genre Manual
open Informal

#doc (Manual) "The claim" =>

%%%
tag := "part-claim"
%%%

{blueprint_part}

:::group "part-claim"
The claim
:::

What the paper and its formalization claim, the file that states it, and how to check it.

{include 0 VpVnpBlueprint.Chapters.Claim}

{include 0 VpVnpBlueprint.Chapters.Statement}

{include 0 VpVnpBlueprint.Chapters.Checking}

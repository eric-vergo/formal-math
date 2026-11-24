/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VpVnpBlueprint.Chapters.SpectralPoints
import VpVnpBlueprint.Chapters.Curvature
import VpVnpBlueprint.Chapters.Dichotomy

open Verso.Genre Manual
open Informal

#doc (Manual) "The common part" =>

%%%
tag := "part-common"
%%%

{blueprint_part}

:::group "part-common"
The common part
:::

The tools that both cases use: tensors, spectral points and prices, the inequality for two crossing wires, nonpositive curvature, and the theorem that one of the two cases holds (Appendices A to D and O of the paper).

{include 0 VpVnpBlueprint.Chapters.SpectralPoints}

{include 0 VpVnpBlueprint.Chapters.Curvature}

{include 0 VpVnpBlueprint.Chapters.Dichotomy}


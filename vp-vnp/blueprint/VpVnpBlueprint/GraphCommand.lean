/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph

/-!
# The dependency graph, opened on its group view

`{vpvnp_graph}` is `{blueprint_graph}` with the group view shown first: the development has
thousands of declarations, and the view of the groups (one per part of the paper and one per Lean
library) is the readable entry point. It takes the same arguments as `{blueprint_graph}`; every
other view stays one click away in the page's view selector.
-/

namespace VpVnpBlueprint

open Lean Elab
open Verso Doc Elab
open Informal Informal.Commands Informal.Graph Informal.Environment

open PartElabM in
/-- `{vpvnp_graph}`: the project's dependency graph, opened on the group view. -/
@[part_command Lean.Doc.Parser.Block.command]
def groupGraph : PartCommand
  | .command v => do
    unless v.name.getId == `vpvnp_graph do Lean.Elab.throwUnsupportedSyntax
    let stx : Syntax := v.stx
    let cfg ← Verso.ArgParse.parseThe BlueprintGraphConfig (← parseArgs v.args)
    let options ← parseGraphOptions cfg
    let previewMode ← parseGraphPreviewMode cfg
    let previewPlacement ← parseGraphPreviewPlacement cfg
    let endPos := stx.getTailPos?.get!
    closePartsUntil 1 endPos
    let expandedTitle := #[← ``(Verso.Doc.Inline.text "Dependency Graph")]
    let metadata : Option (TSyntax `term) := some (← `(term| { number := false }))
    reportImportedConflicts
    let graphData : GraphBlockData :=
      { options, previewMode, previewPlacement, initialView := some groupVariantKey }
    let block ← serializedBlockTerm `Informal.Commands.Block.graph graphData
    addPart <| FinishedPart.mk stx stx expandedTitle "Dependency Graph" metadata #[block] #[]
      endPos
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end VpVnpBlueprint

/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint.PreviewManifest
import VpVnpBlueprint

/-!
Generator entry point for the blueprint site. `lake exe vbp build` finds this file and runs it;
see `blueprint/README.md`.
-/

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc VpVnpBlueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (sideBySide := true)
    (sidebar? := some { links := #[
      { label := "Repository folder",
        href := "https://github.com/eric-vergo/formal-math/tree/blueprint/vp-vnp" }] })

/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, GPT-6.2 (OpenAI)
-/
import Lean

open Lean

def decodeName (s : String) : Name :=
  s.splitOn "." |>.foldl Name.str .anonymous

def jsonName (n : Name) : Json := toJson n.toString

def declModule (env : Environment) (decl : Name) : Name :=
  match env.getModuleIdxFor? decl with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

structure Closure where
  names : Std.HashSet Name
  edgeCount : Nat
  maxFanout : Nat
  maxDistance : Nat

def closure (env : Environment) (roots : Array Name) : IO Closure := do
  let mut pending := roots.map (·, 0)
  let mut seen : Std.HashSet Name := .ofArray roots
  let mut edgeCount := 0
  let mut maxFanout := 0
  let mut maxDistance := 0
  let mut head := 0
  while head < pending.size do
    let (n, distance) := pending[head]!
    head := head + 1
    let some ci := env.find? n | throw (IO.userError s!"Missing constant {n}")
    maxDistance := max maxDistance distance
    let mut fanout := 0
    for dep in ci.getUsedConstantsAsSet do
      if dep != n then
        fanout := fanout + 1
        unless seen.contains dep do
          seen := seen.insert dep
          pending := pending.push (dep, distance + 1)
    edgeCount := edgeCount + fanout
    maxFanout := max maxFanout fanout
  return ⟨seen, edgeCount, maxFanout, maxDistance⟩

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let rootsFile :: moduleNames := args
    | throw (IO.userError "Expected a blueprint roots file followed by project module names")
  let modules := moduleNames.toArray.map decodeName
  let env ← importModules (modules.map fun m => { module := m }) {}
  let roots := #[`Solution.mainTheorem, `Solution.mainTheoremApprox, `Solution.separation,
    `Solution.separationClosure, `Solution.permanent_over_real]
  let mut rootData := #[]
  let mut graphMetrics := #[]
  for root in roots do
    let found ← closure env #[root]
    let names := found.names.toArray.qsort Name.quickLt
    let entries := names.map fun n => toJson (n.toString, (declModule env n).toString)
    rootData := rootData.push (root.toString, toJson entries)
    let stats := Json.mkObj [("edges", toJson found.edgeCount), ("maxFanout", toJson found.maxFanout),
      ("maxShortestDepth", toJson found.maxDistance)]
    graphMetrics := graphMetrics.push (root.toString, stats)
  let mut allLocal := #[]
  for m in modules do
    let some idx := env.getModuleIdx? m | throw (IO.userError s!"No imported module {m}")
    let names := env.header.moduleData[idx.toNat]!.constNames.qsort Name.quickLt
    allLocal := allLocal.push (m.toString, toJson (names.map jsonName))
  let names := (← IO.FS.readFile rootsFile).splitOn "\n"
  let blueprintRoots := names.toArray.filterMap fun text =>
    if text.isEmpty then none else some (decodeName text)
  let blueprintRoots := blueprintRoots.filter fun n => (env.find? n).isSome
  let blueprintClosure ← closure env blueprintRoots
  let localModules : Std.HashSet Name := .ofArray modules
  let locals := blueprintClosure.names.toArray.filter fun n => localModules.contains (declModule env n)
  IO.println (Json.mkObj [("exports", Json.mkObj rootData.toList),
    ("localDeclarations", Json.mkObj allLocal.toList),
    ("graphMetrics", Json.mkObj graphMetrics.toList),
    ("blueprintDeclaredRoots", toJson (blueprintRoots.qsort Name.quickLt |>.map jsonName)),
    ("blueprintProjectClosure", toJson (locals.qsort Name.quickLt |>.map jsonName))]).compress

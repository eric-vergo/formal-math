/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Eric Vergo, Claude (Anthropic)
-/
import Lean

/-!
# The generated part of the blueprint

Writes one Verso chapter module per Lean module of the development, with one blueprint node per
declaration that no written chapter associates yet (the theorems of `Nc` are listed by name instead;
see `listedOnly`). A generated node has no informal statement:
it shows the Lean declaration alone, and its edges in the dependency graph come from the Lean code
(`autoDeps`). Run from the folder `vp-vnp` after `lake build`:

    lake env lean --run blueprint/scripts/GenerateNodes.lean

It writes `blueprint/VpVnpBlueprint/Generated/` (ignored by git) and replaces what is there.

Which declarations: every constant of a module of the development that has a source range of
its own whose line names it, that is not private and not an internal detail, and that is not a
constructor, recursor, projection, matcher or other companion Lean generates. A declaration
named in `(lean := "...")` by a written chapter (any file of `blueprint/VpVnpBlueprint/` outside
`Generated/`) is left out, so each declaration appears once.
-/

open Lean

namespace GenerateNodes

/-- The libraries of the development, in the order the generated part lists them, with the title
of the chapter each one gets. -/
def libraries : List (String × String) :=
  [("Statement", "Statement and Solution"), ("Paper", "Library Paper"), ("Nc", "Library Nc"),
   ("NS1", "Library NS1"), ("Ov", "Library Ov")]

/-- Source files that are not modules of the development: the blueprint, its entry point, the
build folders, the scripts, and the Comparator challenge (which declares the solution's names
again, with `sorry`). -/
def skipDir (name : String) : Bool :=
  name.startsWith "." || name == "blueprint" || name == "scripts" || name == "_out"

partial def leanFiles (root : System.FilePath) (rel : List String) : IO (Array (List String)) := do
  let dir := rel.foldl (· / ·) root
  let mut out := #[]
  let entries ← dir.readDir
  for e in entries.qsort (·.fileName < ·.fileName) do
    let md ← e.path.metadata
    if md.type == .dir then
      unless skipDir e.fileName do
        out := out ++ (← leanFiles root (rel ++ [e.fileName]))
    else if e.fileName.endsWith ".lean" then
      out := out.push (rel ++ [(e.fileName.dropEnd 5).toString])
  return out

/-- The module name of a source path such as `["Nc", "Grp", "Basic"]`. -/
def modName (parts : List String) : Name := parts.foldl Name.str .anonymous

/-- Is this a module of the development? -/
def isDevModule (parts : List String) : Bool :=
  match parts with
  | ["BlueprintMain"] => false
  | ["Challenge"] => false
  | "Comparator" :: rest => rest.getLast? == some "Solution"
  | _ => true

/-- The library a module belongs to, for the chapter it goes into. -/
def libraryOf (parts : List String) : String :=
  match parts with
  | ["Statement"] | ["Solution"] => "Statement"
  | "Comparator" :: _ => "Statement"
  | lib :: _ :: _ => lib
  | [m] => m
  | [] => ""

/-- The names that written chapters associate, read from `(lean := "a, b")` in their source. -/
partial def writtenNames (dir : System.FilePath) : IO (Std.HashSet String) := do
  let mut acc : Std.HashSet String := {}
  for e in ← dir.readDir do
    let md ← e.path.metadata
    if md.type == .dir then
      unless e.fileName == "Generated" do
        for n in ← writtenNames e.path do acc := acc.insert n
    else if e.fileName.endsWith ".lean" then
      let text ← IO.FS.readFile e.path
      for piece in (text.splitOn "lean := \"").drop 1 do
        let inner := (piece.splitOn "\"").headD ""
        for n in inner.splitOn "," do
          let n := n.trimAscii.toString
          unless n.isEmpty do acc := acc.insert n
  return acc

/-- A string literal for a Verso directive argument. -/
def quote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

/-- A tag for a Verso part: letters, digits and hyphens. -/
def tagOf (s : String) : String :=
  "lean-" ++ String.ofList (s.toList.map fun c => if c.isAlphanum then c else '-')

/-- A declaration Lean generated rather than the author wrote. -/
def isCompanion (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  (ci matches .ctorInfo _) || (ci matches .recInfo _) || (ci matches .quotInfo _) || env.isProjectionFn n ||
    isAuxRecursor env n || isNoConfusion env n || Meta.isMatcherCore env n

structure Decl where
  name : Name
  isTheorem : Bool
  line : Nat
  column : Nat

def declsOf (env : Environment) (modIdx : Nat) (source : Array String) : Array Decl := Id.run do
  let mut out := #[]
  for n in env.header.moduleData[modIdx]!.constNames do
    let some ci := env.find? n | continue
    if n.isInternalDetail || isPrivateName n || isCompanion env n ci then continue
    let some ranges := declRangeExt.find? (level := .exported) env n
        <|> declRangeExt.find? (level := .server) env n | continue
    let sel := ranges.selectionRange.pos
    let lineText := source[sel.line - 1]?.getD ""
    let last := match n with
      | .str _ s => s
      | _ => ""
    -- a declaration written in the source names itself on its line; companions that attributes
    -- or commands add (`ext_iff`, `injEq`, instances of `deriving`) point at another name's line
    unless !last.isEmpty && (lineText.splitOn last).length > 1 do continue
    out := out.push { name := n, isTheorem := ci matches .thmInfo _, line := sel.line,
                      column := sel.column }
  return out.qsort fun a b => a.line < b.line || (a.line == b.line && a.column < b.column)

def header : String :=
  "/-\nGenerated by blueprint/scripts/GenerateNodes.lean; do not edit.\n" ++
  "Released under Apache 2.0 license as described in the file LICENSE.\n" ++
  "SPDX-License-Identifier: Apache-2.0\n-/\n"

def preamble : String :=
  "open Verso.Genre Manual\nopen Informal\n\n" ++
  "set_option verso.blueprint.numbering \"none\"\n" ++
  "set_option verso.blueprint.autoDeps true\n\n"

/-- Declarations listed by name, with a link to their source, instead of getting a node: the
theorems of the library `Nc`. A node costs about a quarter of a megabyte of site, and with a node for
each of the development's declarations the site would exceed the 1 GB that GitHub Pages publishes;
the theorems of `Nc` are the largest group of declarations that no other declaration's statement
needs. Their uses still give edges: `autoDeps` follows a declaration without a node to the
declarations with nodes that it uses. -/
def listedOnly (lib : String) (d : Decl) : Bool :=
  lib == "Nc" && d.isTheorem && !(`Paper).isPrefixOf d.name

def moduleFile (mod : Name) (lib group path : String) (decls : Array Decl) : String := Id.run do
  let nodes := decls.filter (!listedOnly lib ·)
  let listed := decls.filter (listedOnly lib ·)
  let mut s := header ++ "import VersoManual\nimport VersoBlueprint\nimport " ++ mod.toString ++
    "\n\n" ++ preamble ++
    "#doc (Manual) " ++ quote mod.toString ++ " =>\n\n%%%\ntag := " ++
    quote (tagOf mod.toString) ++ "\nnumber := false\n%%%\n\n" ++
    s!"Generated from the Lean code; no informal statement yet. The declarations of the module \
      `{mod}`, in source order.\n\n"
  unless nodes.isEmpty do
    s := s ++ s!":::group {quote group}\n{mod}\n:::\n\n"
  for d in nodes do
    let kind := if d.isTheorem then "theorem" else "definition"
    let n := d.name.toString
    s := s ++ s!":::{kind} {quote n} (lean := {quote n}) (parent := {quote group})\n:::\n\n"
  unless listed.isEmpty do
    s := s ++ "The theorems of this module, listed by name with a link to their source (they \
      have no node of their own, to keep the site within the size GitHub Pages publishes):\n\n"
    for d in listed do
      s := s ++ s!"* `{d.name}` ({"{"}repoFile {quote s!"vp-vnp/{path}#L{d.line}"}}[source])\n"
    s := s ++ "\n"
  return s

def chapterFile (lib title : String) (mods : Array Name) : String := Id.run do
  let mut s := header ++ "import VersoManual\nimport VersoBlueprint\n"
  for m in mods do
    s := s ++ "import VpVnpBlueprint.Generated." ++ m.toString ++ "\n"
  s := s ++ "\n" ++ preamble ++ "#doc (Manual) " ++ quote title ++ " =>\n\n%%%\ntag := " ++
    quote (tagOf lib) ++ "\nnumber := false\n%%%\n\n" ++
    "Generated from the Lean code; no informal statement yet. One section per module, each \
      declaration with its Lean source; the edges of the dependency graph between these nodes \
      are read from the Lean code, within each module.\n\n"
  for m in mods do
    s := s ++ "{include 1 VpVnpBlueprint.Generated." ++ m.toString ++ "}\n\n"
  return s

def partFile (chapters : Array (String × String)) : String := Id.run do
  let mut s := header ++ "import VersoManual\nimport VersoBlueprint\n"
  for (lib, _) in chapters do
    s := s ++ "import VpVnpBlueprint.Generated." ++ lib ++ "Library\n"
  s := s ++ "\nopen Verso.Genre Manual\nopen Informal\n\n" ++
    "#doc (Manual) \"The Lean development, declaration by declaration\" =>\n\n%%%\n" ++
    "tag := \"part-generated\"\n%%%\n\n{blueprint_part}\n\n" ++
    "The chapters of this part are generated from the Lean code. They hold every declaration \
      of the development that the chapters above do not yet discuss, each with its Lean source \
      and no informal statement, so that the dependency graph covers the whole development. \
      A declaration that a chapter above discusses is shown there instead. Private \
      declarations, and the companions Lean generates itself (constructors, recursors, \
      projections, equation lemmas), are not listed. The theorems of the library `Nc`, except \
      those named `Paper.…`, are listed by name with a link to their source instead of getting a \
      node of their own: with a node for every declaration the site would exceed the size that \
      GitHub Pages publishes. A declaration without a node still contributes the edges of what it \
      uses. Between generated nodes the graph has the edges within each module only: with the \
      edges between modules as well, the site generator's check of each node's dependencies does \
      not finish. The written chapters' nodes have their edges to the generated nodes of every \
      module.\n\n"
  for (lib, _) in chapters do
    s := s ++ "{include 0 VpVnpBlueprint.Generated." ++ lib ++ "Library}\n"
  return s

def write (path : System.FilePath) (text : String) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path text

end GenerateNodes

open GenerateNodes in
def main : IO UInt32 := do
  let root : System.FilePath := "."
  let out : System.FilePath := "blueprint" / "VpVnpBlueprint" / "Generated"
  let files := (← leanFiles root []).filter isDevModule
  let built ← files.filterM fun parts =>
    (root / ".lake" / "build" / "lib" / "lean" / (String.intercalate "/" parts ++ ".olean")).pathExists
  if built.size < files.size then
    IO.eprintln s!"{files.size - built.size} modules are not built; run `lake build` first"
    return 1
  initSearchPath (← findSysroot)
  let env ← importModules (built.map fun p => { module := modName p }) {} (loadExts := false)
  let written ← writtenNames ("blueprint" / "VpVnpBlueprint")
  if ← out.pathExists then IO.FS.removeDirAll out
  let mut declsOfMod : Std.HashMap Name (Array Decl) := {}
  for parts in built do
    let mod := modName parts
    let some idx := env.getModuleIdx? mod | continue
    let src ← IO.FS.readFile (String.intercalate "/" parts ++ ".lean")
    let decls := (declsOf env idx.toNat (src.splitOn "\n").toArray).filter fun d =>
      !written.contains (d.name.toString)
    unless decls.isEmpty do declsOfMod := declsOfMod.insert mod decls
  let mut chapters : Array (String × String) := #[]
  let mut total := 0
  let mut listedTotal := 0
  for (lib, title) in libraries do
    let mut mods := #[]
    for parts in built.filter (libraryOf · == lib) do
      let mod := modName parts
      let some decls := declsOfMod[mod]? | continue
      total := total + decls.size
      listedTotal := listedTotal + (decls.filter (listedOnly lib ·)).size
      write (out / (String.intercalate "/" parts ++ ".lean")) (moduleFile mod lib
        ("group-" ++ tagOf mod.toString) (String.intercalate "/" parts ++ ".lean") decls)
      mods := mods.push mod
    unless mods.isEmpty do
      write (out / (lib ++ "Library.lean")) (chapterFile lib title mods)
      chapters := chapters.push (lib, title)
  write (out / "Part.lean") (partFile chapters)
  IO.println s!"{total} declarations ({total - listedTotal} nodes, {listedTotal} listed by name) \
    in {chapters.size} chapters, {written.size} names associated by written chapters"
  return 0

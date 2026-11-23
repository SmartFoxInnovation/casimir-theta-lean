import Lean
import ExportParse

open Lean

private def nameParts (json : Json) : Except String Name := do
  let segments ← json.getArr?
  segments.foldlM (init := .anonymous) fun parent segment =>
    match segment with
    | .str part => pure (.str parent part)
    | number => .num parent <$> number.getNat?

private def readBaseNames (path : String) : IO NameSet := do
  IO.FS.withFile path .read fun source => do
    let mut names : NameSet := {}
    repeat
      let line ← source.getLine
      if line.isEmpty then break
      let name ← IO.ofExcept (Json.parse line >>= nameParts)
      names := names.insert name
    return names

private def dottedName (text : String) : Name :=
  (text.splitOn ".").foldl Name.str .anonymous

private def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Materialize a candidate import from recorded proof terms.
    This step does not certify declarations. Each candidate requires a separate leanchecker pass. -/
def main (args : List String) : IO Unit := do
  let [path, output, name, parents, basePath] := args
    | throw <| IO.userError "Usage: PackPublishedTerms slice output module parents base-names"
  let base ← readBaseNames basePath
  let exported ← IO.FS.withFile path .read fun handle => Export.parseStream (.ofHandle handle)
  let mut constants := #[]
  for name in exported.constOrder do
    unless base.contains name do
      let some ci := exported.constMap[name]?
        | throw <| IO.userError s!"Missing exported constant {name}"
      if ci.isUnsafe || ci.isPartial then
        throw <| IO.userError s!"Unsafe or partial declaration {name}"
      if let .axiomInfo _ := ci then
        unless allowed.contains name do
          throw <| IO.userError s!"Unexpected axiom {name}"
      constants := constants.push ci
  if constants.isEmpty then
    throw <| IO.userError "Candidate module contains no new declarations"
  let imports : Array Import := (parents.splitOn ",").toArray.map fun parent =>
    { module := dottedName parent }
  saveModuleData output (dottedName name) {
    isModule := false
    imports
    constNames := constants.map (·.name)
    constants
    extraConstNames := #[]
    entries := #[]
  }
  IO.println s!"Packed {constants.size} candidate declarations for independent kernel replay"

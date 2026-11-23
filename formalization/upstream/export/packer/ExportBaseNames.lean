import Lean

open Lean

private def nameParts : Name → Array Json → Array Json
  | .anonymous, parts => parts
  | .str parent value, parts => nameParts parent (parts.push (.str value))
  | .num parent value, parts => nameParts parent (parts.push (toJson value))

unsafe def main (args : List String) : IO Unit := do
  let output :: baseNames := args
    | throw <| IO.userError "Usage: ExportBaseNames names.ndjson [module ...]"
  initSearchPath (← findSysroot)
  let imports : Array Import := baseNames.toArray.map fun name =>
    { module := name.toName }
  let env ← importModules imports {} 0
  let names := env.constants.fold (fun acc name _ => acc.push name) (#[] : Array Name)
  IO.FS.withFile output .write fun handle => do
    for name in names do
      handle.putStrLn <| Json.compress <| .arr (nameParts name #[]).reverse
  IO.println s!"Listed {names.size} exact declarations available from {baseNames}"

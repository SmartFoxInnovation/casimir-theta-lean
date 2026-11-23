import Lean

/-! Proof-term checks used by the optional publication entry point. -/

namespace RH01.PublicationAudit

open Lean Elab Command

private def standardAxioms : NameSet :=
  .ofList [`propext, `Classical.choice, `Quot.sound]

def checkStandardAxioms (theoremName : Name) : CommandElabM Unit := do
  let used ← collectAxioms theoremName
  unless used.all standardAxioms.contains && used.size == 3 do
    throwError "{theoremName} has axiom set {used.toList}"

/-- Inspect types and stored proof terms of the declarations reached from the root. -/
def checkDependencies (theoremName : Name) (required excluded : List Name) :
    CommandElabM Unit := do
  let env ← getEnv
  let excluded := NameSet.ofList excluded
  let mut seen : Std.HashSet Name := {}
  let mut stack := #[theoremName]
  while let some name := stack.back? do
    stack := stack.pop
    unless seen.contains name do
      if excluded.contains name then
        throwError "{theoremName} depends on {name}"
      seen := seen.insert name
      let some declaration := env.find? name
        | throwError "Missing declaration in proof of {theoremName}: {name}"
      for dep in declaration.getUsedConstantsAsSet do
        unless seen.contains dep do
          stack := stack.push dep
  let missing := required.filter fun name => !seen.contains name
  unless missing.isEmpty do
    throwError "{theoremName} is missing the expected proof dependencies {missing}"
  logInfo m!"{theoremName} uses the expected proof route ({seen.size} declarations checked)"

end RH01.PublicationAudit

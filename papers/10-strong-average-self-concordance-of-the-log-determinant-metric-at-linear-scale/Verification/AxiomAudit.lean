import Paper10
import Verification.Solution
import Lean

/-!
Transitive axiom closure of all public production declarations and Comparator solutions.
Challenge placeholders and negative controls are deliberately not imported.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := env.constants.toList.filter (fun (name, _) =>
    name.getRoot == `Paper10)
  let traversal : Lean.CollectAxioms.M Unit := do
    for (name, _) in roots do
      Lean.CollectAxioms.collect name
  let (_, closure) := (traversal.run env).run {}
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let illegal := closure.axioms.filter (fun a => !allowed.contains a)
  unless illegal.isEmpty do
    throwError "Illegal transitive axiom closure: {illegal}"
  logInfo m!"AXIOM_AUDIT_OK: {roots.length} production/solution declarations; axioms = {closure.axioms}"

import Paper09
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Traverse actual kernel types and proof values from every production root.
The visited cache is shared across roots, so shared mathlib dependencies are
traversed once. Negative-control modules are never imported. -/
run_cmd do
  let env ← getEnv
  let roots := env.constants.toList.filter (fun p => (`Paper09).isPrefixOf p.1)
  if roots.isEmpty then throwError "Empty production audit"
  let action : Lean.CollectAxioms.M Unit := do
    for (name, _) in roots do
      Lean.CollectAxioms.collect name
  let (_, state) := (action.run env).run {}
  let forbidden := state.axioms.filter (fun n =>
    n != `propext && n != `Classical.choice && n != `Quot.sound)
  unless forbidden.isEmpty do
    throwError "Illegal transitive production axioms: {forbidden}"
  for (name, _) in roots do
    logInfo m!"AXIOM_AUDIT_ROOT {name}"
  logInfo m!"AXIOM_AUDIT_OK roots={roots.length}; visited={state.visited.size}; union={state.axioms}"

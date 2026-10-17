import Paper28
import Lean.Util.CollectAxioms

/-! Audit all production constants, including definitions, generated instances,
and helper declarations, with a shared traversal of transitive dependencies.
The challenge and malicious controls are deliberately outside this import closure. -/
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let roots := env.constants.toList.filter (fun p => (`Paper28).isPrefixOf p.1)
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

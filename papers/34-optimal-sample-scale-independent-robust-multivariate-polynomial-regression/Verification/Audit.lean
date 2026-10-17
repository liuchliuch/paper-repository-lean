import Paper34
import Verification.Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- A read-only environment audit. Production proof declarations and definitions,
including private declarations under the production module path, are checked
against Lean's checked kernel environment. Negative controls and challenge
placeholders are deliberately not imported. -/
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, _) in env.constants.toList do
    let s := name.toString
    if s.startsWith "Paper34." || s.startsWith "_private.Paper34." ||
        s.startsWith "Verification." then
      unless (env.checked.get.find? name).isSome do
        throwError "Declaration missing from checked kernel environment: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Illegal production axiom: {name} depends on {ax}"
      logInfo m!"AXIOM_AUDIT {name}: {axioms.toList}"
      count := count+1
  logInfo m!"AXIOM_AUDIT_COMPLETE declarations={count} permitted=[propext, Classical.choice, Quot.sound]"

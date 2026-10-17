import Paper37
import Verification.Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Prepared only. Running this whole-production audit is verification_deferred_by_user. -/
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, _) in env.constants.toList do
    let s := name.toString
    if s.startsWith "Paper37." || s.startsWith "_private.Paper37." || s.startsWith "Verification." then
      unless (env.checked.get.find? name).isSome do
        throwError "Declaration missing from checked kernel environment: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Illegal production axiom: {name} depends on {ax}"
      logInfo m!"AXIOM_AUDIT {name}: {axioms.toList}"
      count := count+1
  logInfo m!"AXIOM_AUDIT_COMPLETE declarations={count} permitted=[propext, Classical.choice, Quot.sound]"

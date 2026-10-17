import Paper17
import Verification.FullSolution
import Lean

/-!
# Axiom audit of the paper-facing contract model and production `Paper17.*`

Transitive axiom closure of all `P17Contract` declarations and of every
`Paper17` declaration present in the environment.  Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted.  Challenge placeholders
and negative controls are deliberately not imported.

The audit imports all additional source contracts, both literal metrics, the
full geometric example and Appendix A. Any unpermitted axiom in their full
dependency closures makes this gate fail.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots := env.constants.toList.filterMap fun (name, _) =>
    if (`P17Contract).isPrefixOf name then some name
    else if (`Paper17).isPrefixOf name then some name
    else none
  let (_, closure) := ((roots.forM Lean.CollectAxioms.collect).run env).run {}
  for ax in closure.axioms do
    unless permitted.contains ax do
      throwError "Illegal axiom in the production/contract dependency closure: {ax}"
  logInfo m!"P17 declarations audited: {roots.length}."
  logInfo m!"Full transitive axiom union: {closure.axioms}."
  logInfo "All audited declarations have only permitted transitive axioms."

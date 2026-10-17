import K44K35Free
import Lean.Util.CollectAxioms

/-! Kernel dependency audit of every declaration in the production namespace.
This inspects transitive proof dependencies, not the spelling of source files. -/
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if (`K44K35Free).isPrefixOf name then
      count := count + 1
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Illegal transitive axiom {ax} in production declaration {name}"
  logInfo m!"TRANSITIVE_AXIOM_AUDIT_OK: {count} production declarations; allowed = {allowed}"

#print axioms K44K35Free.theorem_1
#print axioms K44K35Free.theorem_1_theta
#print axioms K44K35Free.lemma_2
#print axioms K44K35Free.lemma_3_projective
#print axioms K44K35Free.proposition_4
#print axioms K44K35Free.remark_5
#print axioms K44K35Free.lemma_6
#print axioms K44K35Free.lemma_7
#print axioms K44K35Free.lemma_8
#print axioms K44K35Free.proposition_9
#print axioms K44K35Free.proposition_10
#print axioms K44K35Free.preliminary_lower_bound
#print axioms K44K35Free.designated_copies_le_graph_copies

import SemidegreeExt
import Lean

open Lean Elab Command

/- Audit every declaration in the production namespace, including definitions
and auxiliary results, against its complete transitive axiom closure. -/
run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if `SemidegreeExt |>.isPrefixOf name then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless permitted.contains ax do
          throwError "Illegal transitive axiom {ax} in {name}"
      count := count + 1
  logInfo m!"Production declarations audited: {count}; all transitive axioms are permitted."

#print axioms SemidegreeExt.prop_2_1
#print axioms SemidegreeExt.exists_unit_placement
#print axioms SemidegreeExt.cut_condition
#print axioms SemidegreeExt.nested_placement
#print axioms SemidegreeExt.extremal_construction
#print axioms SemidegreeExt.theorem_1_1
#print axioms SemidegreeExt.qMin_eq_C
#print axioms SemidegreeExt.C_closed_form
#print axioms SemidegreeExt.lemma_3_1
#print axioms SemidegreeExt.corollary_1_2
#print axioms SemidegreeExt.q_le_iff_weaklyDegenerate
#print axioms SemidegreeExt.hAlpha_small_expansion
#print axioms SemidegreeExt.hAlpha_high_expansion

#print axioms SemidegreeExt.extraction_subdigraph_iff_induced
#print axioms SemidegreeExt.q_le_iff_all_subdigraphs
#print axioms SemidegreeExt.FlowAlgorithm.run_correct
#print axioms SemidegreeExt.FlowAlgorithm.runCost_bound
#print axioms SemidegreeExt.FlowAlgorithm.metered_correct
#print axioms SemidegreeExt.ConstructionAlgorithm.polynomial_construction
#print axioms SemidegreeExt.ConstructionAlgorithm.uniform_polynomial_time
#print axioms SemidegreeExt.ConstructionAlgorithm.intermediate_integer_bound

#print axioms SemidegreeExt.ConstructionAlgorithm.full_construction_correct
#print axioms SemidegreeExt.ConstructionAlgorithm.fullSolve_polynomial_time

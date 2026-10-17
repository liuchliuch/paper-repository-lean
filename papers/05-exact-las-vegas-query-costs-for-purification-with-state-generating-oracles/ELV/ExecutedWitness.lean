import ELV.ReflectionWitness
import ELV.BitFlip

/-! Actual complete query trajectories as unrestricted adversary witnesses. -/
noncomputable section
namespace ELV.Costs.Realization
open ELV.Model ELV.Query ELV.Stabilize ELV.Costs
variable {gap : Gap} {n : ℕ} [NeZero n]

abbrev AllControls (T : Realization gap n) := Fin T.circuit.length × T.Control

def executedWitness (T : Realization gap n) (O : promisedFamily n gap.δ) :
    OracleQuerySpace n T.AllControls := timeStack
      (Query.trace (bidirectional T.Control O.val) T.circuit
        (WithLp.toLp 2 (publicBasis 0,T.catalyst O)))

lemma executedWitness_cost (T : Realization gap n) (O : promisedFamily n gap.δ) :
    T.pointwiseCost O = ENNReal.ofReal (‖T.executedWitness O‖^2) := by
  change ENNReal.ofReal (Query.cost _ _ _) = _
  congr 1
  exact (timeStack_norm_sq _).symm

lemma executedWitness_feasible (T : Realization gap n) : Query.Witness
    (fun O : promisedFamily n gap.δ => bidirectional T.AllControls O.val)
    (fun _ => publicBasis 0) (fun O => publicBasis (label gap.δ O)) T.executedWitness := by
  intro O O'
  have hh := Query.adversary_identity T.circuit
    (fun O : promisedFamily n gap.δ => bidirectional T.Control O.val)
    (fun _ => publicBasis 0) (fun O => publicBasis (label gap.δ O)) T.catalyst T.exact O O'
  rw [executedWitness,executedWitness,bidirectional_timeStack,bidirectional_timeStack,
    timeStack_inner,timeStack_inner,← Finset.sum_sub_distrib]
  exact hh

end ELV.Costs.Realization

import ELV.FourWitness
import ELV.UnrestrictedUpper

/-! The unrestricted operational minimax equality, with a lower bound on
all real finite query circuits and attained separable upper construction. -/
noncomputable section
namespace ELV.Costs
open ELV.Stabilize ELV.Query ELV.Model ELV.FourOracles ELV.AdversaryFour
variable {n : ℕ} [NeZero n]

theorem unrestricted_realization_lower (gap : Gap) (R : Realization gap n) :
    ENNReal.ofReal (1/(2*gap.δ)) ≤ R.uniformCost := by
  by_cases ht : R.uniformCost=⊤
  · simp [ht]
  apply (ENNReal.ofReal_le_iff_le_toReal ht).2
  have hv (c ε : Bool) : ‖R.executedWitness (input gap n c ε)‖^2 ≤ R.uniformCost.toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal ht).mp
    rw [← R.executedWitness_cost]
    exact le_iSup (fun O => R.pointwiseCost O) _
  have he (ε η : Bool) : (1 : ℂ) =
      inner ℂ (R.executedWitness (input gap n false ε)) (R.executedWitness (input gap n true η)) -
      inner ℂ (signed (bidirectional R.AllControls (oracle gap n false false)) ε
        (R.executedWitness (input gap n false ε)))
        (signed (bidirectional R.AllControls (oracle gap n true false)) η
        (R.executedWitness (input gap n true η))) := by
    have hh := R.executedWitness_feasible (input gap n false ε) (input gap n true η)
    rw [public_gram_difference,instance_label,instance_label] at hh
    norm_num at hh
    rw [← query_sign gap R.AllControls false ε,← query_sign gap R.AllControls true η]
    exact hh
  have hb := four_witness_bound
    (bidirectional R.AllControls (oracle gap n false false))
    (bidirectional R.AllControls (oracle gap n true false)) gap.mu (2*gap.δ)
    (by linarith [gap.δ_pos]) (by nlinarith [gap.mu_sq]) (query_relative gap R.AllControls)
    (fun ε => R.executedWitness (input gap n false ε))
    (fun ε => R.executedWitness (input gap n true ε)) he
  apply four_oracle_lower gap
  have hsum := add_le_add (add_le_add (hv false false) (hv false true))
    (add_le_add (hv true false) (hv true true))
  have hd : 0 ≤ 2*gap.δ := by linarith [gap.δ_pos]
  nlinarith [mul_le_mul_of_nonneg_left hsum hd]

theorem unrestricted_lower (gap : Gap) :
    ENNReal.ofReal (1/(2*gap.δ)) ≤ C_sg gap n := by
  apply le_sInf
  rintro c ⟨R,rfl⟩
  exact unrestricted_realization_lower gap R

/-- Equation (1.1) for the actual full-oracle operational infimum. -/
theorem unrestricted_optimum (gap : Gap) :
    C_sg gap n = ENNReal.ofReal (1/(2*gap.δ)) :=
  le_antisymm (Unrestricted.upper gap n) (unrestricted_lower gap)

/-- One fixed actual circuit attains the infimum, with separable private space. -/
theorem unrestricted_attained_separable (gap : Gap) :
    ∃ R : Realization gap n, R.uniformCost=C_sg gap n ∧
      TopologicalSpace.SeparableSpace R.Private := by
  refine ⟨Unrestricted.realization gap n,?_,Unrestricted.private_separable n⟩
  rw [unrestricted_optimum]
  exact le_antisymm (Unrestricted.uniform_cost_le gap n)
    (unrestricted_realization_lower gap _)

end ELV.Costs

import Paper37.RiskBounds

/-!
# Exact historywise boundary minimax value

This module uses the source probability-kernel criteria, rather than restricting
private randomization to a finite set of seeds or deterministic outputs.
-/
noncomputable section
open scoped ENNReal
open MeasureTheory Paper37.Renewal

namespace Paper37.Prediction

/-- Proposition A.2, including all privately randomized prediction kernels and
all finite-mean stationary renewal laws. The proof uses deterministic-period
models only for the lower bound. -/
theorem historywiseMinimaxRisk_eq_log_two (n : ℕ) :
    historywiseMinimaxRisk n = ENNReal.ofReal (Real.log 2) := by
  apply le_antisymm (historywiseMinimaxRisk_le_log_two n)
  unfold historywiseMinimaxRisk
  apply le_iInf
  intro q
  have hr := Boundary.randomized_period_history_radius
    (q (List.replicate n false)).toMeasure (fun r : Set.Icc (0 : ℝ) 1 => r.val)
    measurable_subtype_coe (fun r => r.property)
  refine hr.trans ?_
  apply iSup_le
  intro k
  have h := Boundary.pointLaw_zero_history n k
  rw [← h.2]
  exact le_iSup_of_le (Boundary.pointLaw (n + k))
    (le_iSup (fun x : {x : List Bool // x.length = n ∧
      0 < blockMass (Boundary.pointLaw (n + k)) x} =>
        ∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl
          (conditional (Boundary.pointLaw (n + k)) x.val) r.val ∂(q x.val).toMeasure)
      ⟨List.replicate n false, by simp, h.1⟩)

end Paper37.Prediction

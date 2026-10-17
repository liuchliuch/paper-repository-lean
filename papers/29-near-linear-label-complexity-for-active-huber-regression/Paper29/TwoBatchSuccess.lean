import Paper29.TwoBatchOutput

noncomputable section
open scoped BigOperators Classical
namespace Paper29.ProcessTools

/-- Pilot-relative radius is exactly the baseline of its true residual. -/
theorem baseline_pilotResidual {n d m₀ : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b π₀ : Fin n → ℝ) (hp₀ : ∀ i, 0 ≤ π₀ i) (μ : Fin m₀ → Fin n) :
    baseline (pilotResidual A b π₀ hp₀ μ) = objective A b (pilotCenter A b π₀ hp₀ μ) := rfl

/-- The actual two-batch output succeeds on the two good events, including the
zero-radius branch and the minimum-norm main solve. -/
theorem twoBatch_good_implies_success {n d m₀ m : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (b π₀ π : Fin n → ℝ)
    (hp₀ : ∀ i, 0 ≤ π₀ i) (hp : ∀ i, 0 ≤ π i)
    (μ : Fin m₀ → Fin n) (ν : Fin m → Fin n) (xstar : Fin d → ℝ)
    (hopt : ∀ x, objective A b xstar ≤ objective A b x)
    {C₀ η ε : ℝ} (hC : 0 < C₀) (hε : 0 ≤ ε) (hη : η < 8)
    (hηdef : η = (2*ε+ε^2)/(2*C₀))
    (hpilot : objective A b (pilotCenter A b π₀ hp₀ μ) ≤ C₀*objective A b xstar)
    (hmain : baseline (pilotResidual A b π₀ hp₀ μ) = 0 ∨
      CenteredTransferEvent A (pilotResidual A b π₀ hp₀ μ) π
        (16*baseline (pilotResidual A b π₀ hp₀ μ))
        (η*baseline (pilotResidual A b π₀ hp₀ μ)) ν) :
    ∀ x, Real.sqrt (objective A b (twoBatchOutput A b π₀ π hp₀ hp (μ,ν))) ≤
      (1+ε)*Real.sqrt (objective A b x) := by
  let yc := pilotCenter A b π₀ hp₀ μ
  let z := pilotResidual A b π₀ hp₀ μ
  have hR0 : 0 ≤ objective A b yc := Finset.sum_nonneg (fun i _ => huber_nonneg _)
  have hbound : Real.sqrt (objective A b (twoBatchOutput A b π₀ π hp₀ hp (μ,ν))) ≤
      (1+ε)*Real.sqrt (objective A b xstar) := by
    by_cases hzero : objective A b yc = 0
    · have hz : z = 0 := by
        funext i
        exact Localization.residual_zero_of_objective_zero A b yc hzero i
      have hout : twoBatchOutput A b π₀ π hp₀ hp (μ,ν) = yc := by
        change yc + mainIncrement A z π hp ν = yc
        rw [hz, mainIncrement_zero, add_zero]
      rw [hout, hzero, Real.sqrt_zero]
      positivity
    · have hRpos : 0 < objective A b yc := lt_of_le_of_ne hR0 (Ne.symm hzero)
      have he : CenteredTransferEvent A z π (16*baseline z) (η*baseline z) ν := by
        rcases hmain with hh | hh
        · exact False.elim (hzero hh)
        · exact hh
      have hloc := centeredEvent_localization_bridge A z π ν η he
      have hh := (Localization.regression_relative_guarantee A b
        (Sampling.importanceWeights π ν) yc xstar (mainIncrement A z π hp ν)
        hRpos hη hC hε hηdef (Sampling.importanceWeights_nonneg π hp ν)
        hloc hopt (mainIncrement_minimizes A z π hp ν) hpilot).2
      exact hh
  intro x
  exact hbound.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hopt x)) (by linarith))

end Paper29.ProcessTools

import Paper09.LowerBound
import Paper09.UpperBound
import Paper09.Asymptotics

open Real Filter MeasureTheory
open scoped Topology
noncomputable section
namespace Paper09.RFIM

/-- The paper's real upper correction exponent agrees with the natural
surface exponent used by the geometric/time-scale construction. -/
lemma upper_correction_exponent {d : ℕ} (hd : 1 ≤ d) (x : ℝ) :
    x ^ ((d:ℝ)-1) = x ^ (d-1) := by
  have he : ((d-1:ℕ):ℝ) = (d:ℝ)-1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  rw [← he, Real.rpow_natCast]

/-- Passing from simultaneous minimum/maximum bounds to either actual time
preserves the vanishing failure probability. This is only event monotonicity. -/
lemma individual_bound_failure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (L U : ℕ → ℝ) (Y Z : ℕ → Ω → ℝ)
    (hgood : Tendsto (fun n => μ {ω | ¬(L n ≤ min (Y n ω) (Z n ω) ∧
        max (Y n ω) (Z n ω) ≤ U n)}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {ω | ¬(L n ≤ Y n ω ∧ Y n ω ≤ U n)}) atTop (𝓝 0) ∧
    Tendsto (fun n => μ {ω | ¬(L n ≤ Z n ω ∧ Z n ω ≤ U n)}) atTop (𝓝 0) := by
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgood
      (fun _ => zero_le _)
    intro n
    apply measure_mono
    intro ω hbad hbounds
    exact hbad ⟨hbounds.1.trans (min_le_left _ _), (le_max_left _ _).trans hbounds.2⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgood
      (fun _ => zero_le _)
    intro n
    apply measure_mono
    intro ω hbad hbounds
    exact hbad ⟨hbounds.1.trans (min_le_right _ _), (le_max_right _ _).trans hbounds.2⟩

/-- Combining the two proved probability events uses only a union bound;
the bounds are kept on the minimum and maximum of the actual times. -/
lemma simultaneous_bound_failure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (L U : ℕ → ℝ) (Y Z : ℕ → Ω → ℝ)
    (hlow : Tendsto (fun n => μ {ω | ¬ L n ≤ min (Y n ω) (Z n ω)}) atTop (𝓝 0))
    (hupper : Tendsto (fun n => μ {ω | ¬ max (Y n ω) (Z n ω) ≤ U n}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {ω | ¬(L n ≤ min (Y n ω) (Z n ω) ∧
      max (Y n ω) (Z n ω) ≤ U n)}) atTop (𝓝 0) := by
  exact failure_intersection_tendsto_zero μ
    (fun n => {ω | L n ≤ min (Y n ω) (Z n ω)})
    (fun n => {ω | max (Y n ω) (Z n ω) ≤ U n}) hlow hupper

/-- The simultaneous two-sided RFIM bounds (1.5). Both inputs are the
proved original propositions on the actual infinite Gaussian environment. -/
theorem theorem_1_3_bounds (d : ℕ) (β σ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 < σ) (hslow : SurfaceSlowPureBoxes d β)
    (hstrong : StrongGaussianDisorder d β σ) :
    ∃ c > 0, ∃ C > 0, Tendsto (fun n : ℕ => (environmentLaw d σ)
      {h | ¬(exp (c*(log (n:ℝ)/log (log (n:ℝ)))^exponentA d) ≤
          min (relaxationTime d n β h) (mixingTime d n β h) ∧
        max (relaxationTime d n β h) (mixingTime d n β h) ≤
          exp (C*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^((d:ℝ)-1)))}) atTop (𝓝 0) := by
  obtain ⟨c, hc, hlow⟩ := proposition_2_1 d β σ hd hβ hσ hslow
  obtain ⟨C, hC, hupper⟩ := proposition_3_1 d β σ hd hβ hσ hstrong
  refine ⟨c, hc, C, hC, ?_⟩
  have hupper' : Tendsto (fun n : ℕ => (environmentLaw d σ)
      {h | ¬ max (relaxationTime d n β h) (mixingTime d n β h) ≤
        exp (C*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^((d:ℝ)-1))}) atTop (𝓝 0) := by
    simpa only [upper_correction_exponent (by omega : 1 ≤ d)] using hupper
  exact simultaneous_bound_failure (environmentLaw d σ)
    (fun n => exp (c*(log (n:ℝ)/log (log (n:ℝ)))^exponentA d))
    (fun n => exp (C*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^((d:ℝ)-1)))
    (fun n h => relaxationTime d n β h) (fun n h => mixingTime d n β h) hlow hupper'

/-- The double-logarithmic limits (1.6), for both actual RFIM time notions.
The truncation at `e` is exactly the truncation in the original statement. -/
theorem theorem_1_3_limits (d : ℕ) (β σ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 < σ) (hslow : SurfaceSlowPureBoxes d β)
    (hstrong : StrongGaussianDisorder d β σ) :
    TendstoInMeasure (environmentLaw d σ)
      (fun (n : ℕ) h => griffithsStatistic n (relaxationTime d n β h)) atTop
      (fun _ => exponentA d) ∧
    TendstoInMeasure (environmentLaw d σ)
      (fun (n : ℕ) h => griffithsStatistic n (mixingTime d n β h)) atTop
      (fun _ => exponentA d) := by
  obtain ⟨c, hc, C, hC, hgood⟩ := theorem_1_3_bounds d β σ hd hβ hσ hslow hstrong
  obtain ⟨hrel, hmix⟩ := individual_bound_failure (environmentLaw d σ)
    (fun n => exp (c*(log (n:ℝ)/log (log (n:ℝ)))^exponentA d))
    (fun n => exp (C*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^((d:ℝ)-1)))
    (fun n h => relaxationTime d n β h) (fun n h => mixingTime d n β h) hgood
  exact ⟨griffithsStatistic_tendstoInMeasure_of_bounds (environmentLaw d σ)
      (fun n h => relaxationTime d n β h) hc hC (exponentA_pos hd) hrel,
    griffithsStatistic_tendstoInMeasure_of_bounds (environmentLaw d σ)
      (fun n h => mixingTime d n β h) hc hC (exponentA_pos hd) hmix⟩

/-- Theorem 1.3 in full: simultaneous two-sided bounds and both double-log
limits, with only Assumptions 1.1 and 1.2 and the fixed model parameters. -/
theorem theorem_1_3 (d : ℕ) (β σ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 < σ) (hslow : SurfaceSlowPureBoxes d β)
    (hstrong : StrongGaussianDisorder d β σ) :
    (∃ c > 0, ∃ C > 0, Tendsto (fun n : ℕ => (environmentLaw d σ)
      {h | ¬(exp (c*(log (n:ℝ)/log (log (n:ℝ)))^exponentA d) ≤
          min (relaxationTime d n β h) (mixingTime d n β h) ∧
        max (relaxationTime d n β h) (mixingTime d n β h) ≤
          exp (C*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^((d:ℝ)-1)))}) atTop (𝓝 0)) ∧
    TendstoInMeasure (environmentLaw d σ)
      (fun (n : ℕ) h => log (log (max (exp 1) (relaxationTime d n β h))) / log (log (n:ℝ)))
      atTop (fun _ => exponentA d) ∧
    TendstoInMeasure (environmentLaw d σ)
      (fun (n : ℕ) h => log (log (max (exp 1) (mixingTime d n β h))) / log (log (n:ℝ)))
      atTop (fun _ => exponentA d) := by
  refine ⟨theorem_1_3_bounds d β σ hd hβ hσ hslow hstrong, ?_⟩
  simpa only [griffithsStatistic] using theorem_1_3_limits d β σ hd hβ hσ hslow hstrong

end Paper09.RFIM

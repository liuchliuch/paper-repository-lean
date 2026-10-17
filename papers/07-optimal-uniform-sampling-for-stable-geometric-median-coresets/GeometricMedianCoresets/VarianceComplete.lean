import GeometricMedianCoresets.VarianceBound
import GeometricMedianCoresets.MainProbability
import GeometricMedianCoresets.FourFive

/-! Lemma 2.3 in its full stated range. -/
noncomputable section
open scoped BigOperators
namespace GeometricMedianCoresets
namespace FinitePopulation

/-- Equation (7), including singleton samples and full samples. -/
theorem variance_identity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n m : ℕ} (hn : 1 < n) (hm : 0 < m) (hmn : m ≤ n) (h : Fin n → H) :
    uniformAvg (m := m) (fun I => ‖sampleMean h I - popMean h‖ ^ 2) =
      ((n:ℝ) - m) / ((m:ℝ) * ((n:ℝ) - 1)) * ((1:ℝ) / n) *
        ∑ i, ‖h i - popMean h‖ ^ 2 := by
  by_cases hfull : m = n
  · subst m
    rw [variance_zero_of_eq (by omega) h]
    simp
  by_cases hone : m = 1
  · subst m
    rw [variance_one_sample (by omega) h]
    have hn1 : (n:ℝ) - 1 ≠ 0 := by
      have hnr : (1:ℝ) < n := by exact_mod_cast hn
      linarith
    simp [hn1]
  · exact variance_identity_m_ge_2 hn (by omega) (by omega) h

end FinitePopulation

/-- Equation (8), with OPT replaced by the cost of any chosen reference point. -/
theorem anchored_variance_bound {X : Type*} (S : SquaredMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (P : Dataset X n) (μ : X) :
    FinitePopulation.uniformAvg (m := m)
      (fun I => meanError (fun i => anchoredFeature S μ (P i)) I) ≤ S.toDist.cost P μ / m := by
  have hh := FinitePopulation.variance_le_raw_sq hn hm hmn
    (fun i => anchoredFeature S μ (P i))
  change FinitePopulation.uniformAvg _ ≤ _ at hh
  have heq : ((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖anchoredFeature S μ (P i)‖ ^ 2 =
      S.toDist.cost P μ / m := by
    calc _ = ((1:ℝ) / m) * (((1:ℝ) / n) * ∑ i, ‖anchoredFeature S μ (P i)‖ ^ 2) := by ring
      _ = _ := by rw [anchored_second_moment S hn P μ]; ring
  rwa [heq] at hh

end GeometricMedianCoresets

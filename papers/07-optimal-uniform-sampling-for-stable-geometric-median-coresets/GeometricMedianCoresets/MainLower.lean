import GeometricMedianCoresets.DistinctClusters
import GeometricMedianCoresets.UniformComparison

/-! Theorem 1.2(ii): the actual distinct one-dimensional lower bound. -/
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
namespace GeometricMedianCoresets.LowerBound

/-- For every permitted sample size there is a distinct real population with failure
probability at least `2/5`, under exactly the uniform law on its `m`-subsets. -/
theorem thm_1_2_ii {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/100) {m : ℕ} (hm : 0 < m)
    (hmsize : (m:ℝ) ≤ 1 / (24200 * ε ^ 2)) :
    ∃ (n : ℕ) (P : Dataset ℝ n), 0 < n ∧ m ≤ n ∧ Function.Injective P ∧
      ((((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => ¬ IsStableCoreset (normDist ℝ) P (indexedSample P I) ε (17 * ε))).card : ℝ) /
        (n.choose m : ℝ) ≥ 2/5 := by
  obtain ⟨n, mark, P, θ, hn, hmn, hlarge, hinj, hθlo, hθhi, hp, hpert⟩ :=
    exists_distinct_clusters hε hε' m
  have hθ : 0 ≤ θ := by linarith only [hθlo, hε]
  have hθ' : θ ≤ 1 := by linarith only [hθhi, hε']
  have hsq : θ ^ 2 ≤ 121 * ε ^ 2 := by
    have h := pow_le_pow_left₀ hθ hθhi 2
    nlinarith only [h]
  have hmR : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hmε : (m:ℝ) * ε ^ 2 ≤ 1/24200 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 24200 * ε ^ 2)).1 hmsize
    nlinarith only [hh]
  have hmθ : (m:ℝ) * θ ^ 2 ≤ 1/200 := by
    have hh := mul_le_mul_of_nonneg_left hsq hmR
    nlinarith only [hh, hmε]
  refine ⟨n, P, hn, hmn, hinj, ?_⟩
  apply (uniform_majority_2_5 hn hm hmn mark hθ hθ' hp hmθ hlarge).trans
  apply sample_fraction_mono
  intro I hI hmajority
  have hcard := (Finset.mem_powersetCard.1 hI).2
  apply majority_not_stable hn mark P hε hε' hθlo hp hpert I (by omega)
  simpa only [hcard] using hmajority

end GeometricMedianCoresets.LowerBound

import Paper35.RankBounds
import Paper35.CDFPower

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Paper35.RankBounds

lemma exists_gaussian_quantile {K : ℕ} (hK : 2 ≤ K) :
    ∃ b : ℝ, Φ b = 1-1/(K : ℝ) := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hp : (0 : ℝ) < K := by linarith
  apply CDFPower.exists_cdf_eq (gaussianReal 0 1)
  · exact sub_pos.mpr ((div_lt_one hp).mpr (by linarith))
  · linarith [one_div_pos.mpr hp]

/-- The normal quantile appearing in source (7.1); the source rank range
K≥2 guarantees its exact CDF equation. -/
def gaussianQuantile (K : ℕ) : ℝ :=
  if hK : 2 ≤ K then Classical.choose (exists_gaussian_quantile hK) else 0

lemma gaussianQuantile_spec {K : ℕ} (hK : 2 ≤ K) :
    Φ (gaussianQuantile K) = 1-1/(K : ℝ) := by
  rw [gaussianQuantile, dif_pos hK]
  exact Classical.choose_spec (exists_gaussian_quantile hK)

/-- Proposition 7.1, both finite-rank bounds at the actual source quantile.
The quantile existence and specialization introduce no external input. -/
theorem gaussianMaxMean_quantile_bounds (htail : TailIntegrationInput)
    (hstop : GaussianStopLossInput) (htangent : GaussianCDFTangentInput)
    {K : ℕ} (hK : 2 ≤ K) :
    gaussianQuantile K-Φ (gaussianQuantile K)^(K+1)/((K : ℝ)*φ (gaussianQuantile K)) ≤
      gaussianMaxMean K ∧ gaussianMaxMean K ≤ (K : ℝ)*φ (gaussianQuantile K) :=
  ⟨gaussianMaxMean_quantile_lower htail htangent hK _ (gaussianQuantile_spec hK),
    gaussianMaxMean_quantile_upper hstop hK _ (gaussianQuantile_spec hK)⟩

end Paper35.RankBounds

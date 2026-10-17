import Paper29.Geometry
import Paper29.AllScale
import Paper29.Majority
import Paper29.Surrogates
import Paper29.Specification
import Paper29.RateDistortion

/-! Wrappers for the independent frozen statement specification. -/
noncomputable section
namespace Paper29.Checked

 theorem lemma31 : Specification.Lemma31 := by
  refine ⟨huber_triangle, psi_sub_le, huber_increment, ?_⟩
  intro n w y z hw
  exact weightedHuber_triangle w y z hw

 theorem lemma38 : Specification.Lemma38 := by
  intro n d A w hn hw hsum hlocal
  exact AllScale.huber_all_scale_extension A w hn hw hsum hlocal

 theorem lemma41 : Specification.Lemma41 := by
  intro N γ hN hγ hγhi
  obtain ⟨hmin, hgap⟩ := Majority.lemma4_1 N γ hN hγ hγhi
  refine ⟨hmin, hgap, ?_, ?_⟩
  · intro t
    exact Majority.negative_global_minimizer N γ (by linarith) hγ hγhi t
  · intro t ht
    exact Majority.negative_exact_scalar_majority_gap N γ hN hγ hγhi t ht

 theorem lemma42 : Specification.Lemma42 := by
  intro r P hu herr
  exact RateDistortion.lemma4_2 P hu herr

 theorem proposition51 : Specification.Proposition51 := by
  intro N hN
  dsimp only
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNp : (0 : ℝ) < (N : ℝ) := by linarith
  have hls := Surrogates.leastSquares_unique_minimizer (N : ℝ) hNp
  have hl1 := Surrogates.absoluteLoss_unique_minimizer (N : ℝ) hNp
  refine ⟨hls.1, hls.2, Surrogates.leastSquaresHuber_minimizer (N : ℝ) hNr,
    ?_, Surrogates.leastSquaresHuber_optimum_value (N : ℝ) hNr,
    Surrogates.leastSquaresHuber_norm_ratio_bounds (N : ℝ) hNr,
    hl1.1, hl1.2, Surrogates.absoluteHuber_minimizer (N : ℝ) hNr,
    Surrogates.absoluteHuber_surrogate_value (N : ℝ),
    Surrogates.absoluteHuber_optimum_value (N : ℝ) hNr,
    Surrogates.absoluteHuber_norm_ratio_exact (N : ℝ) hNr,
    Surrogates.absoluteHuber_norm_ratio_bounds (N : ℝ) hNr⟩
  convert Surrogates.leastSquaresHuber_surrogate_value (N : ℝ) hNr using 1 <;> ring

end Paper29.Checked

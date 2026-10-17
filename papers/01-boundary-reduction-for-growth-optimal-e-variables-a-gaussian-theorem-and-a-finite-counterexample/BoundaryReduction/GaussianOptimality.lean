import BoundaryReduction.GaussianVariational
import Mathlib.MeasureTheory.Measure.Support

open Real Set MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]

lemma expectedLog_sub_le (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) (x y : Space d) :
    expectedLog K (W : Measure Γ) Z x-expectedLog K (W : Measure Γ) Z y ≤
      (R:ℝ)*‖K‖*‖x-y‖ := by
  have hx := integrable_phi_shift K (W : Measure Γ) Z R hR x
  have hy := integrable_phi_shift K (W : Measure Γ) Z R hR y
  have hpt : ∀ z : Space d, phi K (W : Measure Γ) (z+x)-phi K (W : Measure Γ) (z+y) ≤
      (R:ℝ)*‖K‖*‖x-y‖ := by
    intro z
    have h := phi_sub_le K (W : Measure Γ) R hR (z+x) (z+y)
    have heq : z+x-(z+y) = x-y := by abel
    rwa [heq] at h
  have hi := integral_mono (hx.sub hy) (integrable_const ((R:ℝ)*‖K‖*‖x-y‖)) hpt
  simp only [Pi.sub_apply] at hi
  have hs := integral_sub hx hy
  simp only [Pi.sub_apply] at hs
  rw [hs] at hi
  simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul, expectedLog] using hi

lemma lipschitz_expectedLog (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) :
    LipschitzWith (R*‖K‖₊) (expectedLog K (W : Measure Γ) Z) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_sub_le_iff.mpr
  exact ⟨expectedLog_sub_le K Z W R hR x y,
    by simpa only [norm_sub_rev] using expectedLog_sub_le K Z W R hR y x⟩

variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

/-- Equalization at every point of the prior's topological support. -/
theorem minimizer_support_equalization (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hmin : ∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V) :
    ∀ r ∈ (W : Measure Γ).support,
      expectedLog K (W : Measure Γ) Z (r : Space d) = mixtureEntropy K Z W := by
  have hb := boundary_condition_of_minimizer K Z hcenter hcov W R hR hK hmin
  have hi := integrable_expectedLog_prior K Z hcenter hcov W W R hR hK
  have havg := cross_as_prior_average K Z hcenter hcov W W R hR hK
  change (∫ r : Γ, expectedLog K (W : Measure Γ) Z (r : Space d) ∂(W : Measure Γ)) = mixtureEntropy K Z W at havg
  have hzero : (∫ r : Γ, expectedLog K (W : Measure Γ) Z (r : Space d)-mixtureEntropy K Z W ∂(W : Measure Γ)) = 0 := by
    rw [integral_sub hi (integrable_const _), havg]
    simp
  have hae := (integral_eq_zero_iff_of_nonneg (fun r => sub_nonneg.mpr (hb r))
    (hi.sub (integrable_const _))).mp hzero
  have hclosed : IsClosed {r : Γ | expectedLog K (W : Measure Γ) Z (r : Space d) = mixtureEntropy K Z W} :=
    isClosed_eq ((lipschitz_expectedLog K Z W R hR).continuous.comp continuous_subtype_val) continuous_const
  have hs := Measure.support_subset_of_isClosed hclosed
    (hae.mono (fun r hr => sub_eq_zero.mp hr))
  exact fun r hr => hs hr

noncomputable def boundaryMinimum (W : ProbabilityMeasure Γ) : ℝ :=
  sInf (Set.range (fun r : Γ => expectedLog K (W : Measure Γ) Z (r : Space d)))

lemma boundaryMinimum_le (hΓ : Γ.Nonempty) (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) (r : Γ) :
    boundaryMinimum K Z W ≤ expectedLog K (W : Measure Γ) Z (r : Space d) := by
  have hc : Continuous (fun r : Γ => expectedLog K (W : Measure Γ) Z (r : Space d)) :=
    (lipschitz_expectedLog K Z W R hR).continuous.comp continuous_subtype_val
  have hb : BddBelow (Set.range (fun r : Γ => expectedLog K (W : Measure Γ) Z (r : Space d))) :=
    by simpa only [Set.image_univ] using (isCompact_univ.image hc).bddBelow
  exact csInf_le hb ⟨r,rfl⟩

/-- The computable boundary minimum bounds the optimum value, giving (4.15). -/
theorem proposition_4_2_gap (hΓ : Γ.Nonempty) (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hmin : ∀ U : ProbabilityMeasure Γ, mixtureEntropy K Z V ≤ mixtureEntropy K Z U) :
    0 ≤ mixtureEntropy K Z W-mixtureEntropy K Z V ∧
      mixtureEntropy K Z W-mixtureEntropy K Z V ≤ mixtureEntropy K Z W-boundaryMinimum K Z W := by
  constructor
  · exact sub_nonneg.mpr (hmin W)
  · have hi := integral_mono (integrable_const (boundaryMinimum K Z W))
      (integrable_expectedLog_prior K Z hcenter hcov V W R hR hK)
      (boundaryMinimum_le K Z hcenter hcov hΓ W R hR)
    simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hi
    rw [cross_as_prior_average K Z hcenter hcov V W R hR hK] at hi
    have hu := cross_le_entropy K Z hcenter hcov V W R hR hK
    linarith

end BoundaryReduction.Gaussian

import BoundaryReduction.GaussianUniqueness

open Real Set MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

/-- The component likelihood density is the actual Gaussian shift law. -/
lemma component_measure_eq_shift (r : Γ) :
    Z.withDensity (fun x => ENNReal.ofReal (exp (exponent K r x))) =
      Z.map (fun x => x+(r : Space d)) := by
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  have hm := precision_mgf K Z hcenter hvar (r : Space d)
  simp only [mgf, one_mul] at hm
  rw [← gaussian_tilt_eq_shift K Z hcenter hcov]
  unfold Measure.tilted
  congr 1
  ext x
  rw [hm]
  simp only [exponent, precisionForm_apply, exp_sub]

/-- The constructed mixture is exactly the Borel mixture of Gaussian location laws. -/
theorem mixtureMeasure_apply (W : ProbabilityMeasure Γ) (s : Set (Space d)) (hs : MeasurableSet s) :
    mixtureMeasure K Z W s = ∫⁻ r : Γ, (Z.map (fun x => x+(r : Space d))) s ∂(W : Measure Γ) := by
  rw [mixtureMeasure, withDensity_apply _ hs]
  have heq (x : Space d) : ENNReal.ofReal (likelihood K (W : Measure Γ) x) =
      ∫⁻ r : Γ, ENNReal.ofReal (exp (exponent K r x)) ∂(W : Measure Γ) := by
    exact ofReal_integral_eq_lintegral_ofReal
      (by simpa using integrable_exp_shift K (W : Measure Γ) x 0)
      (Filter.Eventually.of_forall (fun r => (exp_pos _).le))
  simp_rw [heq]
  have hc : Continuous (fun p : Space d × Γ => exp (exponent K p.2 p.1)) := by
    unfold exponent
    fun_prop
  rw [lintegral_lintegral_swap (f := fun x : Space d => fun r : Γ => ENNReal.ofReal (exp (exponent K r x)))
    (μ := Z.restrict s) (ν := (W : Measure Γ)) hc.measurable.ennreal_ofReal.aemeasurable]
  congr 1
  ext r
  rw [← withDensity_apply _ hs, component_measure_eq_shift K Z hcenter hcov]

lemma entropy_min_iff_kl_min (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    (∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V) ↔
    (∀ V : ProbabilityMeasure Γ, klDiv (mixtureMeasure K Z W) Z ≤ klDiv (mixtureMeasure K Z V) Z) := by
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  constructor
  · intro h V
    rw [mixture_klDiv K Z hcenter hvar W R hR hK, mixture_klDiv K Z hcenter hvar V R hR hK]
    exact ENNReal.ofReal_le_ofReal (h V)
  · intro h V
    have hh := h V
    rw [mixture_klDiv K Z hcenter hvar W R hR hK, mixture_klDiv K Z hcenter hvar V R hR hK] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mixtureEntropy_nonneg K Z hcenter hvar V R hR hK)).mp hh

/-- The compact Borel KL minimizing prior is unique. -/
theorem exists_unique_kl_minimizer (hΓ : Γ.Nonempty)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    ∃! W : ProbabilityMeasure Γ,
      ∀ V : ProbabilityMeasure Γ, klDiv (mixtureMeasure K Z W) Z ≤ klDiv (mixtureMeasure K Z V) Z := by
  obtain ⟨W,hW,huniq⟩ := exists_unique_entropy_minimizer K Z hcenter hcov hΓ R hR hK
  refine ⟨W, (entropy_min_iff_kl_min K Z hcenter hcov W R hR hK).mp hW, ?_⟩
  intro V hV
  exact huniq V ((entropy_min_iff_kl_min K Z hcenter hcov V R hR hK).mpr hV)

end BoundaryReduction.Gaussian

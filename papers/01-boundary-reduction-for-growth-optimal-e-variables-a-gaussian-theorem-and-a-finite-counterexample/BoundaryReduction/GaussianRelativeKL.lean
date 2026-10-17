import BoundaryReduction.GaussianFiniteExterior
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

open Real Set MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

lemma mixture_mutual_ac (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) :
    mixtureMeasure K Z W ≪ Z ∧ Z ≪ mixtureMeasure K Z W := by
  have hm := (continuous_likelihood K (W : Measure Γ) R hR).measurable.ennreal_ofReal
  exact ⟨withDensity_absolutelyContinuous _ _, withDensity_absolutelyContinuous' hm.aemeasurable
    (Filter.Eventually.of_forall (fun x => (ENNReal.ofReal_pos.mpr (likelihood_pos K (W : Measure Γ) x)).ne'))⟩

lemma relative_llr_eq (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) :
    llr (mixtureMeasure K Z V) (mixtureMeasure K Z W) =ᵐ[Z]
      fun x => phi K (V : Measure Γ) x-phi K (W : Measure Γ) x := by
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  letI := mixture_isProbability K Z hcenter hvar V
  letI := mixture_isProbability K Z hcenter hvar W
  have hmV := (continuous_likelihood K (V : Measure Γ) R hR).measurable.ennreal_ofReal
  have hmW := (continuous_likelihood K (W : Measure Γ) R hR).measurable.ennreal_ofReal
  have hV := Measure.rnDeriv_withDensity Z hmV
  have hW := Measure.rnDeriv_withDensity_right (mixtureMeasure K Z V) Z hmW.aemeasurable
    (Filter.Eventually.of_forall (fun x => (ENNReal.ofReal_pos.mpr (likelihood_pos K (W : Measure Γ) x)).ne'))
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_ne_top))
  filter_upwards [hV,hW] with x hxV hxW
  unfold llr
  change log (((mixtureMeasure K Z V).rnDeriv (Z.withDensity _) x).toReal) = _
  rw [hxW]
  change (Z.withDensity _).rnDeriv Z x = _ at hxV
  simp only [mixtureMeasure] at hxV ⊢
  rw [hxV, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (likelihood_pos K (W : Measure Γ) x).le,
    ENNReal.toReal_ofReal (likelihood_pos K (V : Measure Γ) x).le]
  rw [log_mul (inv_ne_zero (likelihood_pos K (W : Measure Γ) x).ne') (likelihood_pos K (V : Measure Γ) x).ne', log_inv]
  unfold phi
  ring

lemma integrable_phi_under_mixture (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    Integrable (phi K (W : Measure Γ)) (mixtureMeasure K Z V) := by
  have hm := (continuous_likelihood K (V : Measure Γ) R hR).measurable.ennreal_ofReal
  apply (integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (likelihood_pos K (V : Measure Γ) _).le, smul_eq_mul] using
    integrable_cross K Z V W R hR hK

lemma integral_phi_under_mixture (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) :
    (∫ x, phi K (W : Measure Γ) x ∂mixtureMeasure K Z V) =
      ∫ x, likelihood K (V : Measure Γ) x*phi K (W : Measure Γ) x ∂Z := by
  have hm := (continuous_likelihood K (V : Measure Γ) R hR).measurable.ennreal_ofReal
  rw [mixtureMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (likelihood_pos K (V : Measure Γ) _).le, smul_eq_mul]

/-- The actual finite relative KL identity between two Borel Gaussian mixtures. -/
theorem relative_klDiv (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    klDiv (mixtureMeasure K Z V) (mixtureMeasure K Z W) =
      ENNReal.ofReal (mixtureEntropy K Z V-
        ∫ x, likelihood K (V : Measure Γ) x*phi K (W : Measure Γ) x ∂Z) := by
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  letI := mixture_isProbability K Z hcenter hvar V
  letI := mixture_isProbability K Z hcenter hvar W
  have hacV := (mixture_mutual_ac K Z hcenter hcov V R hR).1
  have hacW := (mixture_mutual_ac K Z hcenter hcov W R hR).2
  have heq : llr (mixtureMeasure K Z V) (mixtureMeasure K Z W) =ᵐ[mixtureMeasure K Z V]
      fun x => phi K (V : Measure Γ) x-phi K (W : Measure Γ) x :=
    hacV.ae_le (relative_llr_eq K Z hcenter hcov V W R hR)
  have hV := integrable_phi_under_mixture K Z hcenter hcov V V R hR hK
  have hW := integrable_phi_under_mixture K Z hcenter hcov V W R hR hK
  have hllr : Integrable (llr (mixtureMeasure K Z V) (mixtureMeasure K Z W)) (mixtureMeasure K Z V) :=
    (hV.sub hW).congr (Filter.EventuallyEq.symm heq)
  rw [klDiv_of_ac_of_integrable (hacV.trans hacW) hllr, integral_congr_ae heq]
  have hs := integral_sub hV hW
  simp only [Pi.sub_apply] at hs
  rw [hs, integral_phi_under_mixture K Z hcenter hcov V V R hR,
    integral_phi_under_mixture K Z hcenter hcov V W R hR]
  simp only [measureReal_univ_eq_one, add_sub_cancel_right, mixtureEntropy]

/-- Pythagorean identity (4.17) with all terms finite and the actual KL divergence. -/
theorem mixture_pythagorean (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    mixtureEntropy K Z V = (klDiv (mixtureMeasure K Z V) (mixtureMeasure K Z W)).toReal+
      ∫ r : Γ, expectedLog K (W : Measure Γ) Z (r : Space d) ∂(V : Measure Γ) := by
  rw [relative_klDiv K Z hcenter hcov V W R hR hK,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (cross_le_entropy K Z hcenter hcov V W R hR hK)),
    cross_as_prior_average K Z hcenter hcov V W R hR hK]
  ring

end BoundaryReduction.Gaussian

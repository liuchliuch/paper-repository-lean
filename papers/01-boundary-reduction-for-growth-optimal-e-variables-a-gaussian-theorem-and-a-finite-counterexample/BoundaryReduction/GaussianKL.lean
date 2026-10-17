import BoundaryReduction.GaussianMinimizer
import Mathlib.InformationTheory.KullbackLeibler.Basic

open Real Set MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]

/-- The actual mixture measure, with its likelihood ratio relative to the null Gaussian. -/
noncomputable def mixtureMeasure (W : ProbabilityMeasure Γ) : Measure (Space d) :=
  Z.withDensity (fun x => ENNReal.ofReal (likelihood K (W : Measure Γ) x))

variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hvariance : ∀ v : Space d, variance (precisionForm K v) Z = inner ℝ v (K v))
include hcenter hvariance

lemma mixture_isProbability (W : ProbabilityMeasure Γ) : IsProbabilityMeasure (mixtureMeasure K Z W) := by
  constructor
  rw [mixtureMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_likelihood K Z hcenter hvariance (W : Measure Γ))
      (Filter.Eventually.of_forall (fun x => (likelihood_pos K (W : Measure Γ) x).le)),
    integral_likelihood K Z hcenter hvariance (W : Measure Γ)]
  norm_num

lemma mixture_klFun_integral (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    (∫ x, klFun (likelihood K (W : Measure Γ) x) ∂Z) = mixtureEntropy K Z W := by
  have hE := integrable_entropy K Z (W : Measure Γ) R hR hK
  have hL := integrable_likelihood K Z hcenter hvariance (W : Measure Γ)
  simp only [klFun, phi] at hE ⊢
  have hs := integral_sub (hE.add (integrable_const 1)) hL
  have ha := integral_add hE (integrable_const 1)
  simp only [Pi.add_apply] at hs ha
  rw [hs, ha,
    integral_likelihood K Z hcenter hvariance (W : Measure Γ)]
  simp [mixtureEntropy, phi]

lemma mixtureEntropy_nonneg (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) : 0 ≤ mixtureEntropy K Z W := by
  rw [← mixture_klFun_integral K Z hcenter hvariance W R hR hK]
  exact integral_nonneg (fun x => klFun_nonneg (likelihood_pos K (W : Measure Γ) x).le)

/-- The entropy integral is the actual finite KL divergence of the mixture measure. -/
theorem mixture_klDiv (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    klDiv (mixtureMeasure K Z W) Z = ENNReal.ofReal (mixtureEntropy K Z W) := by
  letI := mixture_isProbability K Z hcenter hvariance W
  have hac : mixtureMeasure K Z W ≪ Z := withDensity_absolutelyContinuous _ _
  have hmeas : Measurable (fun x => ENNReal.ofReal (likelihood K (W : Measure Γ) x)) :=
    (continuous_likelihood K (W : Measure Γ) R hR).measurable.ennreal_ofReal
  have hrn := Measure.rnDeriv_withDensity Z hmeas
  have heq : (fun x => klFun (((mixtureMeasure K Z W).rnDeriv Z x).toReal)) =ᵐ[Z]
      fun x => klFun (likelihood K (W : Measure Γ) x) := by
    filter_upwards [hrn] with x hx
    simp only [mixtureMeasure]
    rw [hx, ENNReal.toReal_ofReal (likelihood_pos K (W : Measure Γ) x).le]
  have hint : Integrable (fun x => klFun (((mixtureMeasure K Z W).rnDeriv Z x).toReal)) Z := by
    have hE := integrable_entropy K Z (W : Measure Γ) R hR hK
    have hL := integrable_likelihood K Z hcenter hvariance (W : Measure Γ)
    exact (((hE.add (integrable_const 1)).sub hL).congr (by
      filter_upwards [heq] with x hx
      simpa only [klFun, phi] using hx.symm))
  have hllr := (integrable_klFun_rnDeriv_iff hac).mp hint
  rw [klDiv_eq_integral_klFun, if_pos ⟨hac,hllr⟩, integral_congr_ae heq,
    mixture_klFun_integral K Z hcenter hvariance W R hR hK]

/-- Finite value of the actual KL objective for every compact prior. -/
theorem mixture_klDiv_ne_top (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) : klDiv (mixtureMeasure K Z W) Z ≠ ∞ := by
  rw [mixture_klDiv K Z hcenter hvariance W R hR hK]
  exact ENNReal.ofReal_ne_top

/-- A compact family has an actual Borel KL minimizer, not a minimizer supplied as data. -/
theorem exists_kl_minimizer (hΓ : Γ.Nonempty)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    ∃ W : ProbabilityMeasure Γ, ∀ V : ProbabilityMeasure Γ,
      klDiv (mixtureMeasure K Z W) Z ≤ klDiv (mixtureMeasure K Z V) Z := by
  obtain ⟨W,hW⟩ := exists_entropy_minimizer K Z hΓ R hR hK
  refine ⟨W, ?_⟩
  intro V
  rw [mixture_klDiv K Z hcenter hvariance W R hR hK,
    mixture_klDiv K Z hcenter hvariance V R hR hK]
  exact ENNReal.ofReal_le_ofReal (hW V)

/-- Borel KL minimizer existence on the full boundary in the Gaussian precision model. -/
theorem exists_boundary_kl_minimizer {B : Set (Space d)} (hd : 1 ≤ d)
    (hB : IsOpen B) (h0 : (0 : Space d) ∈ B) (hb : Bornology.IsBounded B) :
    ∃ W : ProbabilityMeasure (frontier B), ∀ V : ProbabilityMeasure (frontier B),
      klDiv (mixtureMeasure K Z W) Z ≤ klDiv (mixtureMeasure K Z V) Z := by
  have hc := compact_nonempty_boundary hd hB h0 hb
  letI : CompactSpace (frontier B) := isCompact_iff_compactSpace.mp hc.1
  obtain ⟨R,hRpos,hR⟩ := hc.1.isBounded.exists_pos_norm_le
  have hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v) := by
    intro v
    rw [← hvariance]
    exact variance_nonneg _ _
  exact exists_kl_minimizer K Z hcenter hvariance hc.2 ⟨R,hRpos.le⟩ (fun r => hR r r.2) hK

end BoundaryReduction.Gaussian

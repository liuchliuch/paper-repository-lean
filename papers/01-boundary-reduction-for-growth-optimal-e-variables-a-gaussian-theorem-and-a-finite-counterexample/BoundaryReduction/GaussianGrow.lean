import BoundaryReduction.MeasureInformation
import BoundaryReduction.GaussianPythagorean

open Real Set MeasureTheory ProbabilityTheory InformationTheory BigOperators
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ}

/-- Actual location laws in the Gaussian experiment. -/
noncomputable def locationLaw (Z : Measure (Space d)) (μ : Space d) : Measure (Space d) :=
  Z.map (fun x => x+μ)

instance (Z : Measure (Space d)) [IsProbabilityMeasure Z] (μ : Space d) :
    IsProbabilityMeasure (locationLaw Z μ) := Measure.isProbabilityMeasure_map (by fun_prop)

noncomputable def gaussianGrowth (Z : Measure (Space d)) (C : Set (Space d)) : EReal :=
  MeasureGrow.growth Z (fun μ : C => locationLaw Z (μ : Space d))

noncomputable def FinitePrior.toMeasureMixture {C : Set (Space d)}
    (Z : Measure (Space d)) (F : FinitePrior C) :
    MeasureGrow.FiniteMixture (fun μ : C => locationLaw Z (μ : Space d)) :=
  ⟨F.index,F.finite,F.weights,fun i => ⟨F.mean i,F.admissible i⟩⟩

variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

lemma finiteMixture_eq_sum {C : Set (Space d)} (F : FinitePrior C) :
    F.finiteMixture K Z = (F.toMeasureMixture Z).measure := by
  let D := Set.range F.mean
  letI : CompactSpace D := isCompact_iff_compactSpace.mp (Set.finite_range F.mean).isCompact
  have hD : ∀ i, F.mean i ∈ D := fun i => ⟨i,rfl⟩
  rw [← F.mixture_asPrior K Z hD]
  ext s hs
  rw [mixtureMeasure_apply K Z hcenter hcov _ s hs]
  simp only [FinitePrior.asPrior, ProbabilityMeasure.coe_mk,
    lintegral_finset_sum_measure, lintegral_smul_measure, lintegral_dirac,
    MeasureGrow.FiniteMixture.measure, Measure.finset_sum_apply,
    Measure.smul_apply, smul_eq_mul, FinitePrior.toMeasureMixture, locationLaw]

lemma finiteMixture_kl_ne_top {C : Set (Space d)} (F : FinitePrior C) :
    klDiv (F.finiteMixture K Z) Z ≠ ∞ := by
  let D := Set.range F.mean
  have hD := (Set.finite_range F.mean).isCompact
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  have hFD : ∀ i, F.mean i ∈ D := fun i => ⟨i,rfl⟩
  obtain ⟨R,hRpos,hR⟩ := hD.isBounded.exists_pos_norm_le
  let Rn : ℝ≥0 := ⟨R,hRpos.le⟩
  have hRn : ∀ r : D, ‖(r : Space d)‖ ≤ Rn := fun r => hR r r.2
  have hv := precision_variance_of_covariance K Z hcenter hcov
  have hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v) := fun v => by
    rw [← hv]; exact variance_nonneg _ _
  rw [← F.mixture_asPrior K Z hFD]
  exact mixture_klDiv_ne_top K Z hcenter hv (F.asPrior hFD) Rn hRn hK

lemma locationLaw_kl_ne_top (μ : Space d) : klDiv (locationLaw Z μ) Z ≠ ∞ := by
  let D := ({μ} : Set (Space d))
  letI : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_singleton : IsCompact D)
  let r : D := ⟨μ,Set.mem_singleton μ⟩
  have hv := precision_variance_of_covariance K Z hcenter hcov
  have hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v) := fun v => by
    rw [← hv]; exact variance_nonneg _ _
  have hm : mixtureMeasure K Z (pointPrior r) = locationLaw Z μ := by
    unfold mixtureMeasure
    simp only [likelihood_point]
    exact component_measure_eq_shift K Z hcenter hcov r
  rw [← hm]
  exact mixture_klDiv_ne_top K Z hcenter hv (pointPrior r) ‖μ‖₊
    (fun x => by have hx : (x : Space d) = μ := Set.mem_singleton_iff.mp x.2; simpa [hx]) hK

/-- GROW≤I for arbitrary mean sets in the Gaussian family, with all nonnegative
measurable e-variables and the convention log 0=-∞. -/
theorem gaussianGrowth_le_information (C : Set (Space d)) :
    gaussianGrowth Z C ≤ (↑(finiteInformation K Z C) : EReal) := by
  apply iSup_le
  intro S
  have hbound (F : FinitePrior C) :
      (⨅ μ : C, MeasureGrow.logExpectation (locationLaw Z (μ : Space d)) S.value) ≤
        (↑(klDiv (F.finiteMixture K Z) Z) : EReal) := by
    have hF := finiteMixture_kl_ne_top K Z hcenter hcov F
    rw [finiteMixture_eq_sum K Z hcenter hcov F] at hF ⊢
    exact MeasureGrow.worst_logExpectation_le_mixture S (F.toMeasureMixture Z)
      (fun μ => locationLaw_kl_ne_top K Z hcenter hcov μ) hF
  by_cases hx : (⨅ μ : C, MeasureGrow.logExpectation (locationLaw Z (μ : Space d)) S.value) ≤ 0
  · exact hx.trans (EReal.coe_ennreal_nonneg _)
  · have hxmem : (⨅ μ : C, MeasureGrow.logExpectation (locationLaw Z (μ : Space d)) S.value) ∈
        Set.range ((↑) : ℝ≥0∞ → EReal) := by
      rw [EReal.range_coe_ennreal]
      exact (lt_of_not_ge hx).le
    obtain ⟨a,ha⟩ := hxmem
    rw [← ha]
    apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    apply le_sInf
    rintro b ⟨F,rfl⟩
    have hb := hbound F
    rw [← ha] at hb
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mp hb

variable {Γ : Set (Space d)} [CompactSpace Γ]

/-- The boundary likelihood ratio is an actual normalized e-variable. -/
noncomputable def mixtureEVar (W : ProbabilityMeasure Γ) (R : ℝ≥0)
    (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) : MeasureEVar Z :=
  ⟨likelihood K (W : Measure Γ), (continuous_likelihood K (W : Measure Γ) R hR).measurable,
    fun x => (likelihood_pos K (W : Measure Γ) x).le,
    integrable_likelihood K Z hcenter (precision_variance_of_covariance K Z hcenter hcov) (W : Measure Γ),
    (integral_likelihood K Z hcenter (precision_variance_of_covariance K Z hcenter hcov) (W : Measure Γ)).le⟩

lemma logExpectation_mixture (W : ProbabilityMeasure Γ) (R : ℝ≥0)
    (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) (μ : Space d) :
    MeasureGrow.logExpectation (locationLaw Z μ) (likelihood K (W : Measure Γ)) =
      (↑(expectedLog K (W : Measure Γ) Z μ) : EReal) := by
  have hi : Integrable (phi K (W : Measure Γ)) (locationLaw Z μ) := by
    apply (integrable_map_measure
      ((continuous_likelihood K (W : Measure Γ) R hR).log
        (fun x => (likelihood_pos K (W : Measure Γ) x).ne')).aestronglyMeasurable
      (by fun_prop)).mpr
    exact integrable_phi_shift K (W : Measure Γ) Z R hR μ
  rw [MeasureGrow.logExpectation_eq_integral
    (Filter.Eventually.of_forall (fun x => (likelihood_pos K (W : Measure Γ) x).ne')) hi]
  congr 1
  exact integral_map (by fun_prop)
    ((continuous_likelihood K (W : Measure Γ) R hR).log
      (fun x => (likelihood_pos K (W : Measure Γ) x).ne')).aestronglyMeasurable

/-- The GROW equality and attainment portion of Theorem 4.1. -/
theorem theorem_4_1_growth {B : Set (Space d)} [CompactSpace (frontier B)]
    (hB : IsOpen B) (h0 : (0 : Space d) ∈ B) (hΓ : (frontier B).Nonempty)
    (W : ProbabilityMeasure (frontier B)) (R : ℝ≥0)
    (hR : ∀ r : frontier B, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hmin : ∀ V : ProbabilityMeasure (frontier B), mixtureEntropy K Z W ≤ mixtureEntropy K Z V) :
    gaussianGrowth Z Bᶜ = (↑(mixtureEntropy K Z W) : EReal) ∧
      (⨅ μ : ↥(Bᶜ), MeasureGrow.logExpectation (locationLaw Z (μ : Space d))
        (mixtureEVar K Z hcenter hcov W R hR).value) = (↑(mixtureEntropy K Z W) : EReal) := by
  have hinf := (theorem_4_1_information K Z hcenter hcov hB h0 hΓ W R hR hK hmin).1
  have hnonneg := mixtureEntropy_nonneg K Z hcenter (precision_variance_of_covariance K Z hcenter hcov) W R hR hK
  have hupper := gaussianGrowth_le_information K Z hcenter hcov Bᶜ
  rw [hinf, EReal.coe_ennreal_ofReal, max_eq_left hnonneg] at hupper
  have hlower : (↑(mixtureEntropy K Z W) : EReal) ≤
      (⨅ μ : ↥(Bᶜ), MeasureGrow.logExpectation (locationLaw Z (μ : Space d))
        (mixtureEVar K Z hcenter hcov W R hR).value) := by
    apply le_iInf
    intro μ
    change (↑(mixtureEntropy K Z W) : EReal) ≤
      MeasureGrow.logExpectation (locationLaw Z (μ : Space d)) (likelihood K (W : Measure (frontier B)))
    rw [logExpectation_mixture K Z hcenter hcov W R hR]
    exact_mod_cast minimizer_exterior_inequality K Z hcenter hcov hB h0 W R hR hmin μ μ.2
  have hmid : (⨅ μ : ↥(Bᶜ), MeasureGrow.logExpectation (locationLaw Z (μ : Space d))
      (mixtureEVar K Z hcenter hcov W R hR).value) ≤ gaussianGrowth Z Bᶜ := by
    exact le_iSup (fun S : MeasureEVar Z => ⨅ μ : ↥(Bᶜ),
      MeasureGrow.logExpectation (locationLaw Z (μ : Space d)) S.value)
      (mixtureEVar K Z hcenter hcov W R hR)
  exact ⟨le_antisymm hupper (hlower.trans hmid), le_antisymm (hmid.trans hupper) hlower⟩

end BoundaryReduction.Gaussian

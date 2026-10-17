import Paper26.GeneralPosteriorIdentity
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Probability form of the posterior information identity

The original outcome reference measure is arbitrary.  All measure reductions
use the common likelihood support already proved in `LikelihoodSupport`.
`LikelihoodRegularity` records exactly the likelihood hypotheses of
`GeneralPosteriorIdentity.lemma_3_2`; it contains no posterior, marginal-law,
normalization-of-posterior, or Fisher-identity conclusion.

The genuine marginal density defines an outcome measure of total mass equal
to the prior's mass.  Normalized priors therefore give a probability measure.
The Bayes posterior is normalized almost everywhere for that measure, and its
Fisher function is measurable there.  The final theorems express Lemma 3.2 as
an expectation with respect to this actual law, including the ordinary finite
real-valued expectation when the prior-averaged data information is finite.
-/
noncomputable section
open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Paper26.GeneralBayesNormalization
open H1PosteriorBound WeakPosteriorIdentity

variable {Y : Type*} [MeasurableSpace Y] {p : ℕ}

/-- Only the original experiment's regularity and normalization assumptions.
These are the explicit hypotheses of the proved arbitrary-reference-measure
identity, packaged to keep its probability corollaries readable. -/
structure LikelihoodRegularity (ν : Measure Y) (g : Y → ParameterSpace p → ℝ) where
  locallyLipschitz : ∀ᵐ y ∂ν, LocallyLipschitz (g y)
  sectionStronglyMeasurable : ∀ x, AEStronglyMeasurable (fun y => g y x) ν
  jointlyStronglyMeasurable :
    AEStronglyMeasurable (fun z : Y × ParameterSpace p => g z.1 z.2) (ν.prod volume)
  derivativeJointlyStronglyMeasurable :
    AEStronglyMeasurable (fun z : Y × ParameterSpace p => fderiv ℝ (g z.1) z.2)
      (ν.prod volume)
  normalized : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x ^ 2) ∂ν) = 1
  localSets : ℕ → Set (ParameterSpace p)
  localSets_measurable : ∀ n, MeasurableSet (localSets n)
  localSets_cover : ∀ x, ∃ n, x ∈ localSets n
  localEnergy_finite : ∀ n, (∫⁻ x in localSets n,
    (∫⁻ y, ‖fderiv ℝ (g y) x‖ₑ ^ (2 : ℕ) ∂ν)) ≠ ∞
  integral_hasFDerivAt : ∀ᵐ x ∂(volume : Measure (ParameterSpace p)),
    HasFDerivAt (fun t => ∫ y, g y t ^ 2 ∂ν)
      (∫ y, (2 * g y x) • fderiv ℝ (g y) x ∂ν) x

/-- The actual outcome law: its density is the actual prior-likelihood
marginal, without changing the original reference measure. -/
def outcomeLaw (ν : Measure Y) (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) :
    Measure Y := ν.withDensity (marginal h g)

theorem marginal_measurable (ν : Measure Y) (h : WeakH1Root p)
    (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g) :
    AEMeasurable (marginal h g) ν :=
  marginal_aemeasurable ν h g
    (jointDensity_aemeasurable ν h g R.jointlyStronglyMeasurable)

/-- Tonelli is used only after the common s-finite support reduction.  The
prior need not yet be normalized. -/
theorem marginal_integral_eq_mass (ν : Measure Y) (h : WeakH1Root p)
    (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g) :
    (∫⁻ y, marginal h g y ∂ν) = h.mass univ := by
  have hi (x : ParameterSpace p) : Integrable (fun y => g y x ^ 2) ν :=
    (memLp_two_of_lintegral_sq_ne_top ν (R.sectionStronglyMeasurable x)
      (by rw [R.normalized x]; simp)).integrable_sq
  obtain ⟨S, hS, hsf, hz⟩ := LikelihoodSupport.continuous_likelihood_support g
    (R.locallyLipschitz.mono fun _ hy => hy.continuous) hi
  let νS := ν.restrict S
  letI : SFinite νS := hsf
  have hprod : νS.prod (volume : Measure (ParameterSpace p)) ≤ ν.prod volume := by
    apply Measure.le_iff.2
    intro T hT
    rw [Measure.prod_apply hT, Measure.prod_apply hT]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have hn (x : ParameterSpace p) : (∫⁻ y, ENNReal.ofReal (g y x ^ 2) ∂νS) = 1 := by
    calc
      _ = ∫⁻ y, ENNReal.ofReal (g y x ^ 2) ∂ν := by
        apply GeneralPosteriorIdentity.lintegral_restrict_eq_of_zero hS
        filter_upwards [hz] with y hy hnot
        rw [hy hnot]
        simp
      _ = 1 := R.normalized x
  have hm : (∫⁻ y, marginal h g y ∂νS) = h.mass univ := by
    unfold marginal
    rw [lintegral_lintegral_swap (jointDensity_aemeasurable νS h g
      (R.jointlyStronglyMeasurable.mono_measure hprod))]
    have he (x : ParameterSpace p) :
        (∫⁻ y, ENNReal.ofReal ((h.root x * g y x) ^ 2) ∂νS) =
          ENNReal.ofReal (h.root x ^ 2) := by
      simp only [mul_pow, ENNReal.ofReal_mul (sq_nonneg (h.root x))]
      have hgm : AEMeasurable (fun y => ENNReal.ofReal (g y x ^ 2)) νS :=
        ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          ((R.sectionStronglyMeasurable x).aemeasurable.restrict.pow_const 2)
      rw [lintegral_const_mul'' _ hgm, hn x, mul_one]
    simp_rw [he]
    simp only [WeakH1Root.mass, Measure.restrict_univ]
  have he : (∫⁻ y, marginal h g y ∂νS) = ∫⁻ y, marginal h g y ∂ν := by
    apply GeneralPosteriorIdentity.lintegral_restrict_eq_of_zero hS
    filter_upwards [hz] with y hy hnot
    simp [marginal, hy hnot]
  exact he.symm.trans hm

theorem outcomeLaw_univ (ν : Measure Y) (h : WeakH1Root p)
    (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g) :
    outcomeLaw ν h g univ = h.mass univ := by
  rw [outcomeLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact marginal_integral_eq_mass ν h g R

/-- The actual marginal measure is a probability measure for a normalized
prior, even if the original reference measure is not s-finite. -/
theorem outcomeLaw_isProbabilityMeasure (ν : Measure Y) (h : WeakH1Root p)
    (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g)
    (hh : h.mass univ = 1) : IsProbabilityMeasure (outcomeLaw ν h g) :=
  ⟨(outcomeLaw_univ ν h g R).trans hh⟩

theorem marginal_finite_ae (ν : Measure Y) (h : WeakH1Root p)
    (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g) :
    ∀ᵐ y ∂ν, marginal h g y ≠ ∞ := by
  apply (ae_lt_top' (marginal_measurable ν h g R) ?_).mono (fun _ hy => hy.ne)
  rw [marginal_integral_eq_mass ν h g R]
  exact mass_univ_ne_top h

/-- Zero-marginal outcomes have zero actual outcome probability.  The
posterior at almost every observed outcome has mass one. -/
theorem posterior_normalized_ae (ν : Measure Y) (P : WeakLocallyLipschitzProductInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g) :
    ∀ᵐ y ∂outcomeLaw ν h g, (bayesPosterior P h g y).mass univ = 1 := by
  rw [outcomeLaw, ae_withDensity_iff' (marginal_measurable ν h g R)]
  filter_upwards [R.locallyLipschitz] with y hy hm
  exact bayesPosterior_normalized P h g hy hm

/-- The same almost-everywhere posterior is the genuine normalized Bayes
root, represented by a compactly supported weak H¹ object. -/
theorem posterior_root_ae (ν : Measure Y) (P : WeakLocallyLipschitzProductInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g) :
    ∀ᵐ y ∂outcomeLaw ν h g, ∀ x, (bayesPosterior P h g y).root x =
      (Real.sqrt (marginal h g y).toReal)⁻¹ * (h.root x * g y x) := by
  apply (withDensity_absolutelyContinuous ν (marginal h g)).ae_le
  exact R.locallyLipschitz.mono fun y hy x => bayesPosterior_root P h g hy x

/-- Weighted posterior information is already measurable.  Division by its
positive finite marginal gives measurability of posterior Fisher information
for the actual outcome law; zero marginals require no arbitrary quotient
convention in the conclusion. -/
theorem posterior_fisher_aemeasurable (ν : Measure Y)
    (P : WeakLocallyLipschitzProductInput p) (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g) :
    AEMeasurable (fun y => (bayesPosterior P h g y).fisher) (outcomeLaw ν h g) := by
  have hm := marginal_measurable ν h g R
  have hw := weightedPosteriorFisher_aemeasurable ν P U h g R.locallyLipschitz
    (weakProductDerivative_energy_aemeasurable ν h g R.jointlyStronglyMeasurable
      R.derivativeJointlyStronglyMeasurable)
  have hq := (hw.div hm).mono' (withDensity_absolutelyContinuous ν (marginal h g))
  apply hq.congr
  change ∀ᵐ y ∂ν.withDensity (marginal h g),
    marginal h g y * (bayesPosterior P h g y).fisher / marginal h g y =
      (bayesPosterior P h g y).fisher
  rw [ae_withDensity_iff' hm]
  filter_upwards [marginal_finite_ae ν h g R] with y hy hm0
  rw [mul_comm, ENNReal.mul_div_cancel_right hm0 hy]

/-- Lemma 3.2 as an actual nonnegative expectation under the genuine marginal
law.  No information identity occurs in `LikelihoodRegularity`. -/
theorem posterior_information_identity (ν : Measure Y)
    (P : WeakLocallyLipschitzProductInput p) (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g) :
    (∫⁻ y, (bayesPosterior P h g y).fisher ∂outcomeLaw ν h g) =
      h.fisher + dataInformation ν h g := by
  rw [outcomeLaw, lintegral_withDensity_eq_lintegral_mul₀'
    (marginal_measurable ν h g R) (posterior_fisher_aemeasurable ν P U h g R)]
  exact GeneralPosteriorIdentity.lemma_3_2 ν P U h g R.locallyLipschitz
    R.sectionStronglyMeasurable R.jointlyStronglyMeasurable
    R.derivativeJointlyStronglyMeasurable R.normalized R.localSets
    R.localSets_measurable R.localSets_cover R.localEnergy_finite R.integral_hasFDerivAt

theorem fisher_ne_top (h : WeakH1Root p) : h.fisher ≠ ∞ := by
  unfold WeakH1Root.fisher
  exact ENNReal.mul_ne_top (by norm_num) h.energy_ne_top

/-- Finiteness is a conclusion from the source's finite prior-averaged data
information assumption and the already proved expectation identity. -/
theorem posterior_fisher_integrable (ν : Measure Y)
    (P : WeakLocallyLipschitzProductInput p) (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g)
    (hdata : dataInformation ν h g ≠ ∞) :
    Integrable (fun y => (bayesPosterior P h g y).fisher.toReal) (outcomeLaw ν h g) := by
  apply integrable_toReal_of_lintegral_ne_top (posterior_fisher_aemeasurable ν P U h g R)
  rw [posterior_information_identity ν P U h g R]
  exact ENNReal.add_ne_top.2 ⟨fisher_ne_top h, hdata⟩

/-- The ordinary finite real-valued expectation form of Lemma 3.2. -/
theorem posterior_information_identity_real (ν : Measure Y)
    (P : WeakLocallyLipschitzProductInput p) (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g)
    (hdata : dataInformation ν h g ≠ ∞) :
    (∫ y, (bayesPosterior P h g y).fisher.toReal ∂outcomeLaw ν h g) =
      h.fisher.toReal + (dataInformation ν h g).toReal := by
  rw [integral_toReal (posterior_fisher_aemeasurable ν P U h g R)
    (Filter.Eventually.of_forall fun y => lt_top_iff_ne_top.mpr
      (fisher_ne_top (bayesPosterior P h g y)))]
  rw [posterior_information_identity ν P U h g R,
    ENNReal.toReal_add (fisher_ne_top h) hdata]

/-- The source's normalized-prior, finite-information probability
specialization.  The posterior supplied here is already a genuine compactly
supported weak H¹ root, not an assumed posterior-information object. -/
theorem lemma_3_2_probability (ν : Measure Y)
    (P : WeakLocallyLipschitzProductInput p) (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ) (R : LikelihoodRegularity ν g)
    (hh : h.mass univ = 1) (hdata : dataInformation ν h g ≠ ∞) :
    IsProbabilityMeasure (outcomeLaw ν h g) ∧
      (∀ᵐ y ∂outcomeLaw ν h g, (bayesPosterior P h g y).mass univ = 1) ∧
      Integrable (fun y => (bayesPosterior P h g y).fisher.toReal) (outcomeLaw ν h g) ∧
      (∫ y, (bayesPosterior P h g y).fisher.toReal ∂outcomeLaw ν h g) =
        h.fisher.toReal + (dataInformation ν h g).toReal :=
  ⟨outcomeLaw_isProbabilityMeasure ν h g R hh, posterior_normalized_ae ν P h g R,
    posterior_fisher_integrable ν P U h g R hdata,
    posterior_information_identity_real ν P U h g R hdata⟩

end Paper26.GeneralBayesNormalization

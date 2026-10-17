import Paper35.Gaussian
import Paper35.SourceModel
import Paper35.Crossing
import Paper35.Rank
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Paper35.GaussianMarked

/-- Canonical isotropic Gaussian vector law, including dimension zero. -/
def standardGaussian (m : ℕ) : Measure (Source.Space m) :=
  (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map (WithLp.toLp 2)

instance (m : ℕ) : IsProbabilityMeasure (standardGaussian m) := by
  unfold standardGaussian
  exact isProbabilityMeasure_map (WithLp.measurable_toLp 2 (Fin m → ℝ)).aemeasurable

/-- Standard Gaussian CDF, retaining the exact nonnegative probability value. -/
def normalCDF (y : ℝ) : ℝ≥0∞ := gaussianReal 0 1 (Iic y)

/-- The visibility mark averaged over the common pair value N(0,1/2). -/
def visibilityProbability (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y, normalCDF y ^ n ∂gaussianReal 0 (1/2)

/-- Random scalar common pair value and `n` independent remaining candidate scores. -/
def scalarMarkLaw (n : ℕ) : Measure (ℝ × (Fin n → ℝ)) :=
  (gaussianReal 0 (1/2)).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1))

def scalarVisible (n : ℕ) : Set (ℝ × (Fin n → ℝ)) := {z | ∀ k, z.2 k < z.1}

lemma measurableSet_scalarVisible (n : ℕ) : MeasurableSet (scalarVisible n) := by
  simp only [scalarVisible, setOf_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_lt ((measurable_pi_apply k).comp measurable_snd) measurable_fst

/-- Independence of the remaining scores gives precisely the CDF power. -/
theorem scalar_remaining_visibility (n : ℕ) (y : ℝ) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) {z | ∀ k, z k < y} =
      normalCDF y ^ n := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have heq : {z : Fin n → ℝ | ∀ k, z k < y} = Set.pi univ (fun _ => Iio y) := by
    ext z
    simp
  rw [heq, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  exact measure_congr Iio_ae_eq_Iic

/-- The averaged mark (6.6) is proved from actual independent scalar Gaussian laws. -/
theorem scalar_visibility_mass (n : ℕ) :
    scalarMarkLaw n (scalarVisible n) = visibilityProbability n := by
  unfold scalarMarkLaw visibilityProbability
  rw [Measure.prod_apply (measurableSet_scalarVisible n)]
  apply lintegral_congr
  intro y
  exact scalar_remaining_visibility n y

/-- A deterministic finite family of intersections with arbitrary dependent marks. -/
def markedCount {Ω : Type*} (S : Finset ℝ) (M : ℝ → Ω → Prop) (ω : Ω) : ℝ≥0∞ :=
  ∑ s ∈ S, {ω | M s ω}.indicator 1 ω

/-- This sum is the genuine cardinality of the marked subset of the parameter set. -/
theorem markedCount_eq_encard {Ω : Type*} (S : Finset ℝ) (M : ℝ → Ω → Prop) (ω : Ω) :
    markedCount S M ω = (({s | s ∈ S ∧ M s ω} : Set ℝ).encard : ℝ≥0∞) := by
  classical
  have heq : ({s | s ∈ S ∧ M s ω} : Set ℝ) = (↑(S.filter (fun s => M s ω)) : Set ℝ) := by
    ext s
    simp
  rw [heq, Set.encard_coe_eq_coe_finsetCard]
  change markedCount S M ω = ((S.filter (fun s => M s ω)).card : ℝ≥0∞)
  simp only [markedCount, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply,
    Finset.sum_boole]

/-- Finite marked Tonelli: the marks at different intersections need not be independent. -/
theorem lintegral_markedCount {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Finset ℝ) (M : ℝ → Ω → Prop)
    (hM : ∀ s ∈ S, MeasurableSet {ω | M s ω}) :
    (∫⁻ ω, markedCount S M ω ∂μ) = ∑ s ∈ S, μ {ω | M s ω} := by
  unfold markedCount
  rw [lintegral_finset_sum (f := fun s ω => {ω | M s ω}.indicator 1 ω) S
    (fun s hs => (measurable_one.indicator (hM s hs))) ]
  apply Finset.sum_congr rfl
  intro s hs
  exact lintegral_indicator_one (hM s hs)

/-- Only the one-point marginal mark probabilities enter equation (6.7). -/
theorem lintegral_markedCount_of_constant_marginals {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ℝ) (M : ℝ → Ω → Prop) (p : ℝ≥0∞)
    (hM : ∀ s ∈ S, MeasurableSet {ω | M s ω})
    (hp : ∀ s ∈ S, μ {ω | M s ω} = p) :
    (∫⁻ ω, markedCount S M ω ∂μ) = (S.card : ℝ≥0∞) * p := by
  rw [lintegral_markedCount μ S M hM]
  simp_rw [Finset.sum_congr rfl (fun s hs => hp s hs)]
  simp [nsmul_eq_mul]

/-- The transverse interior parameter preimages from Lemma 6.1. -/
def transverseZeros {m : ℕ} (ψ : ℝ → Source.Space m) (L : ℝ)
    (D : Source.Space m) : Set ℝ :=
  {s | 0 < s ∧ s < L ∧ inner ℝ D (ψ s) = 0 ∧
    DifferentiableAt ℝ ψ s ∧ inner ℝ D (deriv ψ s) ≠ 0}

/-- Nonnegative parameterized spherical speed integral. -/
def sphericalLength {m : ℕ} (ψ : ℝ → Source.Space m) (L : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Icc 0 L, ENNReal.ofReal ‖deriv ψ s‖

/-- Explicit external classical input, not an axiom declaration.
For m≥2, an absolutely continuous unit-sphere curve and D~N(0,I_m), this is
exactly the parameterized spherical Crofton theorem with the original hypotheses
and parameter multiplicity, as in paper Lemma 6.1. Sources: Santaló (1942),
Eq. (37), p. 716 for m=2; Santaló (2004), Eq. (18.36), pp. 323–324 generally.
The only intended use is the unmarked transverse-intersection expectation.
No upper-envelope visibility or Gaussian rank coefficient is included here. -/
def ClassicalCroftonLaw : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (L : ℝ), 0 < L → ∀ (ψ : ℝ → Source.Space m),
    AbsolutelyContinuousOnInterval ψ 0 L → (∀ s ∈ Icc 0 L, ‖ψ s‖ = 1) →
      (∫⁻ D, ((transverseZeros ψ L D).encard : ℝ≥0∞) ∂standardGaussian m) =
        ENNReal.ofReal (1 / Real.pi) * sphericalLength ψ L ∧
      ∀ᵐ D ∂standardGaussian m, (transverseZeros ψ L D).Finite

/-- Explicit external classical projection theorem for isotropic Gaussian vectors.
Original quantifiers: every m and every unit v has projection Z·v~N(0,1).
This is the standard linear-image theorem for multivariate normal distributions
(MIT 18.443, Lecture 4, 2006, p. 25, “Linear transformation of a normal random vector”,
https://ocw.mit.edu/courses/18-443-statistics-for-applications-fall-2006/da928274a46632ce0d35d2012a1c8e74_lecture4.pdf),
used solely to identify the individual visibility marks. -/
def GaussianUnitProjectionLaw : Prop :=
  ∀ (m : ℕ) (v : Source.Space m), ‖v‖ = 1 →
    (standardGaussian m).map (fun z => inner ℝ z v) = gaussianReal 0 1

/-- Independent Gaussian common-pair and remaining-candidate vectors. -/
def vectorMarkLaw (m n : ℕ) : Measure (Source.Space m × (Fin n → Source.Space m)) :=
  (standardGaussian m).prod (Measure.pi (fun _ : Fin n => standardGaussian m))

instance (m n : ℕ) : IsProbabilityMeasure (vectorMarkLaw m n) := by
  unfold vectorMarkLaw
  infer_instance

def vectorVisible {m : ℕ} (n : ℕ) (v : Source.Space m) :
    Set (Source.Space m × (Fin n → Source.Space m)) :=
  {z | ∀ k, inner ℝ (z.2 k) v < (Real.sqrt 2)⁻¹ * inner ℝ z.1 v}

lemma measurableSet_vectorVisible {m : ℕ} (n : ℕ) (v : Source.Space m) :
    MeasurableSet (vectorVisible n v) := by
  simp only [vectorVisible, setOf_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_lt (by fun_prop) (by fun_prop)

/-- The common value at a Gaussian pair intersection is N(0,1/2), derived
from the classical one-dimensional projection theorem and scalar Gaussian scaling. -/
theorem commonPairValue_law (hproj : GaussianUnitProjectionLaw) (m : ℕ)
    (v : Source.Space m) (hv : ‖v‖ = 1) :
    (standardGaussian m).map (fun z => (Real.sqrt 2)⁻¹ * inner ℝ z v) =
      gaussianReal 0 (1/2) := by
  change (standardGaussian m).map
    ((fun x : ℝ => (Real.sqrt 2)⁻¹ * x) ∘ (fun z => inner ℝ z v)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hproj m v hv,
    gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.eq
    simp only [NNReal.coe_mk, NNReal.coe_one, mul_one, NNReal.coe_div,
      NNReal.coe_ofNat]
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    field_simp
    nlinarith

/-- Push the independent vector marks to their actual scalar Gaussian law. -/
theorem vectorMark_projection (hproj : GaussianUnitProjectionLaw) (m n : ℕ)
    (v : Source.Space m) (hv : ‖v‖ = 1) :
    MeasurePreserving
      (fun z : Source.Space m × (Fin n → Source.Space m) =>
        ((Real.sqrt 2)⁻¹ * inner ℝ z.1 v, fun k => inner ℝ (z.2 k) v))
      (vectorMarkLaw m n) (scalarMarkLaw n) := by
  have hC : MeasurePreserving (fun z : Source.Space m => (Real.sqrt 2)⁻¹ * inner ℝ z v)
      (standardGaussian m) (gaussianReal 0 (1/2)) :=
    ⟨by fun_prop, commonPairValue_law hproj m v hv⟩
  have hG : MeasurePreserving (fun z : Source.Space m => inner ℝ z v)
      (standardGaussian m) (gaussianReal 0 1) := ⟨by fun_prop, hproj m v hv⟩
  exact hC.prod (measurePreserving_pi (fun _ : Fin n => standardGaussian m)
    (fun _ : Fin n => gaussianReal 0 1) (fun _ => hG))

/-- The visibility probability at every unit direction is the same explicit
Gaussian CDF integral; no independence between different directions is assumed. -/
theorem vector_visibility_mass (hproj : GaussianUnitProjectionLaw) (m n : ℕ)
    (v : Source.Space m) (hv : ‖v‖ = 1) :
    vectorMarkLaw m n (vectorVisible n v) = visibilityProbability n := by
  have h := (vectorMark_projection hproj m n v hv).measure_preimage
    (measurableSet_scalarVisible n).nullMeasurableSet
  exact h.trans (scalar_visibility_mass n)

/-- Equation (6.7) for any finite parameter set, using the actual Gaussian
vectors and their possibly dependent visibility marks along the curve. -/
theorem finite_gaussian_marked_count (hproj : GaussianUnitProjectionLaw)
    {m : ℕ} (n : ℕ) (ψ : ℝ → Source.Space m) (S : Finset ℝ)
    (hunit : ∀ s ∈ S, ‖ψ s‖ = 1) :
    (∫⁻ z, (({s | s ∈ S ∧ z ∈ vectorVisible n (ψ s)} : Set ℝ).encard : ℝ≥0∞)
      ∂vectorMarkLaw m n) = (S.card : ℝ≥0∞) * visibilityProbability n := by
  simp_rw [← markedCount_eq_encard]
  apply lintegral_markedCount_of_constant_marginals
  · exact fun s hs => measurableSet_vectorVisible n (ψ s)
  · exact fun s hs => vector_visibility_mass hproj m n (ψ s) (hunit s hs)

/-- The same finite marked identity stated on the actual set of parameter preimages. -/
theorem finite_gaussian_marked_set (hproj : GaussianUnitProjectionLaw)
    {m : ℕ} (n : ℕ) (ψ : ℝ → Source.Space m) (S : Set ℝ) (hS : S.Finite)
    (hunit : ∀ s ∈ S, ‖ψ s‖ = 1) :
    (∫⁻ z, ((S ∩ {s | z ∈ vectorVisible n (ψ s)}).encard : ℝ≥0∞)
      ∂vectorMarkLaw m n) = (S.encard : ℝ≥0∞) * visibilityProbability n := by
  have h := finite_gaussian_marked_count hproj n ψ hS.toFinset
    (fun s hs => hunit s (hS.mem_toFinset.mp hs))
  simpa only [hS.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq,
    hS.encard_eq_coe_toFinset_card] using h

lemma visibilityProbability_le_one (n : ℕ) : visibilityProbability n ≤ 1 := by
  rw [← scalar_visibility_mass]
  haveI : IsProbabilityMeasure (scalarMarkLaw n) := by
    unfold scalarMarkLaw
    infer_instance
  exact prob_le_one

/-- The marked Crofton expectation for a fixed pair.  The external Crofton
input is unmarked; the visibility factor is derived by finite marked Tonelli
and the real Gaussian projection laws above. -/
theorem marked_pair_crofton (hcrofton : ClassicalCroftonLaw)
    (hproj : GaussianUnitProjectionLaw) (m n : ℕ) (hm : 2 ≤ m) (L : ℝ) (hL : 0 < L)
    (ψ : ℝ → Source.Space m) (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1) :
    (∫⁻ D, ∫⁻ z, (((transverseZeros ψ L D) ∩
      {s | z ∈ vectorVisible n (ψ s)}).encard : ℝ≥0∞)
      ∂vectorMarkLaw m n ∂standardGaussian m) =
      (ENNReal.ofReal (1 / Real.pi) * sphericalLength ψ L) *
        visibilityProbability n := by
  obtain ⟨hmean, hfinite⟩ := hcrofton m hm L hL ψ hac hunit
  calc
    _ = ∫⁻ D, ((transverseZeros ψ L D).encard : ℝ≥0∞) * visibilityProbability n
        ∂standardGaussian m := by
      apply lintegral_congr_ae
      filter_upwards [hfinite] with D hD
      apply finite_gaussian_marked_set hproj n ψ _ hD
      intro s hs
      exact hunit s ⟨hs.1.le, hs.2.1.le⟩
    _ = (∫⁻ D, ((transverseZeros ψ L D).encard : ℝ≥0∞) ∂standardGaussian m) *
        visibilityProbability n :=
      lintegral_mul_const' (visibilityProbability n) _ (ne_of_lt ((visibilityProbability_le_one n).trans_lt
        (by simp : (1 : ℝ≥0∞) < ∞)))
    _ = _ := by rw [hmean]

/-- The half-variance Gaussian density is the square of the standard density,
with its exact normalization. This supplies the analytic factor in (6.6). -/
theorem halfGaussianPDFReal (y : ℝ) :
    gaussianPDFReal 0 (1/2) y =
      (2 * Real.sqrt Real.pi) * (gaussianPDFReal 0 1 y) ^ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hsπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hπ)
  have hs2π : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hsπsq := Real.sq_sqrt hπ.le
  have hs2πsq := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hexp : (Real.exp (-(y ^ 2) / 2)) ^ 2 = Real.exp (-(y ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [gaussianPDFReal, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    sub_zero]
  norm_num only [mul_one, mul_div_cancel₀, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  rw [mul_pow, hexp]
  field_simp
  nlinarith

theorem halfGaussianPDF (y : ℝ) :
    gaussianPDF 0 (1/2) y = ENNReal.ofReal (2 * Real.sqrt Real.pi) *
      (gaussianPDF 0 1 y) ^ 2 := by
  simp only [gaussianPDF, halfGaussianPDFReal, ENNReal.ofReal_mul
    (by positivity : 0 ≤ 2 * Real.sqrt Real.pi), ENNReal.ofReal_pow
    (gaussianPDFReal_nonneg 0 1 y)]

/-- Exact visibility factor (6.6), derived from the Gaussian scalar marks. -/
theorem visibilityProbability_density (n : ℕ) :
    visibilityProbability n = ENNReal.ofReal (2 * Real.sqrt Real.pi) *
      ∫⁻ y, (gaussianPDF 0 1 y) ^ 2 * normalCDF y ^ n := by
  unfold visibilityProbability
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1/2 : ℝ≥0) ≠ 0)]
  have hCDF : Measurable normalCDF := by
    apply Monotone.measurable
    intro x y hxy
    exact measure_mono (Iic_subset_Iic.mpr hxy)
  rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_gaussianPDF _ _).aemeasurable
    (hCDF.pow_const n).aemeasurable]
  change (∫⁻ y, gaussianPDF 0 (1/2) y * normalCDF y ^ n) = _
  simp_rw [halfGaussianPDF]
  simp only [mul_assoc]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Exact external specialization of a published Gaussian-polytope identity.
Kabluchko–Zaporozhets, arXiv:1706.08092v1, Theorem 1.1, Eq. (2), states
E Vol_d(conv(X_1,...,X_K)) = κ_d K!/(d!(K-d-1)!) ∫ Φ^(K-d-1) φ^(d+1)
for iid standard normals in ℝ^d and 1≤d<K. In dimension d=1, §1.3,
Eq. (8) and the following displayed equation identify the same expected
volume with 2 E max_j G_j. The specialized statement below therefore has
exactly K≥2, the actual `gaussianMaxMean` and the standard normal PDF/CDF.
It contains no crossing, sphere-curve or visibility statement.
Source: https://arxiv.org/pdf/1706.08092, pp. 2–3. -/
def GaussianMaxIntegralLaw : Prop :=
  ∀ K : ℕ, 2 ≤ K →
    ENNReal.ofReal (Paper35.gaussianMaxMean K) =
      ENNReal.ofReal ((K : ℝ) * ((K : ℝ) - 1)) *
        ∫⁻ y, (gaussianPDF 0 1 y) ^ 2 * normalCDF y ^ (K - 2)

/-- The new upper-envelope rank coefficient is derived from the actual marked
probability and the published Gaussian-maximum integral formula. -/
theorem marked_coefficient_eq_gaussianRankCoefficient (hmax : GaussianMaxIntegralLaw)
    (K : ℕ) (hK : 2 ≤ K) :
    (K.choose 2 : ℝ≥0∞) * ENNReal.ofReal (1 / Real.pi) *
      visibilityProbability (K - 2) =
        ENNReal.ofReal (Paper35.gaussianRankCoefficient K) := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsq : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hconstant : ((K.choose 2 : ℕ) : ℝ) * (1 / Real.pi) *
      (2 * Real.sqrt Real.pi) =
        (1 / Real.sqrt Real.pi) * ((K : ℝ) * ((K : ℝ) - 1)) := by
    rw [Nat.cast_choose_two]
    field_simp
    nlinarith
  rw [visibilityProbability_density]
  calc
    _ = ENNReal.ofReal (((K.choose 2 : ℕ) : ℝ) * (1 / Real.pi) *
          (2 * Real.sqrt Real.pi)) *
        (∫⁻ y, (gaussianPDF 0 1 y) ^ 2 * normalCDF y ^ (K - 2)) := by
      simp only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (K.choose 2 : ℕ)),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/Real.pi),
        ENNReal.ofReal_natCast, mul_assoc]
    _ = ENNReal.ofReal (1 / Real.sqrt Real.pi) *
        (ENNReal.ofReal ((K : ℝ) * ((K : ℝ) - 1)) *
          (∫⁻ y, (gaussianPDF 0 1 y) ^ 2 * normalCDF y ^ (K - 2))) := by
      rw [hconstant, ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt Real.pi)]
      exact mul_assoc _ _ _
    _ = ENNReal.ofReal (1 / Real.sqrt Real.pi) *
        ENNReal.ofReal (Paper35.gaussianMaxMean K) := by rw [← hmax K hK]
    _ = ENNReal.ofReal (Paper35.gaussianRankCoefficient K) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt Real.pi)]
      congr 1
      unfold Paper35.gaussianRankCoefficient
      ring

/-- Classical finite-dimensional absolutely-continuous curve length theorem,
retained as an explicit external input: parameterized metric total variation
is the integral of the Euclidean derivative norm. This identifies the length
used above with an independently defined geometric length. -/
def ACCurveLengthLaw : Prop :=
  ∀ (m : ℕ) (L : ℝ), 0 < L → ∀ (ψ : ℝ → Source.Space m),
    AbsolutelyContinuousOnInterval ψ 0 L →
      eVariationOn ψ (Icc 0 L) = sphericalLength ψ L

/-- The integral-speed expression is exactly the actual parameterized metric length. -/
theorem sphericalLength_eq_eVariationOn (hlength : ACCurveLengthLaw)
    (m : ℕ) (L : ℝ) (hL : 0 < L) (ψ : ℝ → Source.Space m)
    (hac : AbsolutelyContinuousOnInterval ψ 0 L) :
    sphericalLength ψ L = eVariationOn ψ (Icc 0 L) :=
  (hlength m L hL ψ hac).symm

/-- Summing the identical per-pair marked expectations produces precisely
`c_K` times the parameterized spherical length. The coefficient identity is
proved above rather than supplied as an upper-envelope assumption. -/
theorem all_pairs_marked_crofton (hcrofton : ClassicalCroftonLaw)
    (hproj : GaussianUnitProjectionLaw) (hmax : GaussianMaxIntegralLaw)
    (m K : ℕ) (hm : 2 ≤ m) (hK : 2 ≤ K) (L : ℝ) (hL : 0 < L)
    (ψ : ℝ → Source.Space m) (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1) :
    (K.choose 2 : ℝ≥0∞) *
      (∫⁻ D, ∫⁻ z, (((transverseZeros ψ L D) ∩
        {s | z ∈ vectorVisible (K - 2) (ψ s)}).encard : ℝ≥0∞)
        ∂vectorMarkLaw m (K - 2) ∂standardGaussian m) =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient K) * sphericalLength ψ L := by
  rw [marked_pair_crofton hcrofton hproj m (K-2) hm L hL ψ hac hunit]
  calc
    _ = ((K.choose 2 : ℝ≥0∞) * ENNReal.ofReal (1/Real.pi) *
        visibilityProbability (K-2)) * sphericalLength ψ L := by ac_rfl
    _ = _ := by rw [marked_coefficient_eq_gaussianRankCoefficient hmax K hK]

end Paper35.GaussianMarked

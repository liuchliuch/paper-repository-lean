import Paper35.VisibilityKernel
import Paper35.Gini
import Paper35.Counterexamples
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic.FieldSimp

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal Topology
namespace Paper35.Sharpness
open Source Source.WeightedModel

/-- Half-width of the independent bias interval in (5.3). -/
def biasHalfWidth (B : ℝ) : ℝ := 1 / (2 * B)

/-- The actual uniform bias density, with the prescribed height `B`. -/
def biasDensity (B : ℝ) (y : ℝ) : ℝ≥0∞ :=
  (Icc (-biasHalfWidth B) (biasHalfWidth B)).indicator (fun _ => ENNReal.ofReal B) y

lemma measurable_biasDensity (B : ℝ) : Measurable (biasDensity B) :=
  measurable_const.indicator measurableSet_Icc

lemma biasDensity_le (B y : ℝ) : biasDensity B y ≤ ENNReal.ofReal B := by
  classical
  unfold biasDensity
  by_cases hy : y ∈ Icc (-biasHalfWidth B) (biasHalfWidth B) <;> simp [hy]

lemma biasDensity_sq (B y : ℝ) : biasDensity B y * biasDensity B y =
    ENNReal.ofReal B * biasDensity B y := by
  classical
  unfold biasDensity
  by_cases hy : y ∈ Icc (-biasHalfWidth B) (biasHalfWidth B) <;> simp [hy]

lemma biasDensity_normalized {B : ℝ} (hB : 0 < B) : (∫⁻ y, biasDensity B y) = 1 := by
  unfold biasDensity
  rw [lintegral_indicator measurableSet_Icc]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
    sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul hB.le]
  have heq : B * (biasHalfWidth B + biasHalfWidth B) = 1 := by
    unfold biasHalfWidth
    field_simp; ring
  rw [heq, ENNReal.ofReal_one]

/-- Any weight law with an independent uniform bias is an actual source model. -/
def independentUniformModel {d : ℕ} (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (B : ℝ) (hB : 0 < B) : WeightedModel d where
  weights := μ
  probability := inferInstance
  g := fun _ y => biasDensity B y
  measurable_g := (measurable_biasDensity B).comp measurable_snd
  normalized_g := Filter.Eventually.of_forall fun _ => biasDensity_normalized hB
  b₀ := fun _ => Real.toNNReal B
  measurable_b₀ := measurable_const
  bound := Filter.Eventually.of_forall fun _ y => biasDensity_le B y
  average_pos := by simpa using ENNReal.ofReal_pos.mpr hB
  average_finite := by simp

variable {d : ℕ} (μ : Measure (Space d)) [IsProbabilityMeasure μ] {B : ℝ} (hB : 0 < B)

lemma uniformModel_average : (independentUniformModel μ B hB).average = ENNReal.ofReal B := by
  simp [average, independentUniformModel, ENNReal.ofReal]

lemma uniformModel_tilted : (independentUniformModel μ B hB).tilted = μ := by
  exact tilted_eq_weights_of_constant (independentUniformModel μ B hB) (Real.toNNReal B)
    (Filter.Eventually.of_forall fun _ => rfl)

lemma uniformModel_joint : (independentUniformModel μ B hB).joint =
    μ.prod (volume.withDensity (biasDensity B)) := by
  exact (prod_withDensity_right (measurable_biasDensity B)).symm

lemma origin_scoreDensity (y : ℝ) :
    VisibleCrossing.scoreDensity (independentUniformModel μ B hB) 0 y = biasDensity B y := by
  simp [VisibleCrossing.scoreDensity, independentUniformModel]

/-- At the origin the score law is exactly the independently sampled bias law. -/
lemma origin_scoreCDF (y : ℝ) :
    (independentUniformModel μ B hB).scoreCDF 0 y =
      (volume.withDensity (biasDensity B)) (Iic y) := by
  rw [VisibleCrossing.scoreCDF_eq_densityLaw]
  rw [show VisibleCrossing.scoreDensity (independentUniformModel μ B hB) 0 = biasDensity B
    from funext (origin_scoreDensity μ hB)]

lemma origin_slopeSlice (u : Space d) (y : ℝ) :
    (independentUniformModel μ B hB).slopeSlice 0 u y =
      biasDensity B y • μ.map (fun w => inner ℝ w u) := by
  simp only [slopeSlice, independentUniformModel, inner_zero_right, sub_zero]
  rw [withDensity_const, Measure.map_smul]

lemma projected_gini_eq (u : Space d) :
    (∫⁻ a, ∫⁻ a', ENNReal.ofReal |a - a'|
      ∂μ.map (fun w => inner ℝ w u) ∂μ.map (fun w => inner ℝ w u)) =
        (independentUniformModel μ B hB).directionalGini u := by
  let τ := μ.map (fun w => inner ℝ w u)
  letI : IsProbabilityMeasure τ := Measure.isProbabilityMeasure_map (by fun_prop)
  rw [VisibilityKernel.directionalGini_layerCake]
  simp only [VisibilityKernel.tiltedProjection, uniformModel_tilted μ hB]
  rw [← lintegral_prod (fun z : ℝ × ℝ => ENNReal.ofReal |z.1 - z.2|)
    ((measurable_fst.sub measurable_snd).abs).ennreal_ofReal.aemeasurable]
  exact Visibility.gini_layer_cake τ

/-- The source crossing kernel factors exactly at the origin, for every
projected weight law, including laws without a first moment. -/
theorem origin_crossingKernel (u : Space d) (y : ℝ) :
    (independentUniformModel μ B hB).crossingKernel 0 u y =
      biasDensity B y * biasDensity B y *
        (independentUniformModel μ B hB).directionalGini u := by
  let τ := μ.map (fun w => inner ℝ w u)
  letI : IsProbabilityMeasure τ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hm : Measurable (fun a : ℝ => ∫⁻ a', ENNReal.ofReal |a - a'| ∂τ) :=
    ((measurable_fst.sub measurable_snd).abs).ennreal_ofReal.lintegral_prod_right'
  unfold crossingKernel
  simp_rw [origin_slopeSlice μ hB, lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul _ hm]
  rw [projected_gini_eq μ hB u]
  ac_rfl

/-- The second identity of (5.4), for the actual uniform bias law. -/
theorem uniform_bias_cdf_density_square (hB : 0 < B) (n : ℕ) :
    (∫⁻ y, (volume.withDensity (biasDensity B)) (Iic y) ^ n *
      (biasDensity B y * biasDensity B y)) = ENNReal.ofReal B / (n + 1 : ℝ≥0∞) := by
  have hn := CDFPower.lintegral_cdf_mass_pow_mul_density
    (measurable_biasDensity B).aemeasurable (biasDensity_normalized hB) n
  simp_rw [biasDensity_sq]
  calc
    _ = ENNReal.ofReal B * ∫⁻ y,
        (volume.withDensity (biasDensity B)) (Iic y) ^ n * biasDensity B y := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro y
      ac_rfl
    _ = _ := by rw [hn]; rfl

/-- Uniform independent biases attain the sharp visibility estimate exactly
at the origin for every prescribed weight law. -/
theorem origin_visibility_equality (n : ℕ) (u : Space d) :
    (∫⁻ y, (independentUniformModel μ B hB).scoreCDF 0 y ^ n *
      (independentUniformModel μ B hB).crossingKernel 0 u y) =
      (ENNReal.ofReal B / (n + 1 : ℝ≥0∞)) *
        (independentUniformModel μ B hB).directionalGini u := by
  have hF := (VisibilityKernel.measurable_scoreCDF (independentUniformModel μ B hB) 0).pow_const n
  calc
    _ = ∫⁻ y, ((independentUniformModel μ B hB).scoreCDF 0 y ^ n *
        (biasDensity B y * biasDensity B y)) *
          (independentUniformModel μ B hB).directionalGini u := by
      apply lintegral_congr
      intro y
      rw [origin_crossingKernel]
      ac_rfl
    _ = (∫⁻ y, (independentUniformModel μ B hB).scoreCDF 0 y ^ n *
        (biasDensity B y * biasDensity B y)) *
          (independentUniformModel μ B hB).directionalGini u :=
      lintegral_mul_const _ (hF.mul ((measurable_biasDensity B).mul (measurable_biasDensity B)))
    _ = _ := by
      simp_rw [origin_scoreCDF μ hB]
      rw [uniform_bias_cdf_density_square hB n]

/-- An affine image of unit-uniform coordinates is uniform on `[-a,a]`. -/
def affineUniform (a t : ℝ) : ℝ := -a + (2 * a) * t

lemma measurable_affineUniform (a : ℝ) : Measurable (affineUniform a) := by
  unfold affineUniform
  fun_prop

/-- Independent unit-uniform coordinates, transformed coordinatewise into
Euclidean space. This is the actual weight vector used in (5.3). -/
def uniformWeightMap (d : ℕ) (a : ℝ) (z : Fin d → ℝ) : Space d :=
  (EuclideanSpace.measurableEquiv (Fin d)).symm (fun i => affineUniform a (z i))

lemma measurable_uniformWeightMap (d : ℕ) (a : ℝ) : Measurable (uniformWeightMap d a) := by
  exact (EuclideanSpace.measurableEquiv (Fin d)).symm.measurable.comp
    (measurable_pi_lambda _ (fun i => (measurable_affineUniform a).comp (measurable_pi_apply i)))

def uniformWeights (d : ℕ) (a : ℝ) : Measure (Space d) :=
  (Measure.pi (fun _ : Fin d => Gini.unitLaw)).map (uniformWeightMap d a)

instance uniformWeights_probability (d : ℕ) (a : ℝ) : IsProbabilityMeasure (uniformWeights d a) :=
  Measure.isProbabilityMeasure_map (measurable_uniformWeightMap d a).aemeasurable

/-- The entire coordinate law is the product of identical uniform laws. -/
theorem uniformWeights_coordinate_product (d : ℕ) (a : ℝ) :
    (uniformWeights d a).map (EuclideanSpace.measurableEquiv (Fin d)) =
      Measure.pi (fun _ : Fin d => Gini.unitLaw.map (affineUniform a)) := by
  letI : IsProbabilityMeasure (Gini.unitLaw.map (affineUniform a)) :=
    Measure.isProbabilityMeasure_map (measurable_affineUniform a).aemeasurable
  rw [uniformWeights, Measure.map_map
    (EuclideanSpace.measurableEquiv (Fin d)).measurable (measurable_uniformWeightMap d a)]
  change (Measure.pi (fun _ : Fin d => Gini.unitLaw)).map
    (fun z i => affineUniform a (z i)) = _
  exact Measure.pi_map_pi fun _ => (measurable_affineUniform a).aemeasurable

lemma measurable_coordinate (i : Fin d) : Measurable (fun w : Space d => w i) :=
  (measurable_pi_apply i).comp (EuclideanSpace.measurableEquiv (Fin d)).measurable

/-- Each projected coordinate has the prescribed affine-uniform law. -/
theorem uniformWeights_coordinate_marginal (a : ℝ) (i : Fin d) :
    (uniformWeights d a).map (fun w => w i) = Gini.unitLaw.map (affineUniform a) := by
  rw [uniformWeights, Measure.map_map (measurable_coordinate i) (measurable_uniformWeightMap d a)]
  change (Measure.pi (fun _ : Fin d => Gini.unitLaw)).map
    ((affineUniform a) ∘ Function.eval i) = _
  rw [← Measure.map_map (measurable_affineUniform a) (measurable_pi_apply i),
    (measurePreserving_eval (fun _ : Fin d => Gini.unitLaw) i).map_eq]

/-- The exact Gini mean difference for independent copies of the uniform slope. -/
theorem affine_uniform_lintegral_gini (a : ℝ) (ha : 0 ≤ a) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal |z.1 - z.2|
      ∂(Gini.unitLaw.map (affineUniform a)).prod (Gini.unitLaw.map (affineUniform a))) =
        ENNReal.ofReal (2 * a / 3) := by
  have hm := measurable_affineUniform a
  have hZ : MemLp (affineUniform a) 2 Gini.unitLaw :=
    (memLp_const (-a)).add (Gini.unitLaw_memLp.const_mul (2 * a))
  have hi := hZ.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hip : Integrable (fun z : ℝ × ℝ => |affineUniform a z.1 - affineUniform a z.2|)
      (Gini.unitLaw.prod Gini.unitLaw) :=
    ((hi.comp_fst Gini.unitLaw).sub (hi.comp_snd Gini.unitLaw)).abs
  have hmean : Gini.meanDifference Gini.unitLaw (affineUniform a) = 2 * a / 3 := by
    rw [show affineUniform a = (fun t : ℝ => -a + (2 * a) * t) from rfl,
      Gini.meanDifference_affine]
    change |2 * a| * Gini.meanDifference Gini.unitLaw id = _
    rw [Gini.unitLaw_meanDifference, abs_of_nonneg (mul_nonneg (by norm_num) ha)]
    ring
  rw [Measure.map_prod_map Gini.unitLaw Gini.unitLaw hm hm,
    lintegral_map ((measurable_fst.sub measurable_snd).abs.ennreal_ofReal) (hm.prodMap hm)]
  calc
    _ = ENNReal.ofReal (Gini.meanDifference Gini.unitLaw (affineUniform a)) :=
      (ofReal_integral_eq_lintegral_ofReal hip
        (Filter.Eventually.of_forall fun z => abs_nonneg _)).symm
    _ = _ := congrArg ENNReal.ofReal hmean

/-- Unit coordinate direction of the straight probe. -/
def axis (i : Fin d) : Space d := EuclideanSpace.single i 1

lemma inner_axis (i : Fin d) (w : Space d) : inner ℝ w (axis i) = w i := by
  simp [axis, EuclideanSpace.inner_single_right]

/-- The first identity of (5.4) for each coordinate of the actual product model. -/
theorem uniformWeights_directionalGini (a : ℝ) (ha : 0 ≤ a) (i : Fin d)
    {B : ℝ} (hB : 0 < B) :
    (independentUniformModel (uniformWeights d a) B hB).directionalGini (axis i) =
      ENNReal.ofReal (2 * a / 3) := by
  letI : IsProbabilityMeasure (Gini.unitLaw.map (affineUniform a)) :=
    Measure.isProbabilityMeasure_map (measurable_affineUniform a).aemeasurable
  rw [← projected_gini_eq (uniformWeights d a) hB (axis i)]
  simp_rw [inner_axis]
  rw [uniformWeights_coordinate_marginal]
  rw [← lintegral_prod (fun z : ℝ × ℝ => ENNReal.ofReal |z.1 - z.2|)
    ((measurable_fst.sub measurable_snd).abs).ennreal_ofReal.aemeasurable]
  exact affine_uniform_lintegral_gini a ha

/-- Every actual coordinate has variance `a²/3`; no moment equality is assumed. -/
theorem uniformWeights_coordinate_variance (a : ℝ) (i : Fin d) :
    ProbabilityTheory.variance (fun w : Space d => w i) (uniformWeights d a) = a ^ 2 / 3 := by
  have hd : ProbabilityTheory.IdentDistrib (fun w : Space d => w i) (affineUniform a)
      (uniformWeights d a) Gini.unitLaw :=
    ⟨(measurable_coordinate i).aemeasurable, (measurable_affineUniform a).aemeasurable,
      uniformWeights_coordinate_marginal a i⟩
  rw [hd.variance_eq]
  have hvar := ProbabilityTheory.variance_const_add (μ := Gini.unitLaw)
    (X := fun t : ℝ => (2 * a) * t)
    (measurable_const.mul measurable_id).aestronglyMeasurable (-a)
  rw [show affineUniform a = (fun t : ℝ => -a + (2 * a) * t) from rfl,
    hvar, ProbabilityTheory.variance_mul]
  change (2 * a) ^ 2 * ProbabilityTheory.variance id Gini.unitLaw = _
  rw [Gini.unitLaw_variance]
  ring

/-- The affine-unit representation is exactly the normalized Lebesgue
uniform law on `[-a,a]`, so the coordinate law has a genuine density. -/
theorem affine_uniform_law {a : ℝ} (ha : 0 < a) :
    Gini.unitLaw.map (affineUniform a) = Counterexamples.uniformSlope a := by
  have h2a : 0 < 2 * a := by positivity
  have hm := measurable_affineUniform a
  have hpre : (affineUniform a) ⁻¹' Icc (-a) a = Icc (0 : ℝ) 1 := by
    ext t
    simp only [mem_preimage, mem_Icc, affineUniform]
    constructor
    · rintro ⟨hl, hr⟩
      constructor <;> nlinarith
    · rintro ⟨hl, hr⟩
      constructor <;> nlinarith
  have hfull : volume.map (affineUniform a) = ENNReal.ofReal |(2 * a)⁻¹| • volume := by
    change volume.map ((fun x : ℝ => -a + x) ∘ (fun t : ℝ => (2 * a) * t)) = _
    have hadd : Measurable (fun x : ℝ => -a + x) := by fun_prop
    have hmul : Measurable (fun t : ℝ => (2 * a) * t) := by fun_prop
    rw [← Measure.map_map hadd hmul,
      Real.map_volume_mul_left h2a.ne', Measure.map_smul, map_add_left_eq_self]
  calc
    _ = (volume.map (affineUniform a)).restrict (Icc (-a) a) := by
      rw [restrict_map hm measurableSet_Icc, hpre]
      rfl
    _ = ENNReal.ofReal |(2 * a)⁻¹| • volume.restrict (Icc (-a) a) := by
      rw [hfull, Measure.restrict_smul]
    _ = _ := by
      rw [abs_of_pos (inv_pos.mpr h2a), ENNReal.ofReal_inv_of_pos h2a]
      unfold Counterexamples.uniformSlope ProbabilityTheory.cond
      rw [Real.volume_Icc]
      congr 2
      congr 1
      ring

/-- The coordinates of the constructed weight vector have bounded densities. -/
theorem uniformWeights_coordinate_density {a : ℝ} (ha : 0 < a) (i : Fin d) :
    (uniformWeights d a).map (fun w => w i) =
      volume.withDensity ((Icc (-a) a).indicator (fun _ => (ENNReal.ofReal (2 * a))⁻¹)) := by
  rw [uniformWeights_coordinate_marginal, affine_uniform_law ha, Counterexamples.uniformSlope_density]

lemma uniformWeights_coordinate_bounded {a : ℝ} (ha : 0 < a) (i : Fin d) :
    ∀ᵐ w ∂uniformWeights d a, |w i| ≤ a := by
  have hs : ∀ᵐ z ∂Counterexamples.uniformSlope a, z ∈ Icc (-a) a := by
    unfold Counterexamples.uniformSlope ProbabilityTheory.cond
    apply (ae_smul_measure_iff (ENNReal.inv_ne_zero.mpr
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))).2
    exact ae_restrict_mem measurableSet_Icc
  have hz : ∀ᵐ z ∂(uniformWeights d a).map (fun w => w i), |z| ≤ a := by
    rw [uniformWeights_coordinate_marginal, affine_uniform_law ha]
    simpa only [abs_le] using hs
  exact (ae_map_iff (measurable_coordinate i).aemeasurable
    (measurableSet_le measurable_id.abs measurable_const)).1 hz

/-- The local pair-visible intensity furnished by the exact crossing formula. -/
def localIntensity {d : ℕ} (m : WeightedModel d) (K : ℕ) (x u : Space d) : ℝ≥0∞ :=
  (K.choose 2 : ℝ≥0∞) * ∫⁻ y, m.scoreCDF x y ^ (K - 2) * m.crossingKernel x u y

/-- Exact origin intensity for the iid-coordinate uniform construction. -/
theorem origin_rank_intensity (a : ℝ) (ha : 0 ≤ a) (i : Fin d)
    {B : ℝ} (hB : 0 < B) (K : ℕ) (hK : 2 ≤ K) :
    localIntensity (independentUniformModel (uniformWeights d a) B hB) K 0 (axis i) =
      ((K : ℝ≥0∞) * ENNReal.ofReal B / 2) * ENNReal.ofReal (2 * a / 3) := by
  have hi : (K - 2 : ℕ) + 1 = K - 1 := by omega
  have hi' : ((K - 2 : ℕ) : ℝ≥0∞) + 1 = ((K - 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hi
  unfold localIntensity
  rw [origin_visibility_equality, uniformWeights_directionalGini a ha i hB, hi',
    ← mul_assoc, weighted_rank_cancellation K hK]

/-- The coordinates in (5.3) have exactly the requested variance. -/
theorem sharp_coordinates_variance (σ : ℝ) (i : Fin d) :
    ProbabilityTheory.variance (fun w : Space d => w i)
      (uniformWeights d (Real.sqrt 3 * σ)) = σ ^ 2 := by
  rw [uniformWeights_coordinate_variance, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

/-- The exact local intensity (5.5), for every positive prescribed `B,σ`,
every rank `K≥2`, and every coordinate direction in every positive dimension. -/
theorem origin_sharp_intensity {σ B : ℝ} (hσ : 0 < σ) (hB : 0 < B)
    (K : ℕ) (hK : 2 ≤ K) (i : Fin d) :
    localIntensity (independentUniformModel (uniformWeights d (Real.sqrt 3 * σ)) B hB)
      K 0 (axis i) = ENNReal.ofReal ((K : ℝ) / Real.sqrt 3 * B * σ) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [origin_rank_intensity _ (mul_nonneg hs.le hσ.le) i hB K hK]
  have hfrac : Real.sqrt 3 / 3 = 1 / Real.sqrt 3 := by
    apply (eq_div_iff hs.ne').2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hreal : ((K : ℝ) * B / 2) * (2 * (Real.sqrt 3 * σ) / 3) =
      (K : ℝ) / Real.sqrt 3 * B * σ := by
    calc
      _ = (K : ℝ) * B * σ * (Real.sqrt 3 / 3) := by ring
      _ = _ := by rw [hfrac]; ring
  calc
    _ = ENNReal.ofReal (((K : ℝ) * B / 2) * (2 * (Real.sqrt 3 * σ) / 3)) := by
      symm
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos (by norm_num),
        ENNReal.ofReal_mul (Nat.cast_nonneg K)]
      simp
    _ = _ := congrArg ENNReal.ofReal hreal

end Paper35.Sharpness

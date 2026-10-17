import Paper35.GaussianMarked
import Paper35.CurveCalculus
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Tactic.Module

/-!
# Proposition 7.2: actual planar Gaussian convex hulls

The external geometric inputs are explicit classical propositions: the exact
published Gaussian face formula and Cauchy's deterministic support-function
formula for geometric perimeter. The Gaussian unit-projection and maximum
integral laws are the same classical inputs used by `GaussianMarked`.

The proof here supplies the change from the face integral to the actual marked
Gaussian probability, the paper's coefficient identification, rotational
invariance of support maxima, their absolute-moment Fubini justification,
the actual rank-two segment extreme points, and the elimination in (7.6).
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Paper35.PlanarPolytope
open Source GaussianMarked

abbrev Plane := Space 2
abbrev Cloud (K : ℕ) := Fin K → Plane

def cloudLaw (K : ℕ) : Measure (Cloud K) := Measure.pi (fun _ => standardGaussian 2)
instance (K : ℕ) : IsProbabilityMeasure (cloudLaw K) := by unfold cloudLaw; infer_instance

/-- The actual planar convex hull, rather than a surrogate crossing count. -/
def hull {K : ℕ} (Z : Cloud K) : Set Plane := convexHull ℝ (range Z)

def vertexCount {K : ℕ} (Z : Cloud K) : ℝ≥0∞ := ((hull Z).extremePoints ℝ).encard

lemma vertices_finite {K : ℕ} (Z : Cloud K) : ((hull Z).extremePoints ℝ).Finite :=
  (finite_range Z).subset extremePoints_convexHull_subset

/-- Geometric perimeter: boundary length for a polygon and twice the diameter
for an actual segment or point (the doubled-segment convention). -/
def perimeter (P : Set Plane) : ℝ := by
  classical
  exact if ∃ x y : Plane, P = segment ℝ x y then 2 * Metric.diam P
    else (Measure.hausdorffMeasure 1 (frontier P)).toReal

def circle (t : ℝ) : Plane := WithLp.toLp 2 ![Real.cos t, Real.sin t]

lemma continuous_circle : Continuous circle := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun i => Fin.cases Real.continuous_cos
    (fun j => Fin.cases Real.continuous_sin (fun k => Fin.elim0 k) j) i)

lemma norm_circle (t : ℝ) : ‖circle t‖ = 1 := by
  have hs : ‖circle t‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_two]
    change ‖Real.cos t‖^2 + ‖Real.sin t‖^2 = 1
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq t]
  nlinarith [norm_nonneg (circle t)]

def support {K : ℕ} (hK : 0 < K) (Z : Cloud K) (t : ℝ) : ℝ :=
  CurveCalculus.finiteSup hK (fun j => inner ℝ (Z j) (circle t))

lemma continuous_support {K : ℕ} (hK : 0 < K) :
    Continuous (fun z : ℝ × Cloud K => support hK z.2 z.1) := by
  unfold support CurveCalculus.finiteSup
  apply Continuous.finset_sup'_apply
  intro i hi
  exact ((continuous_apply i).comp continuous_snd).inner (continuous_circle.comp continuous_fst)

/-- Exact specialized published face-number input. Kabluchko--Zaporozhets,
arXiv:1704.04968v3, Theorem 1.4, equation (1.25), p. 9, with d=2,k=0.
Their g_n(1/2) is the integral below by equation (1.7). This input contains
only the actual Gaussian convex hull and its classical face count, no c_K,
maxout, or upper-envelope crossing identity. The rank-two segment is separate.
The usual measurability of the random face count, implicit in the published
expectation statement, is recorded explicitly alongside that statement.
https://arxiv.org/pdf/1704.04968 -/
def ClassicalGaussianFaceLaw : Prop :=
  ∀ K : ℕ, 3 ≤ K →
    AEMeasurable vertexCount (cloudLaw K) ∧
      (∫⁻ Z, vertexCount Z ∂cloudLaw K) = ENNReal.ofReal ((K : ℝ)*((K : ℝ)-1)) *
        ∫⁻ y, normalCDF (Real.sqrt (1/2)*y)^(K-2) ∂gaussianReal 0 1

/-- Exact deterministic finite-cloud specialization of Cauchy's support-function
formula. Alexander--Berg--Foote (2005), Rocky Mountain J. Math. 35(6),
pp. 1825--1826, equations (1.2)--(1.3). The degenerate case is the usual
continuous extension giving twice the length of a segment.
https://persweb.wabash.edu/facstaff/footer/papers/abfinrmj.pdf -/
def CauchyPerimeterLaw : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (Z : Cloud K),
    perimeter (hull Z) = ∫ t in Icc 0 (2*Real.pi), support hK Z t

lemma scaled_standard_halfGaussian :
    (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt (1/2)*y) = gaussianReal 0 (1/2) := by
  rw [gaussianReal_map_const_mul]
  congr 2
  · simp
  · apply NNReal.coe_injective
    simp only [NNReal.coe_mk, mul_one]
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/2)]

lemma faceIntegral_eq_visibility (K : ℕ) :
    (∫⁻ y, normalCDF (Real.sqrt (1/2)*y)^(K-2) ∂gaussianReal 0 1) =
      visibilityProbability (K-2) := by
  have hF : Measurable normalCDF := (show Monotone normalCDF from
    fun _ _ h => measure_mono (Iic_subset_Iic.mpr h)).measurable
  unfold visibilityProbability
  rw [← scaled_standard_halfGaussian, lintegral_map (hF.pow_const _) (by fun_prop)]

/-- The classical Gaussian face formula yields the paper's exact rank
coefficient by the independently proved marked-probability identity. -/
theorem expected_vertices_eq_coefficient_of_three_le (hface : ClassicalGaussianFaceLaw)
    (hmax : GaussianMaxIntegralLaw) (K : ℕ) (hK : 3 ≤ K) :
    (∫⁻ Z, vertexCount Z ∂cloudLaw K) =
      ENNReal.ofReal (2*Real.pi) * ENNReal.ofReal (Paper35.gaussianRankCoefficient K) := by
  rw [(hface K hK).2, faceIntegral_eq_visibility]
  rw [← marked_coefficient_eq_gaussianRankCoefficient hmax K (by omega)]
  have hchoose : ENNReal.ofReal ((K : ℝ)*((K : ℝ)-1)) = (K.choose 2 : ℝ≥0∞)*2 := by
    rw [show (K.choose 2 : ℝ≥0∞)*2 = ENNReal.ofReal ((K.choose 2 : ℝ)*2) by
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ K.choose 2)]
      norm_num]
    congr 1
    rw [Nat.cast_choose_two]
    ring
  rw [hchoose]
  have hπ : ENNReal.ofReal (2*Real.pi) * ENNReal.ofReal (1/Real.pi) = 2 := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*Real.pi)]
    norm_num [Real.pi_ne_zero]
  calc
    _ = (K.choose 2 : ℝ≥0∞) *
        (ENNReal.ofReal (2*Real.pi) * ENNReal.ofReal (1/Real.pi)) * visibilityProbability (K-2) := by rw [hπ]
    _ = _ := by ac_rfl

lemma measurable_support {K : ℕ} (hK : 0 < K) (t : ℝ) :
    Measurable (fun Z : Cloud K => support hK Z t) :=
  ((continuous_support hK).comp (continuous_const.prodMk continuous_id)).measurable

/-- Rotational invariance is used only through the classical one-dimensional
unit projection law. Independence then gives the actual maximum distribution. -/
theorem support_law (hproj : GaussianUnitProjectionLaw) (n : ℕ) (t : ℝ) :
    (cloudLaw (n+1)).map (fun Z => support (Nat.succ_pos n) Z t) =
      Paper35.standardNormalSequence.map (Paper35.prefixMax n) := by
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply (measurable_support _ t) measurableSet_Iic,
    Measure.map_apply (Paper35.continuous_prefixMax n).measurable measurableSet_Iic]
  change cloudLaw (n+1) {Z | support (Nat.succ_pos n) Z t ≤ y} =
    Paper35.standardNormalSequence {x | Paper35.prefixMax n x ≤ y}
  rw [Paper35.prefixMax_distribution]
  have hevent : {Z : Cloud (n+1) | support (Nat.succ_pos n) Z t ≤ y} =
      Set.pi univ (fun _ : Fin (n+1) => (fun z : Plane => inner ℝ z (circle t)) ⁻¹' Iic y) := by
    ext Z
    simp [support, CurveCalculus.finiteSup, Finset.sup'_le_iff]
  rw [hevent, cloudLaw, Measure.pi_pi]
  have hprojmeas : Measurable (fun z : Plane => inner ℝ z (circle t)) := by fun_prop
  simp_rw [← Measure.map_apply hprojmeas measurableSet_Iic, hproj 2 (circle t) (norm_circle t)]
  simp

theorem support_identDistrib (hproj : GaussianUnitProjectionLaw) (n : ℕ) (t : ℝ) :
    IdentDistrib (fun Z => support (Nat.succ_pos n) Z t) (Paper35.prefixMax n)
      (cloudLaw (n+1)) Paper35.standardNormalSequence :=
  ⟨(measurable_support _ t).aemeasurable, (Paper35.continuous_prefixMax n).measurable.aemeasurable,
    support_law hproj n t⟩

lemma integral_support (hproj : GaussianUnitProjectionLaw) (n : ℕ) (t : ℝ) :
    (∫ Z, support (Nat.succ_pos n) Z t ∂cloudLaw (n+1)) = Paper35.gaussianMaxMean (n+1) :=
  (support_identDistrib hproj n t).integral_eq

lemma integrable_support (hproj : GaussianUnitProjectionLaw) (n : ℕ) (t : ℝ) :
    Integrable (fun Z => support (Nat.succ_pos n) Z t) (cloudLaw (n+1)) :=
  (support_identDistrib hproj n t).integrable_iff.mpr (Paper35.integrable_prefixMax n)

/-- Own Fubini justification: all support maxima have the same integrable
one-dimensional Gaussian-maximum distribution, so their absolute first moments
are constant in direction. -/
lemma integrable_support_joint (hproj : GaussianUnitProjectionLaw) (n : ℕ) :
    Integrable (fun z : ℝ × Cloud (n+1) => support (Nat.succ_pos n) z.2 z.1)
      ((volume.restrict (Icc 0 (2*Real.pi))).prod (cloudLaw (n+1))) := by
  apply (integrable_prod_iff (continuous_support (Nat.succ_pos n)).measurable.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (integrable_support hproj n)
  · have heq : (fun t : ℝ => ∫ Z, ‖support (Nat.succ_pos n) Z t‖ ∂cloudLaw (n+1)) =
        (fun _ : ℝ => ∫ x, ‖Paper35.prefixMax n x‖ ∂Paper35.standardNormalSequence) := by
      funext t
      exact (support_identDistrib hproj n t).norm.integral_eq
    rw [heq]
    exact integrable_const _

/-- Cauchy's deterministic formula plus own rotation and Fubini steps yield
the expected geometric perimeter, including the doubled-segment convention. -/
theorem expected_perimeter_eq (hCauchy : CauchyPerimeterLaw)
    (hproj : GaussianUnitProjectionLaw) (K : ℕ) (hK : 0 < K) :
    (∫ Z, perimeter (hull Z) ∂cloudLaw K) = 2*Real.pi*Paper35.gaussianMaxMean K := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  simp_rw [hCauchy (n+1) (Nat.succ_pos n)]
  have H := integral_integral_swap (μ := volume.restrict (Icc 0 (2*Real.pi)))
    (ν := cloudLaw (n+1)) (f := fun t Z => support (Nat.succ_pos n) Z t)
    (integrable_support_joint hproj n)
  dsimp only at H
  rw [← H]
  simp_rw [integral_support hproj n]
  simp [Real.pi_pos.le, mul_comm]

/-- Eliminate the actual maximum mean to obtain the planar relation (7.6). -/
theorem expected_vertices_eq_scaled_perimeter_of_three_le (hface : ClassicalGaussianFaceLaw)
    (hmax : GaussianMaxIntegralLaw) (hCauchy : CauchyPerimeterLaw)
    (hproj : GaussianUnitProjectionLaw) (K : ℕ) (hK : 3 ≤ K) :
    (∫⁻ Z, vertexCount Z ∂cloudLaw K) =
      ENNReal.ofReal ((1/Real.sqrt Real.pi) * ∫ Z, perimeter (hull Z) ∂cloudLaw K) := by
  rw [expected_vertices_eq_coefficient_of_three_le hface hmax K hK, expected_perimeter_eq hCauchy hproj K (by omega)]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*Real.pi)]
  congr 1
  unfold Paper35.gaussianRankCoefficient
  ring

lemma left_mem_extremePoints_segment (x y : Plane) :
    x ∈ (segment ℝ x y).extremePoints ℝ := by
  by_cases hxy : x = y
  · subst y
    simp
  refine ⟨left_mem_segment ℝ x y, ?_⟩
  intro u hu v hv hx
  rw [segment_eq_image'] at hu hv
  obtain ⟨a,ha,rfl⟩ := hu
  obtain ⟨b,hb,rfl⟩ := hv
  rw [openSegment_eq_image] at hx
  obtain ⟨c,hc,hcvec⟩ := hx
  dsimp only at hcvec
  have hvec : ((1-c)*a+c*b) • (y-x) = (0 : Plane) := by
    calc
      _ = ((1-c) • (x+a • (y-x)) + c • (x+b • (y-x))) - x := by module
      _ = 0 := by rw [hcvec, sub_self]
  have hab : (1-c)*a+c*b = 0 :=
    (smul_eq_zero.mp hvec).resolve_right (sub_ne_zero.mpr (Ne.symm hxy))
  have ha0 : a = 0 := by nlinarith [ha.1,hb.1,hc.1,hc.2]
  simp [ha0]

lemma extremePoints_segment (x y : Plane) :
    (segment ℝ x y).extremePoints ℝ = {x,y} := by
  apply subset_antisymm
  · simpa only [convexHull_pair] using
      (extremePoints_convexHull_subset (𝕜 := ℝ) (A := ({x,y} : Set Plane)))
  · intro z hz
    rcases (show z = x ∨ z = y from by simpa using hz) with hz | hz
    · rw [hz]
      exact left_mem_extremePoints_segment x y
    · rw [hz, segment_symm]
      exact left_mem_extremePoints_segment y x

lemma vertexCount_two (Z : Cloud 2) (hZ : Z 0 ≠ Z 1) : vertexCount Z = 2 := by
  have hcloud : range Z = {Z 0,Z 1} := by
    ext z
    simp [Fin.exists_fin_two, eq_comm]
  simp only [vertexCount, hull, hcloud, convexHull_pair, extremePoints_segment, Set.encard_pair hZ]
  norm_num

/-- The rank-two geometric perimeter is pointwise exactly the usual doubled
segment length, also when the two points coincide. -/
theorem perimeter_hull_two (Z : Cloud 2) : perimeter (hull Z) = 2 * dist (Z 0) (Z 1) := by
  have hcloud : range Z = {Z 0,Z 1} := by
    ext z
    simp [Fin.exists_fin_two, eq_comm]
  have hseg : hull Z = segment ℝ (Z 0) (Z 1) := by rw [hull,hcloud,convexHull_pair]
  rw [perimeter, if_pos ⟨Z 0,Z 1,hseg⟩, hull, hcloud, convexHull_diam, Metric.diam_pair]

lemma standardGaussian_noAtoms (hproj : GaussianUnitProjectionLaw) : NoAtoms (standardGaussian 2) := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  constructor
  intro z
  have hnull : (standardGaussian 2) ((fun w : Plane => inner ℝ w (circle 0)) ⁻¹'
      {inner ℝ z (circle 0)}) = 0 := by
    rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      hproj 2 (circle 0) (norm_circle 0)]
    exact measure_singleton _
  apply measure_mono_null _ hnull
  intro w hw
  have hw' := mem_singleton_iff.mp hw
  subst w
  rfl

lemma ae_cloud_two_distinct (hproj : GaussianUnitProjectionLaw) :
    ∀ᵐ Z ∂cloudLaw 2, Z 0 ≠ Z 1 := by
  letI := standardGaussian_noAtoms hproj
  have hpair : ∀ᵐ z ∂(standardGaussian 2).prod (standardGaussian 2), z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    exact Filter.Eventually.of_forall (fun x => by
      rw [ae_iff]
      simp)
  have hmap := (measurePreserving_piFinTwo (fun _ : Fin 2 => standardGaussian 2)).map_eq
  have H : ∀ᵐ z ∂(cloudLaw 2).map (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Plane)), z.1 ≠ z.2 := by
    rw [cloudLaw, hmap]
    exact hpair
  exact (ae_map_iff (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Plane)).measurable.aemeasurable
    (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mp H

/-- The two-point case is proved as an actual random segment, separately from
the full-dimensional Gaussian face-number theorem. -/
theorem expected_vertices_two (hproj : GaussianUnitProjectionLaw) :
    (∫⁻ Z, vertexCount Z ∂cloudLaw 2) = 2 := by
  calc
    _ = ∫⁻ _Z, (2 : ℝ≥0∞) ∂cloudLaw 2 := by
      apply lintegral_congr_ae
      filter_upwards [ae_cloud_two_distinct hproj] with Z hZ
      exact vertexCount_two Z hZ
    _ = 2 := by simp

/-- The geometric perimeter has a genuine finite expectation; Fubini is
justified above using absolute moments, not merely formal iterated integrals. -/
theorem integrable_perimeter (hCauchy : CauchyPerimeterLaw)
    (hproj : GaussianUnitProjectionLaw) (K : ℕ) (hK : 0 < K) :
    Integrable (fun Z => perimeter (hull Z)) (cloudLaw K) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  convert (integrable_support_joint hproj n).integral_prod_right using 1
  funext Z
  exact hCauchy (n+1) (Nat.succ_pos n) Z

/-- Full first identity in (7.5), including the separately proved rank-two
segment case. -/
theorem expected_vertices_eq_coefficient (hface : ClassicalGaussianFaceLaw)
    (hmax : GaussianMaxIntegralLaw) (hproj : GaussianUnitProjectionLaw)
    (K : ℕ) (hK : 2 ≤ K) :
    (∫⁻ Z, vertexCount Z ∂cloudLaw K) =
      ENNReal.ofReal (2*Real.pi) * ENNReal.ofReal (Paper35.gaussianRankCoefficient K) := by
  by_cases htwo : K = 2
  · subst K
    rw [expected_vertices_two hproj, Paper35.gaussianRankCoefficient_two,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*Real.pi)]
    norm_num [Real.pi_ne_zero]
  · exact expected_vertices_eq_coefficient_of_three_le hface hmax K (by omega)

theorem expected_vertices_eq_maxMean (hface : ClassicalGaussianFaceLaw)
    (hmax : GaussianMaxIntegralLaw) (hproj : GaussianUnitProjectionLaw)
    (K : ℕ) (hK : 2 ≤ K) :
    (∫⁻ Z, vertexCount Z ∂cloudLaw K) =
      ENNReal.ofReal (2*Real.sqrt Real.pi*Paper35.gaussianMaxMean K) := by
  rw [expected_vertices_eq_coefficient hface hmax hproj K hK,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*Real.pi)]
  congr 1
  unfold Paper35.gaussianRankCoefficient
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [← mul_div_assoc]
  apply (div_eq_iff hs).mpr
  have hsq := Real.sq_sqrt Real.pi_pos.le
  nlinarith [congrArg (fun r : ℝ => 2 * Paper35.gaussianMaxMean K * r) hsq]

/-- Complete planar elimination identity (7.6), for every original K≥2. -/
theorem expected_vertices_eq_scaled_perimeter (hface : ClassicalGaussianFaceLaw)
    (hmax : GaussianMaxIntegralLaw) (hCauchy : CauchyPerimeterLaw)
    (hproj : GaussianUnitProjectionLaw) (K : ℕ) (hK : 2 ≤ K) :
    (∫⁻ Z, vertexCount Z ∂cloudLaw K) =
      ENNReal.ofReal ((1/Real.sqrt Real.pi) * ∫ Z, perimeter (hull Z) ∂cloudLaw K) := by
  rw [expected_vertices_eq_coefficient hface hmax hproj K hK,
    expected_perimeter_eq hCauchy hproj K (by omega)]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*Real.pi)]
  congr 1
  unfold Paper35.gaussianRankCoefficient
  ring

lemma vertexCount_ne_top {K : ℕ} (Z : Cloud K) : vertexCount Z ≠ ∞ :=
  ENat.toENNReal_ne_top.mpr (vertices_finite Z).encard_lt_top.ne

theorem aemeasurable_vertexCount (hface : ClassicalGaussianFaceLaw)
    (hproj : GaussianUnitProjectionLaw) (K : ℕ) (hK : 2 ≤ K) :
    AEMeasurable vertexCount (cloudLaw K) := by
  by_cases htwo : K = 2
  · subst K
    apply (measurable_const : Measurable (fun _ : Cloud 2 => (2 : ℝ≥0∞))).aemeasurable.congr
    filter_upwards [ae_cloud_two_distinct hproj] with Z hZ
    exact (vertexCount_two Z hZ).symm
  · exact (hface K (by omega)).1

/-- The real-valued source expectation is finite and equals the same coefficient,
not merely the `toReal` of a potentially nonmeasurable count. -/
theorem expected_vertices_real_eq_coefficient (hface : ClassicalGaussianFaceLaw)
    (hmax : GaussianMaxIntegralLaw) (hproj : GaussianUnitProjectionLaw)
    (K : ℕ) (hK : 2 ≤ K) :
    (∫ Z, (vertexCount Z).toReal ∂cloudLaw K) = 2*Real.pi*Paper35.gaussianRankCoefficient K := by
  rw [integral_toReal (aemeasurable_vertexCount hface hproj K hK)
    (Filter.Eventually.of_forall (fun Z => (vertexCount_ne_top Z).lt_top)),
    expected_vertices_eq_coefficient hface hmax hproj K hK]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.pi),
    ENNReal.toReal_ofReal (Paper35.gaussianRankCoefficient_nonneg K)]

/-- Proposition 7.2 in the source's real expectation form, for the actual
convex-hull extreme-point count and geometric perimeter. -/
theorem planar_gaussian_polytope_identities (hface : ClassicalGaussianFaceLaw)
    (hmax : GaussianMaxIntegralLaw) (hCauchy : CauchyPerimeterLaw)
    (hproj : GaussianUnitProjectionLaw) (K : ℕ) (hK : 2 ≤ K) :
    (∫ Z, (vertexCount Z).toReal ∂cloudLaw K) = 2*Real.pi*Paper35.gaussianRankCoefficient K ∧
    (∫ Z, perimeter (hull Z) ∂cloudLaw K) = 2*Real.pi*Paper35.gaussianMaxMean K ∧
    (∫ Z, (vertexCount Z).toReal ∂cloudLaw K) =
      (1/Real.sqrt Real.pi) * ∫ Z, perimeter (hull Z) ∂cloudLaw K := by
  refine ⟨expected_vertices_real_eq_coefficient hface hmax hproj K hK,
    expected_perimeter_eq hCauchy hproj K (by omega), ?_⟩
  rw [expected_vertices_real_eq_coefficient hface hmax hproj K hK,
    expected_perimeter_eq hCauchy hproj K (by omega)]
  unfold Paper35.gaussianRankCoefficient
  ring

end Paper35.PlanarPolytope

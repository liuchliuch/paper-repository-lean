import Paper35.GaussianSpectrum
import Paper35.RandomCount

/-!
# Independent anisotropic Gaussian parameters in the original sample law

The arbitrary Gaussian weight law and independent scalar Gaussian bias are
transported from the actual standard finite Gaussian product. Their original
affine score counts are preserved after removing the common mean. The PSD
covariance operator norm is proved to be its greatest real eigenvalue and the
square of the principal-root operator norm. These bridges establish the full
Corollary 2.9 bound, fixed-rank supremum and isotropic universal optimality,
using only the previously declared classical inputs for Gaussian representation
and the proved spherical upper-envelope assembly.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace Paper35.GaussianIndependent
open Source GaussianLift GaussianMarked
variable {d : ℕ}

def drop (z : Space (d+1)) : Space d := WithLp.toLp 2 (fun i => z i.castSucc)
def split (z : Space (d+1)) : Candidate d := (drop z, z (Fin.last d))

lemma measurable_drop (d : ℕ) : Measurable (drop (d := d)) :=
  (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
    (measurable_pi_iff.mpr (fun _ => by fun_prop))
lemma measurable_split (d : ℕ) : Measurable (split (d := d)) :=
  (measurable_drop d).prodMk (by fun_prop)

/-- The independent horizontal and last-coordinate Gaussian factors are
proved from the actual finite product law. -/
theorem standardGaussian_split (d : ℕ) :
    (standardGaussian (d+1)).map split = (standardGaussian d).prod (gaussianReal 0 1) := by
  let μ : Measure (Fin d → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let ν : Measure (Fin (d+1) → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) (Fin.last d)
  have he : ν.map e = (gaussianReal 0 1).prod μ := by
    simpa only [ν, μ] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => gaussianReal 0 1) (Fin.last d)).map_eq
  have hsplit : (split ∘ (WithLp.toLp 2 : (Fin (d+1) → ℝ) → Space (d+1))) =
      (fun q : ℝ × (Fin d → ℝ) => (WithLp.toLp 2 q.2, q.1)) ∘ e := by
    funext z
    simp [split, drop, e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    rfl
  change (ν.map (WithLp.toLp 2)).map split = (μ.map (WithLp.toLp 2)).prod (gaussianReal 0 1)
  rw [Measure.map_map (measurable_split d) (WithLp.measurable_toLp 2 _), hsplit,
    ← Measure.map_map (by fun_prop) e.measurable, he]
  have hs : (fun q : ℝ × (Fin d → ℝ) => (WithLp.toLp 2 q.2, q.1)) =
      (Prod.map (WithLp.toLp 2) id) ∘ Prod.swap := rfl
  rw [hs, ← Measure.map_map (by fun_prop) measurable_swap, Measure.prod_swap,
    ← Measure.map_prod_map _ _ (WithLp.measurable_toLp 2 _) measurable_id, Measure.map_id]

lemma bias_affine_law (μ σ : ℝ) :
    (gaussianReal 0 1).map (fun z => μ+σ*z) = gaussianReal μ ⟨σ^2, sq_nonneg _⟩ := by
  rw [show (fun z : ℝ => μ+σ*z) = (fun z => μ+z) ∘ (fun z => σ*z) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  simp

/-- Original independent Gaussian weight and scalar bias model. -/
structure Model (d : ℕ) where
  weights : GaussianLift.Model d
  biasMean : ℝ
  biasStd : ℝ
  biasStd_pos : 0 < biasStd

namespace Model

def joint (g : Model d) : Measure (Candidate d) :=
  g.weights.law.prod (gaussianReal g.biasMean ⟨g.biasStd^2, sq_nonneg _⟩)
instance (g : Model d) : IsProbabilityMeasure g.joint := by
  unfold joint
  infer_instance

def sampleLaw (g : Model d) (K : ℕ) : Measure (Fin K → Candidate d) :=
  Measure.pi (fun _ => g.joint)
instance (g : Model d) (K : ℕ) : IsProbabilityMeasure (g.sampleLaw K) := by
  unfold sampleLaw
  infer_instance

def canonicalSample (g : Model d) (z : Space (d+1)) : Candidate d :=
  (g.weights.mean + rootMap g.weights.covariance (drop z), g.biasMean + g.biasStd*z (Fin.last d))

/-- Any independent Gaussian weight and bias on any probability space have
exactly this original product law, so the source model imposes no coupling. -/
theorem joint_eq_of_independent {Ω : Type*} [MeasurableSpace Ω]
    (g : Model d) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Space d) (b : Ω → ℝ) (hWm : AEMeasurable W μ) (hbm : AEMeasurable b μ)
    (hInd : IndepFun W b μ) (hW : μ.map W = g.weights.law)
    (hb : μ.map b = gaussianReal g.biasMean ⟨g.biasStd^2, sq_nonneg _⟩) :
    μ.map (fun ω => (W ω, b ω)) = g.joint := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map hWm hbm).mp hInd, hW, hb]
  rfl

lemma measurable_canonicalSample (g : Model d) : Measurable g.canonicalSample := by
  unfold canonicalSample
  exact (measurable_const.add ((rootMap _).continuous.measurable.comp (measurable_drop d))).prodMk
    (by fun_prop)

/-- The original independent law equals the actual canonical Gaussian linear
image. Only the existing generic Gaussian representation theorem is used. -/
theorem joint_eq_map (hrep : GaussianRepresentationLaw) (g : Model d) :
    g.joint = (standardGaussian (d+1)).map g.canonicalSample := by
  rw [joint, hrep d g.weights, ← bias_affine_law g.biasMean g.biasStd,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), ← standardGaussian_split d,
    Measure.map_map (by fun_prop) (measurable_split d)]
  rfl

theorem sampleLaw_eq_map (hrep : GaussianRepresentationLaw) (g : Model d) (K : ℕ) :
    g.sampleLaw K = (gaussianIid (d+1) K).map (fun Z j => g.canonicalSample (Z j)) := by
  have h := Measure.pi_map_pi (μ := fun _ : Fin K => standardGaussian (d+1))
    (f := fun _ => g.canonicalSample) (fun _ => g.measurable_canonicalSample.aemeasurable)
  simp_rw [← g.joint_eq_map hrep] at h
  exact h.symm

lemma inner_drop_append (z : Space (d+1)) (x : Space d) (b : ℝ) :
    inner ℝ z (GaussianAnisotropic.append x b) = inner ℝ (drop z) x+z (Fin.last d)*b := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_castSucc,
    GaussianAnisotropic.append, drop, WithLp.ofLp_toLp, star_trivial]
  simp [mul_comm]

lemma canonical_score (g : Model d) (z : Space (d+1)) (x : Space d) :
    inner ℝ (g.canonicalSample z).1 x+(g.canonicalSample z).2 =
      (inner ℝ g.weights.mean x+g.biasMean) +
        inner ℝ z (GaussianAnisotropic.lift (rootMap g.weights.covariance) g.biasStd x) := by
  simp only [canonicalSample, inner_add_left, GaussianAnisotropic.lift, inner_drop_append]
  have hs : inner ℝ ((rootMap g.weights.covariance) (drop z)) x =
      inner ℝ (drop z) ((rootMap g.weights.covariance) x) :=
    rootMap_symmetric g.weights.covariance (drop z) x
  rw [hs]
  ring

def expectedCount (g : Model d) (K : ℕ) (p : Probe d) : ℝ≥0∞ :=
  expectedSwitchCount (g.sampleLaw K) (Source.WeightedModel.scores p) p.length

/-- Transport of actual source switch counts removes precisely the common
Gaussian mean, while retaining the original independent sample law. -/
theorem expectedCount_eq_canonical (hrep : GaussianRepresentationLaw) (g : Model d)
    (K : ℕ) (p : Probe d)
    (hLN : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ) :
    g.expectedCount K p = GaussianSharpness.expectedCount
      (rootMap g.weights.covariance) g.biasStd K p := by
  have hm := RandomCount.measurable_affineSwitchCount p.curve p.length p.length_pos
    p.lipschitz.continuousOn hLN
  have hma : AEMeasurable (fun θ : Fin K → Candidate d =>
      switchCount (Source.WeightedModel.scores p θ) p.length) (g.sampleLaw K) := hm.aemeasurable
  rw [g.sampleLaw_eq_map hrep K] at hma
  unfold expectedCount expectedSwitchCount
  rw [g.sampleLaw_eq_map hrep K,
    lintegral_map' hma (measurable_pi_iff.mpr fun j =>
      g.measurable_canonicalSample.comp (measurable_pi_apply j)).aemeasurable]
  apply lintegral_congr
  intro Z
  have hs : Source.WeightedModel.scores p (fun j => g.canonicalSample (Z j)) =
      fun j s => (inner ℝ g.weights.mean (p.curve s)+g.biasMean) +
        1 * GaussianSharpness.liftedScores (rootMap g.weights.covariance) g.biasStd p Z j s := by
    funext j s
    simpa only [Source.WeightedModel.scores, GaussianSharpness.liftedScores, one_mul]
      using g.canonical_score (Z j) (p.curve s)
  rw [hs]
  exact Gaussian.switchCount_affine _ _ _ (fun _ => zero_lt_one) p.length

def expectedDensity (g : Model d) (K : ℕ) (p : Probe d) : ℝ :=
  (g.expectedCount K p).toReal / p.length

theorem expectedDensity_source (g : Model d) (K : ℕ) (p : Probe d) :
    g.expectedDensity K p =
      (∫⁻ θ, switchDensity (Source.WeightedModel.scores p θ) p.length ∂g.sampleLaw K).toReal := by
  unfold expectedDensity expectedCount expectedSwitchCount switchDensity
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const' _ _
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr p.length_pos))]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal p.length_pos.le]

lemma expectedDensity_eq_canonical (hrep : GaussianRepresentationLaw) (g : Model d)
    (K : ℕ) (p : Probe d)
    (hLN : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ) :
    g.expectedDensity K p = GaussianSharpness.expectedDensity
      (rootMap g.weights.covariance) g.biasStd K p := by
  unfold expectedDensity GaussianSharpness.expectedDensity
  rw [g.expectedCount_eq_canonical hrep K p hLN]

end Model

namespace Model

/-- The original source's anisotropic normalized feature map (2.20). -/
def psi (g : Model d) (x : Space d) : Space (d+1) :=
  GaussianSharpness.normalizedMap (rootMap g.weights.covariance) g.biasStd x

lemma psi_formula (g : Model d) (x : Space d) :
    g.psi x = (Real.sqrt (g.biasStd^2+GaussianLift.covarianceForm g.weights.covariance x))⁻¹ •
      GaussianAnisotropic.append (rootMap g.weights.covariance x) g.biasStd := by
  unfold psi GaussianSharpness.normalizedMap Gaussian.normalize GaussianAnisotropic.lift
  congr 2
  rw [← norm_rootMap_sq _ g.weights.covariance_psd]
  have he := GaussianAnisotropic.norm_append_sq (rootMap g.weights.covariance x) g.biasStd
  have he' : ‖GaussianAnisotropic.append (rootMap g.weights.covariance x) g.biasStd‖^2 =
      g.biasStd^2+‖rootMap g.weights.covariance x‖^2 := he.trans (add_comm _ _)
  rw [← he', Real.sqrt_sq (norm_nonneg _)]

section ClassicalInputs
variable
    (hrep : GaussianRepresentationLaw)
    (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw)
    (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw)
    (hmax : GaussianMaxIntegralLaw)
include hrep hcrofton hregular hproj hrot hmax

/-- Formula (2.19) for the actual independent weight/bias Gaussian law,
using precisely the anisotropic map (2.20). -/
theorem independent_spherical_length (g : Model d) (hd : 1 ≤ d)
    (K : ℕ) (hK : 2 ≤ K) (p : Probe d)
    (hLNsource : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ)
    (hLNmark : ∀ q : Probe d, VisibleCrossing.LusinNovikovInput
      (MarkSample (d+1) (K-2)) (CurveParameter q.length)) :
    g.expectedCount K p = ENNReal.ofReal (gaussianRankCoefficient K) *
      sphericalLength (fun s => g.psi (p.curve s)) p.length := by
  rw [g.expectedCount_eq_canonical hrep K p hLNsource]
  exact GaussianSharpness.countLengthIdentity_of_classicalInputs
    (rootMap g.weights.covariance) g.biasStd_pos hd K hK
    hcrofton hregular hproj hrot hmax hLNmark p

theorem independent_spherical_metric_length (g : Model d) (hd : 1 ≤ d)
    (K : ℕ) (hK : 2 ≤ K) (p : Probe d)
    (hlength : ACCurveLengthLaw)
    (hLNsource : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ)
    (hLNmark : ∀ q : Probe d, VisibleCrossing.LusinNovikovInput
      (MarkSample (d+1) (K-2)) (CurveParameter q.length)) :
    g.expectedCount K p = ENNReal.ofReal (gaussianRankCoefficient K) *
      eVariationOn (fun s => g.psi (p.curve s)) (Icc 0 p.length) := by
  rw [g.independent_spherical_length hrep hcrofton hregular hproj hrot hmax hd K hK p
    hLNsource hLNmark]
  unfold psi
  rw [sphericalLength_eq_eVariationOn hlength (d+1) p.length p.length_pos _
    (GaussianSharpness.normalized_probe_absolutelyContinuous
      (rootMap g.weights.covariance) g.biasStd_pos p)]

theorem expectedCount_finite (g : Model d) (hd : 1 ≤ d)
    (K : ℕ) (hK : 2 ≤ K) (p : Probe d)
    (hLNsource : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ)
    (hLNmark : ∀ q : Probe d, VisibleCrossing.LusinNovikovInput
      (MarkSample (d+1) (K-2)) (CurveParameter q.length)) :
    g.expectedCount K p < ∞ := by
  rw [g.expectedCount_eq_canonical hrep K p hLNsource]
  exact GaussianSharpness.expectedCount_finite _ g.biasStd_pos K
    (GaussianSharpness.countLengthIdentity_of_classicalInputs
      (rootMap g.weights.covariance) g.biasStd_pos hd K hK
      hcrofton hregular hproj hrot hmax hLNmark) p

/-- The original anisotropic bound (2.21), with arbitrary means, independent
Gaussian bias, and possibly singular weight covariance. -/
theorem expectedDensity_le_anisotropic (g : Model d) (hd : 1 ≤ d)
    (K : ℕ) (hK : 2 ≤ K) (p : Probe d)
    (hLNsource : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ)
    (hLNmark : ∀ q : Probe d, VisibleCrossing.LusinNovikovInput
      (MarkSample (d+1) (K-2)) (CurveParameter q.length)) :
    g.expectedDensity K p ≤ gaussianRankCoefficient K *
      (Real.sqrt (covarianceMax g.weights.covariance) / g.biasStd) := by
  rw [g.expectedDensity_eq_canonical hrep K p hLNsource,
    GaussianSharpness.expectedDensity_eq_speed _ _ K
      (GaussianSharpness.countLengthIdentity_of_classicalInputs
        (rootMap g.weights.covariance) g.biasStd_pos hd K hK
        hcrofton hregular hproj hrot hmax hLNmark)]
  rw [← norm_rootMap_eq_sqrt _ g.weights.covariance_psd]
  exact mul_le_mul_of_nonneg_left
    (GaussianSharpness.probeSpeed_le _ g.biasStd_pos p) (gaussianRankCoefficient_nonneg K)

/-- The exact original-law supremum in (2.22). -/
theorem anisotropic_supremum (g : Model d)
    (hpositive : 0 < covarianceMax g.weights.covariance)
    (K : ℕ) (hK : 2 ≤ K)
    (hLNsource : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ)
    (hLNmark : ∀ q : Probe d, VisibleCrossing.LusinNovikovInput
      (MarkSample (d+1) (K-2)) (CurveParameter q.length)) :
    (⨆ p : Probe d, ENNReal.ofReal (g.expectedDensity K p /
      (Real.sqrt (covarianceMax g.weights.covariance) / g.biasStd))) =
        ENNReal.ofReal (gaussianRankCoefficient K) := by
  have hA : rootMap g.weights.covariance ≠ 0 := by
    intro h
    have hh := norm_rootMap_squared _ g.weights.covariance_psd
    rw [h, norm_zero, zero_pow (by norm_num)] at hh
    linarith
  simp_rw [g.expectedDensity_eq_canonical hrep K _ hLNsource,
    ← norm_rootMap_eq_sqrt _ g.weights.covariance_psd]
  exact GaussianSharpness.gaussian_expectedDensity_supremum
    hcrofton hregular hproj hrot hmax (rootMap g.weights.covariance) hA g.biasStd_pos K hK hLNmark

/-- The Gaussian rank-linear coefficient is optimal on the original
independent source law, uniformly over every rank and positive-length probe. -/
theorem universal_rank_coefficient_iff (g : Model d) (hd : 1 ≤ d)
    (hpositive : 0 < covarianceMax g.weights.covariance) (C : ℝ)
    (hLNsource : ∀ K : ℕ, 2 ≤ K →
      VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ)
    (hLNmark : ∀ K : ℕ, 2 ≤ K → ∀ q : Probe d,
      VisibleCrossing.LusinNovikovInput (MarkSample (d+1) (K-2)) (CurveParameter q.length)) :
    (∀ K : ℕ, 2 ≤ K → ∀ p : Probe d, g.expectedDensity K p ≤
      C * ((K : ℝ)-1) * (Real.sqrt (covarianceMax g.weights.covariance) / g.biasStd)) ↔
        1 / Real.pi ≤ C := by
  have hr : 0 < Real.sqrt (covarianceMax g.weights.covariance) / g.biasStd :=
    div_pos (Real.sqrt_pos.2 hpositive) g.biasStd_pos
  constructor
  · intro hb
    have hs := g.anisotropic_supremum hrep hcrofton hregular hproj hrot hmax hpositive
      2 (by omega) (hLNsource 2 (by omega)) (hLNmark 2 (by omega))
    rw [gaussianRankCoefficient_two] at hs
    have hle : ENNReal.ofReal (1 / Real.pi) ≤ ENNReal.ofReal C := by
      rw [← hs]
      apply iSup_le
      intro p
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ hr).mpr
      have h := hb 2 (by omega) p
      norm_num at h
      exact h
    exact (ENNReal.ofReal_le_ofReal_iff'.mp hle).resolve_right
      (not_le.mpr (one_div_pos.mpr Real.pi_pos))
  · intro hC K hK p
    exact (g.expectedDensity_le_anisotropic hrep hcrofton hregular hproj hrot hmax hd K hK p
      (hLNsource K hK) (hLNmark K hK)).trans
      (mul_le_mul_of_nonneg_right ((gaussianRankCoefficient_uniform_bound_iff C).2 hC K hK) hr.le)

/-- The original isotropic estimate (2.24), including zero weight variance. -/
theorem expectedDensity_le_isotropic (g : Model d) (hd : 1 ≤ d)
    {s : ℝ} (hs : 0 ≤ s)
    (hcov : g.weights.covariance = s^2 • (1 : Matrix (Fin d) (Fin d) ℝ))
    (K : ℕ) (hK : 2 ≤ K) (p : Probe d)
    (hLNsource : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ)
    (hLNmark : ∀ q : Probe d, VisibleCrossing.LusinNovikovInput
      (MarkSample (d+1) (K-2)) (CurveParameter q.length)) :
    g.expectedDensity K p ≤ ((K : ℝ)-1) / Real.pi * (s / g.biasStd) := by
  have hb := g.expectedDensity_le_anisotropic hrep hcrofton hregular hproj hrot hmax hd K hK p
    hLNsource hLNmark
  rw [hcov, covarianceMax_isotropic hd, Real.sqrt_sq hs] at hb
  have hr := ((gaussianRankCoefficient_uniform_bound_iff (1 / Real.pi)).2 le_rfl) K hK
  have hr' : gaussianRankCoefficient K ≤ ((K : ℝ)-1) / Real.pi := by
    convert hr using 1; ring
  exact hb.trans (mul_le_mul_of_nonneg_right hr' (div_nonneg hs g.biasStd_pos.le))

/-- On every nondegenerate isotropic source, `1/pi` is the optimal universal
constant in precisely the original rank-linear normalization. -/
theorem isotropic_universal_coefficient_iff (g : Model d) (hd : 1 ≤ d)
    {s : ℝ} (hs : 0 < s)
    (hcov : g.weights.covariance = s^2 • (1 : Matrix (Fin d) (Fin d) ℝ)) (C : ℝ)
    (hLNsource : ∀ K : ℕ, 2 ≤ K →
      VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ)
    (hLNmark : ∀ K : ℕ, 2 ≤ K → ∀ q : Probe d,
      VisibleCrossing.LusinNovikovInput (MarkSample (d+1) (K-2)) (CurveParameter q.length)) :
    (∀ K : ℕ, 2 ≤ K → ∀ p : Probe d, g.expectedDensity K p ≤
      C * ((K : ℝ)-1) * (s / g.biasStd)) ↔ 1 / Real.pi ≤ C := by
  have hp : 0 < covarianceMax g.weights.covariance := by
    rw [hcov, covarianceMax_isotropic hd]
    exact sq_pos_of_pos hs
  have h := g.universal_rank_coefficient_iff hrep hcrofton hregular hproj hrot hmax hd hp C
    hLNsource hLNmark
  simpa only [hcov, covarianceMax_isotropic hd, Real.sqrt_sq hs.le] using h

end ClassicalInputs
end Model
end Paper35.GaussianIndependent

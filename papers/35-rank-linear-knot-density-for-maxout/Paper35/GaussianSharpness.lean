import Paper35.GaussianAnisotropic
import Paper35.SharpnessLimit
import Paper35.GaussianUpperEnvelope
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Gaussian shrinking-segment sharpness

For the actual iid standard Gaussian linear-image scores, this module proves
normalized straight-segment derivatives, continuity of their true spherical
speed, the shrinking average limit, the bound for every arclength probe,
operator-norm attainment, and the exact density supremum. The final count
statements instantiate the proved Lemma 6.2 assembly with its precise classical
inputs; no local intensity, limit, or sharpness formula is postulated.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace Paper35.GaussianSharpness
open Source GaussianAnisotropic
variable {d : ℕ}

def normalizedMap (A : Space d →L[ℝ] Space d) (σ : ℝ) (x : Space d) : Space (d+1) :=
  Gaussian.normalize (lift A σ x)

def lineSpeed (A : Space d →L[ℝ] Space d) (σ : ℝ) (v : Space d) (t : ℝ) : ℝ :=
  ‖Gaussian.normalizedVelocity (lift A σ (t • v)) (velocity A v)‖

lemma continuous_lineSpeed (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (v : Space d) : Continuous (lineSpeed A σ v) := by
  have hl : Continuous (fun t : ℝ => lift A σ (t • v)) :=
    (continuous_lift A σ).comp (continuous_id.smul continuous_const)
  have hn : ∀ t : ℝ, ‖lift A σ (t • v)‖ ≠ 0 :=
    fun t => norm_ne_zero_iff.mpr (lift_ne_zero A hσ _)
  unfold lineSpeed Gaussian.normalizedVelocity
  exact ((hl.norm.inv₀ hn).smul continuous_const |>.sub
    ((hl.inner continuous_const).div (hl.norm.pow 3) (fun t => pow_ne_zero _ (hn t))
      |>.smul hl)).norm

lemma lineSpeed_zero (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (v : Space d) : lineSpeed A σ v 0 = ‖A v‖ / σ := by
  have h := normalizedVelocity_sq A hσ ((0 : ℝ) • v) v
  change lineSpeed A σ v 0 ^ 2 = _ at h
  simp only [zero_smul] at h
  simp only [map_zero, norm_zero, inner_zero_left, zero_pow (by norm_num : 2 ≠ 0),
    add_zero, zero_div, sub_zero] at h
  have hn : 0 ≤ lineSpeed A σ v 0 := norm_nonneg _
  have hd : 0 ≤ ‖A v‖ / σ := div_nonneg (norm_nonneg _) hσ.le
  have heq : (‖A v‖ / σ)^2 = ‖A v‖^2 / σ^2 := div_pow _ _ _
  nlinarith

lemma lineSpeed_le (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    {v : Space d} (hv : ‖v‖ = 1) (t : ℝ) : lineSpeed A σ v t ≤ ‖A‖ / σ := by
  simpa only [lineSpeed, hv, mul_one] using normalizedVelocity_le A hσ (t • v) v

/-- The original centered axial segment, with its original Euclidean arclength. -/
def lineCurve (v : Space d) (ε s : ℝ) : Space d := (-ε / 2 + s) • v

lemma lineCurve_isometry {v : Space d} (hv : ‖v‖ = 1) (ε : ℝ) :
    Isometry (lineCurve v ε) := by
  apply isometry_iff_dist_eq.mpr
  intro s t
  simp only [lineCurve, dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.norm_eq_abs]
  congr 1
  ring

def lineProbe (v : Space d) (hv : ‖v‖ = 1) (ε : ℝ) (hε : 0 < ε) : Probe d where
  curve := lineCurve v ε
  length := ε
  length_pos := hε
  lipschitz := (lineCurve_isometry hv ε).lipschitz.lipschitzOnWith
  arclength := by
    have hid : eVariationOn (id : ℝ → ℝ) (Icc 0 ε) ≤ ENNReal.ofReal ε := by
      have h := (monotone_id.monotoneOn univ : MonotoneOn (id : ℝ → ℝ) univ).eVariationOn_le
        (a := 0) (b := ε) (mem_univ _) (mem_univ _)
      simpa only [univ_inter, id_eq, sub_zero] using h
    have h := (lineCurve_isometry hv ε).lipschitz.lipschitzOnWith.comp_eVariationOn_le
      (g := (id : ℝ → ℝ)) (s := Icc 0 ε) (mapsTo_univ _ _)
    have hle : eVariationOn (lineCurve v ε) (Icc 0 ε) ≤
        eVariationOn (id : ℝ → ℝ) (Icc 0 ε) := by simpa using h
    apply le_antisymm (hle.trans hid)
    have hlower := eVariationOn.edist_le (lineCurve v ε)
      (left_mem_Icc.mpr hε.le) (right_mem_Icc.mpr hε.le)
    have hed : edist (lineCurve v ε 0) (lineCurve v ε ε) = ENNReal.ofReal ε := by
      rw [(lineCurve_isometry hv ε).edist_eq]
      simp [edist_dist, Real.dist_eq, abs_of_nonneg hε.le]
    rwa [hed] at hlower

lemma lineCurve_hasDerivAt (v : Space d) (ε s : ℝ) :
    HasDerivAt (lineCurve v ε) v s := by
  simpa only [lineCurve, one_smul] using
    ((hasDerivAt_id s).const_add (-ε/2)).smul_const v

lemma normalized_line_hasDerivAt (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (v : Space d) (ε s : ℝ) :
    HasDerivAt (fun t => normalizedMap A σ (lineCurve v ε t))
      (Gaussian.normalizedVelocity (lift A σ (lineCurve v ε s)) (velocity A v)) s :=
  Gaussian.hasDerivAt_normalize (hasDerivAt_lift A σ (lineCurve_hasDerivAt v ε s))
    (lift_ne_zero A hσ _)

lemma normalized_line_speed (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (v : Space d) (ε s : ℝ) :
    ‖deriv (fun t => normalizedMap A σ (lineCurve v ε t)) s‖ =
      lineSpeed A σ v (-ε/2+s) := by
  rw [(normalized_line_hasDerivAt A hσ v ε s).deriv]
  rfl

/-- The true spherical length of the normalized centered line, in real form. -/
theorem sphericalLength_line (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (v : Space d) {ε : ℝ} (hε : 0 < ε) :
    GaussianMarked.sphericalLength (fun t => normalizedMap A σ (lineCurve v ε t)) ε =
      ENNReal.ofReal (∫ t in (-ε/2)..(ε/2), lineSpeed A σ v t) := by
  unfold GaussianMarked.sphericalLength
  simp_rw [normalized_line_speed A hσ]
  have hc : Continuous (fun s : ℝ => lineSpeed A σ v (-ε/2+s)) :=
    (continuous_lineSpeed A hσ v).comp (continuous_const.add continuous_id)
  rw [← ofReal_integral_eq_lintegral_ofReal hc.continuousOn.integrableOn_Icc
    (Eventually.of_forall fun _ => norm_nonneg _)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hε.le,
    intervalIntegral.integral_comp_add_left (lineSpeed A σ v) (-ε/2)]
  congr 1
  congr 1 <;> ring

/-- Actual spherical speed per Euclidean length on shrinking positive segments. -/
def centeredSpeed (A : Space d →L[ℝ] Space d) (σ : ℝ) (v : Space d) (ε : ℝ) : ℝ :=
  (GaussianMarked.sphericalLength (fun t => normalizedMap A σ (lineCurve v ε t)) ε).toReal / ε

theorem centeredSpeed_limit (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (v : Space d) :
    Tendsto (centeredSpeed A σ v) (𝓝[>] 0) (𝓝 (‖A v‖ / σ)) := by
  have h := Sharpness.tendsto_centered_average (continuous_lineSpeed A hσ v).measurable
    (continuous_lineSpeed A hσ v).continuousAt
  rw [lineSpeed_zero A hσ v] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  unfold centeredSpeed
  rw [sphericalLength_line A hσ v hε, ENNReal.toReal_ofReal]
  exact intervalIntegral.integral_nonneg (by have he : 0 < ε := hε; linarith) (fun _ _ => norm_nonneg _)

/-- The global bound is proved on every actual arclength probe. -/
theorem sphericalLength_probe_le (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (p : Probe d) :
    GaussianMarked.sphericalLength (fun t => normalizedMap A σ (p.curve t)) p.length ≤
      ENNReal.ofReal (‖A‖ / σ) * ENNReal.ofReal p.length := by
  have hd : ∀ᵐ s ∂volume, s ∈ Icc 0 p.length → DifferentiableAt ℝ p.curve s := by
    simpa only [ae_iff, Classical.not_imp] using
      Source.CrossingJacobian.nondifferentiable_null p
  have hdi : ∀ᵐ s ∂volume.restrict (Ioo 0 p.length), DifferentiableAt ℝ p.curve s := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hd] with s hs hsi
    exact hs (Ioo_subset_Icc_self hsi)
  unfold GaussianMarked.sphericalLength
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc : Ioo (0 : ℝ) p.length =ᵐ[volume] Icc 0 p.length)]
  calc
    _ ≤ ∫⁻ _s in Ioo 0 p.length, ENNReal.ofReal (‖A‖ / σ) := by
      apply lintegral_mono_ae
      filter_upwards [hdi, ae_restrict_mem measurableSet_Ioo] with s hs hsi
      have hnorm := Gaussian.hasDerivAt_normalize (hasDerivAt_lift A σ hs.hasDerivAt)
        (lift_ne_zero A hσ _)
      simp only [normalizedMap]
      rw [hnorm.deriv]
      apply ENNReal.ofReal_le_ofReal
      exact (normalizedVelocity_le A hσ _ _).trans
        (mul_le_of_le_one_right (div_nonneg (norm_nonneg _) hσ.le)
          (Heterogeneous.probe_speed_le_one p hsi))
    _ = _ := by simp [Real.volume_Ioo, sub_zero]

def probeSpeed (A : Space d →L[ℝ] Space d) (σ : ℝ) (p : Probe d) : ℝ :=
  (GaussianMarked.sphericalLength (fun t => normalizedMap A σ (p.curve t)) p.length).toReal /
    p.length

lemma probeSpeed_le (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ) (p : Probe d) :
    probeSpeed A σ p ≤ ‖A‖ / σ := by
  have hc : 0 ≤ ‖A‖ / σ := div_nonneg (norm_nonneg _) hσ.le
  have h := ENNReal.toReal_mono (by finiteness) (sphericalLength_probe_le A hσ p)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
    ENNReal.toReal_ofReal p.length_pos.le] at h
  exact (div_le_iff₀ p.length_pos).mpr h

/-- Finite-dimensional covariance roots attain their operator norm on a unit direction. -/
theorem exists_unit_norm_attaining (A : Space d →L[ℝ] Space d) (hA : A ≠ 0) :
    ∃ v : Space d, ‖v‖ = 1 ∧ ‖A v‖ = ‖A‖ := by
  have hpos : (0 : ℝ≥0) < ‖A‖₊ := by
    exact_mod_cast norm_pos_iff.mpr hA
  obtain ⟨x, hx, _⟩ := A.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm hpos
  have hx' : ‖x‖ = 1 := by
    simpa using congrArg (fun t : ℝ≥0 => (t : ℝ)) hx
  have hne : (Metric.sphere (0 : Space d) 1).Nonempty :=
    ⟨x, by simpa only [Metric.mem_sphere, dist_zero_right] using hx'⟩
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere (0 : Space d) 1).exists_isMaxOn hne
    A.continuous.norm.continuousOn
  have hv' : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
  refine ⟨v, hv', le_antisymm (by simpa only [hv', mul_one] using A.le_opNorm v) ?_⟩
  rw [← A.sSup_sphere_eq_norm]
  exact csSup_le (hne.image _) (by rintro _ ⟨w, hw, rfl⟩; exact hmax hw)

/-- The source geometric supremum is achieved in the limit by positive-length
centered segments along a norm-attaining direction. -/
theorem probeSpeed_supremum (A : Space d →L[ℝ] Space d) (hA : A ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) :
    (⨆ p : Probe d, ENNReal.ofReal (probeSpeed A σ p)) = ENNReal.ofReal (‖A‖ / σ) := by
  apply le_antisymm
  · exact iSup_le fun p => ENNReal.ofReal_le_ofReal (probeSpeed_le A hσ p)
  · obtain ⟨v, hv, hAv⟩ := exists_unit_norm_attaining A hA
    have hlim := centeredSpeed_limit A hσ v
    rw [hAv] at hlim
    apply le_of_tendsto (ENNReal.continuous_ofReal.tendsto _ |>.comp hlim)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact le_iSup_of_le (lineProbe v hv ε hε) le_rfl

/-- The actual normalized image of every source probe is absolutely continuous. -/
theorem normalized_probe_absolutelyContinuous (A : Space d →L[ℝ] Space d)
    {σ : ℝ} (hσ : 0 < σ) (p : Probe d) :
    AbsolutelyContinuousOnInterval (fun s => normalizedMap A σ (p.curve s)) 0 p.length := by
  have hl : LipschitzOnWith ‖horizontal.comp A‖₊
      (fun s => lift A σ (p.curve s)) (Icc 0 p.length) := by
    simp_rw [lift_eq_horizontal]
    have hb := (horizontal.comp A).lipschitz.comp_lipschitzOnWith p.lipschitz
    have hc := (LipschitzWith.const (σ • append (0 : Space d) 1)).lipschitzOnWith
      (s := Icc 0 p.length) (α := ℝ)
    simpa only [mul_one, add_zero, Function.comp_apply] using hb.add hc
  obtain ⟨C, hC⟩ := GaussianLift.normalized_lipschitzOn p.length_pos.le hl
    (fun _ _ => lift_ne_zero A hσ _)
  have hC' : LipschitzOnWith C (fun s => normalizedMap A σ (p.curve s))
      (uIcc 0 p.length) := by
    simpa only [uIcc_of_le p.length_pos.le, normalizedMap] using hC
  exact hC'.absolutelyContinuousOnInterval

lemma normalized_probe_unit (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (p : Probe d) (s : ℝ) : ‖normalizedMap A σ (p.curve s)‖ = 1 :=
  Gaussian.normalize_norm _ (lift_ne_zero A hσ _)

/-- Original affine Gaussian linear-image scores, before normalization. -/
def liftedScores (A : Space d →L[ℝ] Space d) (σ : ℝ) (p : Probe d)
    {K : ℕ} (Z : Fin K → Space (d+1)) : Fin K → ℝ → ℝ :=
  fun j s => inner ℝ (Z j) (lift A σ (p.curve s))

def expectedCount (A : Space d →L[ℝ] Space d) (σ : ℝ) (K : ℕ) (p : Probe d) : ℝ≥0∞ :=
  expectedSwitchCount (GaussianMarked.gaussianIid (d+1) K) (liftedScores A σ p) p.length

/-- Common positive normalization preserves the actual count on every sample. -/
theorem expectedCount_eq_normalized (A : Space d →L[ℝ] Space d) {σ : ℝ}
    (hσ : 0 < σ) (K : ℕ) (p : Probe d) :
    expectedCount A σ K p = expectedSwitchCount (GaussianMarked.gaussianIid (d+1) K)
      (GaussianMarked.gaussianScores (fun s => normalizedMap A σ (p.curve s))) p.length := by
  unfold expectedCount expectedSwitchCount
  apply lintegral_congr
  intro Z
  unfold switchCount
  apply congrArg (fun S : Set ℝ => (S.encard : ℝ≥0∞))
  simpa only [liftedScores, normalizedMap, GaussianMarked.gaussianScores, zero_add] using
    Gaussian.covarianceLift_switchSet Z (fun s => lift A σ (p.curve s)) (fun _ => 0)
      (fun _ => lift_ne_zero A hσ _) p.length

/-- Internal Lemma 6.2 dependency, expressed on the actual Gaussian sample law.
The subsequent geometry and limiting steps are independently proved above. -/
def CountLengthIdentity (A : Space d →L[ℝ] Space d) (σ : ℝ) (K : ℕ) : Prop :=
  ∀ p : Probe d, expectedCount A σ K p = ENNReal.ofReal (gaussianRankCoefficient K) *
    GaussianMarked.sphericalLength (fun s => normalizedMap A σ (p.curve s)) p.length

/-- The identity needed here follows from the proved Gaussian upper-envelope
assembly and precisely its classical inputs, with no sharpness premise. -/
theorem countLengthIdentity_of_classicalInputs (A : Space d →L[ℝ] Space d)
    {σ : ℝ} (hσ : 0 < σ) (hd : 1 ≤ d) (K : ℕ) (hK : 2 ≤ K)
    (hcrofton : GaussianMarked.ClassicalCroftonLaw)
    (hregular : GaussianMarked.ClassicalCroftonRegularityLaw)
    (hproj : GaussianMarked.GaussianUnitProjectionLaw)
    (hrot : GaussianMarked.GaussianPairReconstructionLaw)
    (hmax : GaussianMarked.GaussianMaxIntegralLaw)
    (hLN : ∀ p : Probe d, VisibleCrossing.LusinNovikovInput
      (GaussianMarked.MarkSample (d+1) (K-2)) (GaussianMarked.CurveParameter p.length)) :
    CountLengthIdentity A σ K := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, K = n+2 := ⟨K-2, by omega⟩
  intro p
  rw [expectedCount_eq_normalized A hσ]
  exact GaussianMarked.gaussian_upper_envelope_crofton hcrofton hregular hproj hrot hmax
    (d+1) n (by omega) p.length p.length_pos
    (fun s => normalizedMap A σ (p.curve s))
    (normalized_probe_absolutelyContinuous A hσ p)
    (fun s _ => normalized_probe_unit A hσ p s)
    (by simpa only [Nat.add_sub_cancel] using hLN p)

/-- The actual expected counts in the density statements are finite. -/
lemma expectedCount_finite (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (K : ℕ) (hcount : CountLengthIdentity A σ K) (p : Probe d) :
    expectedCount A σ K p < ∞ := by
  rw [hcount p]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_of_le_of_lt (sphericalLength_probe_le A hσ p)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))

/-- Expected count per original Euclidean arclength. -/
def expectedDensity (A : Space d →L[ℝ] Space d) (σ : ℝ) (K : ℕ) (p : Probe d) : ℝ :=
  (expectedCount A σ K p).toReal / p.length

lemma expectedDensity_eq_speed (A : Space d →L[ℝ] Space d) (σ : ℝ) (K : ℕ)
    (hcount : CountLengthIdentity A σ K) (p : Probe d) :
    expectedDensity A σ K p = gaussianRankCoefficient K * probeSpeed A σ p := by
  unfold expectedDensity probeSpeed
  rw [hcount p, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (gaussianRankCoefficient_nonneg K)]
  ring

/-- Equation (6.11) is attained asymptotically by the actual centered segments. -/
theorem expectedDensity_line_limit (A : Space d →L[ℝ] Space d) {σ : ℝ} (hσ : 0 < σ)
    (K : ℕ) (hcount : CountLengthIdentity A σ K) (v : Space d) (hv : ‖v‖ = 1) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} => expectedDensity A σ K (lineProbe v hv ε ε.property))
      (comap Subtype.val (𝓝[>] 0))
      (𝓝 (gaussianRankCoefficient K * (‖A v‖ / σ))) := by
  have h := (centeredSpeed_limit A hσ v).const_mul (gaussianRankCoefficient K)
  have ht : Tendsto (Subtype.val : {ε : ℝ // 0 < ε} → ℝ)
      (comap Subtype.val (𝓝[>] 0)) (𝓝[>] 0) := tendsto_comap
  convert h.comp ht using 1
  funext ε
  exact expectedDensity_eq_speed A σ K hcount (lineProbe v hv ε ε.property)

/-- Positive epsilon selects a genuine centered source probe. -/
def centeredExpectedDensity (A : Space d →L[ℝ] Space d) (σ : ℝ) (K : ℕ)
    (v : Space d) (hv : ‖v‖ = 1) (ε : ℝ) : ℝ :=
  if hε : 0 < ε then expectedDensity A σ K (lineProbe v hv ε hε) else 0

theorem centeredExpectedDensity_limit (A : Space d →L[ℝ] Space d) {σ : ℝ}
    (hσ : 0 < σ) (K : ℕ) (hcount : CountLengthIdentity A σ K)
    (v : Space d) (hv : ‖v‖ = 1) :
    Tendsto (centeredExpectedDensity A σ K v hv) (𝓝[>] 0)
      (𝓝 (gaussianRankCoefficient K * (‖A v‖ / σ))) := by
  have h := (centeredSpeed_limit A hσ v).const_mul (gaussianRankCoefficient K)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he : 0 < ε := hε
  rw [centeredExpectedDensity, dif_pos he, expectedDensity_eq_speed A σ K hcount]
  rfl

/-- A norm-attaining unit direction supplies the desired shrinking family. -/
theorem exists_optimal_shrinking_direction (A : Space d →L[ℝ] Space d) (hA : A ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (K : ℕ) (hcount : CountLengthIdentity A σ K) :
    ∃ (v : Space d) (hv : ‖v‖ = 1),
      Tendsto (centeredExpectedDensity A σ K v hv) (𝓝[>] 0)
        (𝓝 (gaussianRankCoefficient K * (‖A‖ / σ))) := by
  obtain ⟨v, hv, hAv⟩ := exists_unit_norm_attaining A hA
  refine ⟨v, hv, ?_⟩
  simpa only [hAv] using centeredExpectedDensity_limit A hσ K hcount v hv

/-- The exact sharp Gaussian density supremum in the nonzero-covariance case. -/
theorem expectedDensity_supremum (A : Space d →L[ℝ] Space d) (hA : A ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (K : ℕ) (hcount : CountLengthIdentity A σ K) :
    (⨆ p : Probe d, ENNReal.ofReal (expectedDensity A σ K p)) =
      ENNReal.ofReal (gaussianRankCoefficient K * (‖A‖ / σ)) := by
  simp_rw [expectedDensity_eq_speed A σ K hcount,
    ENNReal.ofReal_mul (gaussianRankCoefficient_nonneg K)]
  rw [← ENNReal.mul_iSup, probeSpeed_supremum A hA hσ]

/-- This real quotient is precisely the source expectation of switch density. -/
theorem expectedDensity_source (A : Space d →L[ℝ] Space d) (σ : ℝ) (K : ℕ)
    (p : Probe d) : expectedDensity A σ K p =
      (∫⁻ Z, switchDensity (liftedScores A σ p Z) p.length
        ∂GaussianMarked.gaussianIid (d+1) K).toReal := by
  unfold expectedDensity expectedCount expectedSwitchCount switchDensity
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const' _ _
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr p.length_pos))]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal p.length_pos.le]

lemma positive_dimension_of_nonzero (A : Space d →L[ℝ] Space d) (hA : A ≠ 0) : 1 ≤ d := by
  by_contra hn
  have hd : d = 0 := by omega
  subst d
  apply hA
  ext x i
  exact Fin.elim0 i

/-- The coefficient-normalized exact supremum appearing in (2.22). -/
theorem normalized_expectedDensity_supremum (A : Space d →L[ℝ] Space d) (hA : A ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (K : ℕ) (hcount : CountLengthIdentity A σ K) :
    (⨆ p : Probe d, ENNReal.ofReal (expectedDensity A σ K p / (‖A‖ / σ))) =
      ENNReal.ofReal (gaussianRankCoefficient K) := by
  have hc : 0 < ‖A‖ / σ := div_pos (norm_pos_iff.mpr hA) hσ
  simp_rw [ENNReal.ofReal_div_of_pos hc]
  rw [← ENNReal.iSup_div, expectedDensity_supremum A hA hσ K hcount,
    ENNReal.ofReal_mul (gaussianRankCoefficient_nonneg K),
    ENNReal.mul_div_cancel_right (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top]

section ClassicalInputs
variable
    (hcrofton : GaussianMarked.ClassicalCroftonLaw)
    (hregular : GaussianMarked.ClassicalCroftonRegularityLaw)
    (hproj : GaussianMarked.GaussianUnitProjectionLaw)
    (hrot : GaussianMarked.GaussianPairReconstructionLaw)
    (hmax : GaussianMarked.GaussianMaxIntegralLaw)

include hcrofton hregular hproj hrot hmax

/-- Corollary 2.9 sharpness on the actual affine Gaussian sample law. The
only inputs are the classical theorems used to establish Lemma 6.2. -/
theorem gaussian_expectedDensity_supremum (A : Space d →L[ℝ] Space d) (hA : A ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (K : ℕ) (hK : 2 ≤ K)
    (hLN : ∀ p : Probe d, VisibleCrossing.LusinNovikovInput
      (GaussianMarked.MarkSample (d+1) (K-2)) (GaussianMarked.CurveParameter p.length)) :
    (⨆ p : Probe d, ENNReal.ofReal (expectedDensity A σ K p / (‖A‖ / σ))) =
      ENNReal.ofReal (gaussianRankCoefficient K) :=
  normalized_expectedDensity_supremum A hA hσ K
    (countLengthIdentity_of_classicalInputs A hσ (positive_dimension_of_nonzero A hA) K hK
      hcrofton hregular hproj hrot hmax hLN)

/-- Positive Euclidean-length centered Gaussian segments attain the exact
local density at any chosen unit direction, in the shrinking limit. -/
theorem gaussian_expectedDensity_line_limit (A : Space d →L[ℝ] Space d)
    {σ : ℝ} (hσ : 0 < σ) (hd : 1 ≤ d) (K : ℕ) (hK : 2 ≤ K)
    (hLN : ∀ p : Probe d, VisibleCrossing.LusinNovikovInput
      (GaussianMarked.MarkSample (d+1) (K-2)) (GaussianMarked.CurveParameter p.length))
    (v : Space d) (hv : ‖v‖ = 1) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} => expectedDensity A σ K (lineProbe v hv ε ε.property))
      (comap Subtype.val (𝓝[>] 0))
      (𝓝 (gaussianRankCoefficient K * (‖A v‖ / σ))) :=
  expectedDensity_line_limit A hσ K
    (countLengthIdentity_of_classicalInputs A hσ hd K hK hcrofton hregular hproj hrot hmax hLN)
    v hv

/-- There is an actual unit direction whose positive-length Gaussian probes
converge to the sharp coefficient, with Lemma 6.2 fully instantiated. -/
theorem gaussian_exists_optimal_shrinking_direction
    (A : Space d →L[ℝ] Space d) (hA : A ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (K : ℕ) (hK : 2 ≤ K)
    (hLN : ∀ p : Probe d, VisibleCrossing.LusinNovikovInput
      (GaussianMarked.MarkSample (d+1) (K-2)) (GaussianMarked.CurveParameter p.length)) :
    ∃ (v : Space d) (hv : ‖v‖ = 1),
      Tendsto (centeredExpectedDensity A σ K v hv) (𝓝[>] 0)
        (𝓝 (gaussianRankCoefficient K * (‖A‖ / σ))) :=
  exists_optimal_shrinking_direction A hA hσ K
    (countLengthIdentity_of_classicalInputs A hσ (positive_dimension_of_nonzero A hA) K hK
      hcrofton hregular hproj hrot hmax hLN)

end ClassicalInputs
end Paper35.GaussianSharpness

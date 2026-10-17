import Paper35.Sharpness
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Positive-length realization of the uniform-coordinate sharpness construction

The compact-support estimate, actual kernel and CDF limits, dominated
convergence, centered-window FTC limit, straight-probe construction, and iid
coordinate admissibility are proved here. No local intensity or shrinking
limit is assumed. Only the final conversion from local intensity to random
switch counts uses the original internal `ExactCrossingClaim` (Lemma 3.1),
kept explicit until that separate source obligation is discharged.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
namespace Paper35.Sharpness
open Source Source.WeightedModel

variable {d : ℕ}

/-- The actual source crossing kernel as an integral over the two actual
weight samples, not a postulated intensity representation. -/
theorem crossingKernel_weights (m : WeightedModel d) (x u : Space d) (y : ℝ) :
    m.crossingKernel x u y = ∫⁻ z : Space d × Space d,
      ENNReal.ofReal |inner ℝ z.1 u - inner ℝ z.2 u| *
        m.g z.1 (y - inner ℝ z.1 x) * m.g z.2 (y - inner ℝ z.2 x)
      ∂m.weights.prod m.weights := by
  letI := m.probability
  let gy := fun w : Space d => m.g w (y - inner ℝ w x)
  let ν := m.weights.withDensity gy
  let A := fun w : Space d => inner ℝ w u
  have hg : Measurable gy := by
    have hy : Measurable (fun _ : Space d => y) := measurable_const
    exact m.measurable_g.comp (measurable_id.prodMk (hy.sub (by fun_prop)))
  have hA : Measurable A := by fun_prop
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    (ne_top_of_le_ne_top m.average_finite.ne (VisibilityKernel.sliceMass_le_average m x y))
  letI : IsFiniteMeasure (ν.map A) := Measure.isFiniteMeasure_map _ _
  have habs : Measurable (fun z : Space d × Space d => ENNReal.ofReal |A z.1 - A z.2|) :=
    ((hA.comp measurable_fst).sub (hA.comp measurable_snd)).abs.ennreal_ofReal
  have hreal : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal |z.1 - z.2|) :=
    (measurable_fst.sub measurable_snd).abs.ennreal_ofReal
  have hfull := (habs.mul (hg.comp measurable_fst)).mul (hg.comp measurable_snd)
  calc
    _ = ∫⁻ w, ∫⁻ w', ENNReal.ofReal |A w - A w'| ∂ν ∂ν := by
      change (∫⁻ a, ∫⁻ a', ENNReal.ofReal |a - a'| ∂ν.map A ∂ν.map A) = _
      rw [lintegral_map hreal.lintegral_prod_right' hA]
      apply lintegral_congr
      intro w
      have ht : Measurable (fun a' : ℝ => ENNReal.ofReal |A w - a'|) := by fun_prop
      exact lintegral_map ht hA
    _ = ∫⁻ w, ∫⁻ w', ENNReal.ofReal |A w - A w'| * gy w * gy w'
        ∂m.weights ∂m.weights := by
      change (∫⁻ w, ∫⁻ w', ENNReal.ofReal |A w - A w'|
        ∂m.weights.withDensity gy ∂m.weights.withDensity gy) = _
      rw [lintegral_withDensity_eq_lintegral_mul _ hg habs.lintegral_prod_right']
      simp only [Pi.mul_apply]
      apply lintegral_congr
      intro w
      have hw : Measurable (fun w' : Space d => ENNReal.ofReal |A w - A w'|) := by
        have hc : Measurable (fun _ : Space d => A w) := measurable_const
        exact (hc.sub hA).abs.ennreal_ofReal
      rw [lintegral_withDensity_eq_lintegral_mul _ hg hw]
      simp only [Pi.mul_apply]
      rw [← lintegral_const_mul _ (hg.mul hw)]
      apply lintegral_congr
      intro w'
      ac_rfl
    _ = _ := (lintegral_prod _ hfull.aemeasurable).symm

/-- Source score CDFs are continuous at the origin along every deterministic
straight direction. Absolute continuity of the actual conditional bias law
removes the fixed-height boundary event. -/
theorem tendsto_scoreCDF_line (m : WeightedModel d) (u : Space d) (y : ℝ) :
    Tendsto (fun t : ℝ => m.scoreCDF (t • u) y) (𝓝 0) (𝓝 (m.scoreCDF 0 y)) := by
  have hne : ∀ᵐ θ ∂m.joint, VisibleCrossing.scoreValue 0 θ ≠ y := by
    simpa only [mem_setOf_eq] using measure_eq_zero_iff_ae_notMem.mp
      (VisibleCrossing.score_singleton_null m 0 y)
  have hl (θ : Candidate d) : Tendsto
      (fun t : ℝ => VisibleCrossing.scoreValue (t • u) θ) (𝓝 0)
      (𝓝 (VisibleCrossing.scoreValue 0 θ)) := by
    have hc : Continuous (fun t : ℝ => VisibleCrossing.scoreValue (t • u) θ) := by
      unfold VisibleCrossing.scoreValue
      fun_prop
    simpa using hc.tendsto 0
  change Tendsto (fun t : ℝ => m.joint {θ | VisibleCrossing.scoreValue (t • u) θ ≤ y})
    (𝓝 0) (𝓝 (m.joint {θ | VisibleCrossing.scoreValue 0 θ ≤ y}))
  apply tendsto_measure_of_ae_tendsto_indicator (𝓝 (0 : ℝ))
    (measurableSet_le (VisibleCrossing.measurable_scoreValue 0) measurable_const)
    (fun t => measurableSet_le (VisibleCrossing.measurable_scoreValue (t • u)) measurable_const)
    MeasurableSet.univ (measure_ne_top m.joint univ)
    (Filter.Eventually.of_forall fun _ => subset_univ _)
  filter_upwards [hne] with θ hθ
  rcases lt_or_gt_of_ne hθ with hlt | hgt
  · filter_upwards [(hl θ).eventually_lt_const hlt] with t ht
    exact iff_of_true ht.le hlt.le
  · filter_upwards [(hl θ).eventually_const_lt hgt] with t ht
    exact iff_of_false (not_le.mpr ht) (not_le.mpr hgt)

lemma biasDensity_zero_of_abs_gt (B y : ℝ) (hy : biasHalfWidth B < |y|) :
    biasDensity B y = 0 := by
  apply Set.indicator_of_notMem
  change ¬ (-biasHalfWidth B ≤ y ∧ y ≤ biasHalfWidth B)
  exact fun h => not_le.mpr hy (abs_le.mpr h)

/-- The paper's compact-support argument, before integration. -/
lemma shifted_biasDensity_zero {B a δ t A y : ℝ} (_ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (ht : |t| ≤ δ) (hA : |A| ≤ a)
    (hy : biasHalfWidth B + a * δ < |y|) : biasDensity B (y - t * A) = 0 := by
  apply biasDensity_zero_of_abs_gt
  by_contra h
  have hab : |y - t * A| ≤ biasHalfWidth B := le_of_not_gt h
  have hprod : |t * A| ≤ a * δ := by
    rw [abs_mul]
    calc
      _ ≤ δ * a := mul_le_mul ht hA (abs_nonneg _) hδ
      _ = _ := mul_comm _ _
  have htri := abs_add_le (y - t * A) (t * A)
  rw [sub_add_cancel] at htri
  linarith

/-- The actual two-weight integrand admits the claimed constant bound. -/
lemma uniform_weightKernel_bound {a B : ℝ} (_ha : 0 ≤ a) (_hB : 0 < B)
    {w w' : Space d} {u : Space d} (hw : |inner ℝ w u| ≤ a)
    (hw' : |inner ℝ w' u| ≤ a) (t y : ℝ) :
    ENNReal.ofReal |inner ℝ w u - inner ℝ w' u| *
      biasDensity B (y - t * inner ℝ w u) * biasDensity B (y - t * inner ℝ w' u) ≤
        ENNReal.ofReal (2 * a) * ENNReal.ofReal B * ENNReal.ofReal B := by
  have hab : |inner ℝ w u - inner ℝ w' u| ≤ 2 * a := by
    have h := abs_sub_le (inner ℝ w u) (0 : ℝ) (inner ℝ w' u)
    have h0 : |(0 : ℝ) - inner ℝ w' u| ≤ a := by
      rw [abs_sub_comm, sub_zero]
      exact hw'
    simp only [sub_zero] at h
    linarith
  exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hab)
    (biasDensity_le _ _)) (biasDensity_le _ _)

/-- The actual crossing kernel is at most `2 a B²`, with no moment premise. -/
theorem uniform_crossingKernel_bound (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (u : Space d)
    (hμ : ∀ᵐ w ∂μ, |inner ℝ w u| ≤ a) (t y : ℝ) :
    (independentUniformModel μ B hB).crossingKernel (t • u) u y ≤
      ENNReal.ofReal (2 * a) * ENNReal.ofReal B * ENNReal.ofReal B := by
  rw [crossingKernel_weights]
  change (∫⁻ z : Space d × Space d,
    ENNReal.ofReal |inner ℝ z.1 u - inner ℝ z.2 u| *
      biasDensity B (y - inner ℝ z.1 (t • u)) *
      biasDensity B (y - inner ℝ z.2 (t • u)) ∂μ.prod μ) ≤ _
  have hpair : ∀ᵐ z ∂μ.prod μ, |inner ℝ z.1 u| ≤ a ∧ |inner ℝ z.2 u| ≤ a :=
    (Measure.quasiMeasurePreserving_fst.ae hμ).and
      (Measure.quasiMeasurePreserving_snd.ae hμ)
  calc
    _ ≤ ∫⁻ _z : Space d × Space d,
        ENNReal.ofReal (2 * a) * ENNReal.ofReal B * ENNReal.ofReal B ∂μ.prod μ := by
      apply lintegral_mono_ae
      filter_upwards [hpair] with z hz
      simpa only [inner_smul_right] using
        uniform_weightKernel_bound ha hB hz.1 hz.2 t y
    _ = _ := by simp

/-- The actual kernel vanishes outside the paper's expanding compact support. -/
theorem uniform_crossingKernel_zero (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {a B δ t y : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (hδ : 0 ≤ δ) (u : Space d)
    (hμ : ∀ᵐ w ∂μ, |inner ℝ w u| ≤ a) (ht : |t| ≤ δ)
    (hy : biasHalfWidth B + a * δ < |y|) :
    (independentUniformModel μ B hB).crossingKernel (t • u) u y = 0 := by
  rw [crossingKernel_weights]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμ] with z hz
  change ENNReal.ofReal |inner ℝ z.1 u - inner ℝ z.2 u| *
    biasDensity B (y - inner ℝ z.1 (t • u)) *
    biasDensity B (y - inner ℝ z.2 (t • u)) = 0
  rw [inner_smul_right,
    shifted_biasDensity_zero ha hδ ht hz hy, mul_zero, zero_mul]

lemma continuousAt_biasDensity {B y : ℝ} (hB : 0 < B)
    (hyL : y ≠ -biasHalfWidth B) (hyR : y ≠ biasHalfWidth B) :
    ContinuousAt (biasDensity B) y := by
  unfold biasDensity
  apply continuousOn_const.continuousAt_indicator
  have hh : 0 < biasHalfWidth B := by unfold biasHalfWidth; positivity
  rw [frontier_Icc (by linarith : -biasHalfWidth B ≤ biasHalfWidth B)]
  simp [hyL, hyR]

/-- The paper's pointwise crossing-kernel limit away from the two endpoints
of the uniform bias interval. The proof uses the actual two-weight integral. -/
theorem tendsto_uniform_crossingKernel (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {a B y : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (u : Space d)
    (hμ : ∀ᵐ w ∂μ, |inner ℝ w u| ≤ a)
    (hyL : y ≠ -biasHalfWidth B) (hyR : y ≠ biasHalfWidth B) :
    Tendsto (fun t : ℝ => (independentUniformModel μ B hB).crossingKernel (t • u) u y)
      (𝓝 0) (𝓝 ((independentUniformModel μ B hB).crossingKernel 0 u y)) := by
  let F := fun (t : ℝ) (z : Space d × Space d) =>
    ENNReal.ofReal |inner ℝ z.1 u - inner ℝ z.2 u| *
      biasDensity B (y - t * inner ℝ z.1 u) * biasDensity B (y - t * inner ℝ z.2 u)
  let C := ENNReal.ofReal (2 * a) * ENNReal.ofReal B * ENNReal.ofReal B
  have hF (t : ℝ) : Measurable (F t) := by
    have h1 : Measurable (fun z : Space d × Space d => inner ℝ z.1 u) := by fun_prop
    have h2 : Measurable (fun z : Space d × Space d => inner ℝ z.2 u) := by fun_prop
    have ht : Measurable (fun _ : Space d × Space d => t) := measurable_const
    have hy : Measurable (fun _ : Space d × Space d => y) := measurable_const
    exact (((h1.sub h2).abs.ennreal_ofReal).mul
      ((measurable_biasDensity B).comp (hy.sub (ht.mul h1)))).mul
      ((measurable_biasDensity B).comp (hy.sub (ht.mul h2)))
  have hpair : ∀ᵐ z ∂μ.prod μ, |inner ℝ z.1 u| ≤ a ∧ |inner ℝ z.2 u| ≤ a :=
    (Measure.quasiMeasurePreserving_fst.ae hμ).and
      (Measure.quasiMeasurePreserving_snd.ae hμ)
  have hdom (t : ℝ) : ∀ᵐ z ∂μ.prod μ, F t z ≤ C := by
    filter_upwards [hpair] with z hz
    exact uniform_weightKernel_bound ha hB hz.1 hz.2 t y
  have hC : (∫⁻ _z : Space d × Space d, C ∂μ.prod μ) ≠ ∞ := by
    simp only [lintegral_const, measure_univ, mul_one]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hρ := continuousAt_biasDensity hB hyL hyR
  have hρfin : biasDensity B y ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (biasDensity_le B y)
  have hshift (A : ℝ) : Tendsto (fun t : ℝ => biasDensity B (y - t * A))
      (𝓝 0) (𝓝 (biasDensity B y)) := by
    have hc : Continuous (fun t : ℝ => y - t * A) := by fun_prop
    exact hρ.tendsto.comp (by simpa using hc.tendsto 0)
  have hpoint (z : Space d × Space d) : Tendsto (fun t : ℝ => F t z) (𝓝 0) (𝓝 (F 0 z)) := by
    have hp := ENNReal.Tendsto.const_mul (hshift (inner ℝ z.1 u))
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal |inner ℝ z.1 u - inner ℝ z.2 u| ≠ ∞))
    have hpfin : ENNReal.ofReal |inner ℝ z.1 u - inner ℝ z.2 u| * biasDensity B y ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hρfin
    have h := ENNReal.Tendsto.mul hp (Or.inr hρfin) (hshift (inner ℝ z.2 u)) (Or.inr hpfin)
    simpa only [F, zero_mul, sub_zero] using h
  have hlim := tendsto_lintegral_filter_of_dominated_convergence (μ := μ.prod μ)
    (fun _ => C) (Filter.Eventually.of_forall hF) (Filter.Eventually.of_forall hdom) hC
    (Filter.Eventually.of_forall hpoint)
  have heq (t : ℝ) : (independentUniformModel μ B hB).crossingKernel (t • u) u y =
      ∫⁻ z, F t z ∂μ.prod μ := by
    rw [crossingKernel_weights]
    simp only [independentUniformModel, inner_smul_right]
    rfl
  have hfun : (fun t : ℝ => (independentUniformModel μ B hB).crossingKernel (t • u) u y) =
      (fun t : ℝ => ∫⁻ z, F t z ∂μ.prod μ) := funext heq
  rw [hfun, show (independentUniformModel μ B hB).crossingKernel 0 u y =
    ∫⁻ z, F 0 z ∂μ.prod μ from by simpa only [zero_smul] using heq 0]
  exact hlim

/-- The exact compact-support domination stated after (5.5). -/
theorem uniform_crossingKernel_domination (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {a B δ : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (hδ : 0 ≤ δ) (u : Space d)
    (hμ : ∀ᵐ w ∂μ, |inner ℝ w u| ≤ a) {t : ℝ} (ht : |t| ≤ δ) (y : ℝ) :
    (independentUniformModel μ B hB).crossingKernel (t • u) u y ≤
      (Icc (-(biasHalfWidth B + a * δ)) (biasHalfWidth B + a * δ)).indicator
        (fun _ => ENNReal.ofReal (2 * a) * ENNReal.ofReal B * ENNReal.ofReal B) y := by
  by_cases hy : |y| ≤ biasHalfWidth B + a * δ
  · have hmem : y ∈ Icc (-(biasHalfWidth B + a * δ)) (biasHalfWidth B + a * δ) := abs_le.mp hy
    rw [Set.indicator_of_mem hmem]
    exact uniform_crossingKernel_bound μ ha hB u hμ t y
  · have hmem : y ∉ Icc (-(biasHalfWidth B + a * δ)) (biasHalfWidth B + a * δ) :=
      fun h => hy (abs_le.mpr h)
    rw [Set.indicator_of_notMem hmem]
    rw [uniform_crossingKernel_zero μ ha hB hδ u hμ ht (lt_of_not_ge hy)]

lemma measurable_crossingKernel_height (m : WeightedModel d) (x u : Space d) :
    Measurable (m.crossingKernel x u) := by
  have hm := ((VisibilityKernel.measurable_qminus m x u).mul
    (VisibilityKernel.measurable_qplus m x u)).lintegral_prod_right' (ν := (volume : Measure ℝ))
  have heq : m.crossingKernel x u =
      (fun y => 2 * ∫⁻ r, VisibilityKernel.qminus m x u y r * VisibilityKernel.qplus m x u y r) :=
    funext (VisibilityKernel.crossingKernel_layerCake m x u)
  rw [heq]
  exact hm.const_mul 2

/-- Dominated convergence proves continuity of the actual local-intensity
integral at the origin. Its only weight premise is the proved bounded slope
support; no intensity or limiting statement is assumed. -/
theorem tendsto_uniform_localIntensity (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (u : Space d)
    (hμ : ∀ᵐ w ∂μ, |inner ℝ w u| ≤ a) (K : ℕ) :
    Tendsto (fun t : ℝ => localIntensity (independentUniformModel μ B hB) K (t • u) u)
      (𝓝 0) (𝓝 (localIntensity (independentUniformModel μ B hB) K 0 u)) := by
  let m := independentUniformModel μ B hB
  let n := K - 2
  let C := ENNReal.ofReal (2 * a) * ENNReal.ofReal B * ENNReal.ofReal B
  let H := biasHalfWidth B + a
  let D : ℝ → ℝ≥0∞ := (Icc (-H) H).indicator (fun _ => C)
  let F := fun t y : ℝ => m.scoreCDF (t • u) y ^ n * m.crossingKernel (t • u) u y
  have hF (t : ℝ) : Measurable (F t) :=
    ((VisibilityKernel.measurable_scoreCDF m (t • u)).pow_const n).mul
      (measurable_crossingKernel_height m (t • u) u)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hD : (∫⁻ y, D y) ≠ ∞ := by
    dsimp only [D]
    rw [lintegral_indicator measurableSet_Icc]
    simp only [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top hC (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have ht : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 := by
    have h := (continuous_abs.tendsto (0 : ℝ)).eventually_lt_const (by norm_num : |(0 : ℝ)| < 1)
    exact h.mono fun t ht => ht.le
  have hdom : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ y : ℝ, F t y ≤ D y := by
    filter_upwards [ht] with t ht
    exact Filter.Eventually.of_forall fun y => by
      have hpow : m.scoreCDF (t • u) y ^ n ≤ 1 :=
        pow_le_one₀ (zero_le _) (scoreCDF_le_one m (t • u) y)
      calc
        _ ≤ m.crossingKernel (t • u) u y := by
          exact (mul_le_mul_right' hpow _).trans_eq (one_mul _)
        _ ≤ D y := by
          simpa only [D, H, mul_one] using uniform_crossingKernel_domination μ ha hB
            (by norm_num : (0 : ℝ) ≤ 1) u hμ ht y
  have hneL : ∀ᵐ y : ℝ, y ≠ -biasHalfWidth B := by
    simpa only [mem_singleton_iff] using (Set.countable_singleton (-biasHalfWidth B)).ae_notMem volume
  have hneR : ∀ᵐ y : ℝ, y ≠ biasHalfWidth B := by
    simpa only [mem_singleton_iff] using (Set.countable_singleton (biasHalfWidth B)).ae_notMem volume
  have hpoint : ∀ᵐ y : ℝ, Tendsto (fun t : ℝ => F t y) (𝓝 0) (𝓝 (F 0 y)) := by
    filter_upwards [hneL, hneR] with y hyL hyR
    have hCDF := ENNReal.Tendsto.pow (n := n) (tendsto_scoreCDF_line m u y)
    have hR := tendsto_uniform_crossingKernel μ ha hB u hμ hyL hyR
    have hRfin : m.crossingKernel 0 u y ≠ ∞ := by
      apply ne_top_of_le_ne_top hC
      simpa only [zero_smul] using uniform_crossingKernel_bound μ ha hB u hμ 0 y
    have hFfin : m.scoreCDF 0 y ^ n ≠ ∞ :=
      ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (scoreCDF_le_one m 0 y))
    have h := ENNReal.Tendsto.mul hCDF (Or.inr hRfin) hR (Or.inr hFfin)
    simpa only [F, zero_smul] using h
  have hlim := tendsto_lintegral_filter_of_dominated_convergence D
    (Filter.Eventually.of_forall hF) hdom hD hpoint
  have h := ENNReal.Tendsto.const_mul (a := (K.choose 2 : ℝ≥0∞)) hlim
    (Or.inr (ENNReal.natCast_ne_top _))
  simpa only [localIntensity, F, n, zero_smul] using h

/-- The explicit (5.3) construction has the claimed local intensity limit. -/
theorem tendsto_sharp_localIntensity {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ)
    (K : ℕ) (hK : 2 ≤ K) (i : Fin d) :
    Tendsto (fun t : ℝ => localIntensity
      (independentUniformModel (uniformWeights d (Real.sqrt 3 * σ)) B hB)
        K (t • axis i) (axis i)) (𝓝 0)
      (𝓝 (ENNReal.ofReal ((K : ℝ) / Real.sqrt 3 * B * σ))) := by
  have ha : 0 < Real.sqrt 3 * σ := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hσ
  have hμ : ∀ᵐ w ∂uniformWeights d (Real.sqrt 3 * σ), |inner ℝ w (axis i)| ≤ Real.sqrt 3 * σ := by
    simpa only [inner_axis] using uniformWeights_coordinate_bounded ha i
  simpa only [origin_sharp_intensity hσ hB K hK i] using
    tendsto_uniform_localIntensity (uniformWeights d (Real.sqrt 3 * σ)) ha.le hB (axis i) hμ K

lemma measurable_line_scoreCDF (m : WeightedModel d) (u : Space d) :
    Measurable (Function.uncurry (fun t y : ℝ => m.scoreCDF (t • u) y)) := by
  let S : Set ((ℝ × ℝ) × Candidate d) :=
    {p | VisibleCrossing.scoreValue (p.1.1 • u) p.2 ≤ p.1.2}
  have hs : MeasurableSet S := by
    apply measurableSet_le _ measurable_fst.snd
    unfold VisibleCrossing.scoreValue
    fun_prop
  have hm : Measurable (S.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hs
  convert hm.lintegral_prod_right' (ν := m.joint) using 1
  funext p
  change m.scoreCDF (p.1 • u) p.2 =
    ∫⁻ θ, {θ | VisibleCrossing.scoreValue (p.1 • u) θ ≤ p.2}.indicator (fun _ => 1) θ ∂m.joint
  rw [lintegral_indicator
    (measurableSet_le (VisibleCrossing.measurable_scoreValue (p.1 • u)) measurable_const)]
  simp [scoreCDF, VisibleCrossing.scoreValue]

lemma measurable_line_crossingKernel (m : WeightedModel d) (u : Space d) :
    Measurable (Function.uncurry (fun t y : ℝ => m.crossingKernel (t • u) u y)) := by
  letI := m.probability
  have h1 : Measurable (fun p : (ℝ × ℝ) × (Space d × Space d) =>
      m.g p.2.1 (p.1.2 - inner ℝ p.2.1 (p.1.1 • u))) := by
    exact m.measurable_g.comp (measurable_snd.fst.prodMk
      (measurable_fst.snd.sub (by fun_prop)))
  have h2 : Measurable (fun p : (ℝ × ℝ) × (Space d × Space d) =>
      m.g p.2.2 (p.1.2 - inner ℝ p.2.2 (p.1.1 • u))) := by
    exact m.measurable_g.comp (measurable_snd.snd.prodMk
      (measurable_fst.snd.sub (by fun_prop)))
  have hA : Measurable (fun p : (ℝ × ℝ) × (Space d × Space d) =>
      ENNReal.ofReal |inner ℝ p.2.1 u - inner ℝ p.2.2 u|) := by fun_prop
  have hm := ((hA.mul h1).mul h2).lintegral_prod_right' (ν := m.weights.prod m.weights)
  convert hm using 1
  funext p
  exact crossingKernel_weights m (p.1 • u) u p.2

lemma measurable_line_localIntensity (m : WeightedModel d) (K : ℕ) (u : Space d) :
    Measurable (fun t : ℝ => localIntensity m K (t • u) u) := by
  have hm := (((measurable_line_scoreCDF m u).pow_const (K - 2)).mul
    (measurable_line_crossingKernel m u)).lintegral_prod_right' (ν := (volume : Measure ℝ))
  exact hm.const_mul (K.choose 2 : ℝ≥0∞)

/-- Standard FTC gives the centered-window average limit from measurability
and continuity at the center. This proof adds no assumption about a limit. -/
theorem tendsto_centered_average {f : ℝ → ℝ} (hm : Measurable f) (hc : ContinuousAt f 0) :
    Tendsto (fun ε : ℝ => (∫ t in (-ε / 2)..(ε / 2), f t) / ε)
      (𝓝[>] 0) (𝓝 (f 0)) := by
  have hmf : StronglyMeasurableAtFilter f (𝓝 (0 : ℝ)) :=
    hm.stronglyMeasurable.stronglyMeasurableAtFilter
  have hi := intervalIntegral.integral_hasFDerivAt
    (IntervalIntegrable.refl : IntervalIntegrable f volume 0 0) hmf hmf hc hc
  have hleft : HasDerivAt (fun ε : ℝ => -ε / 2) (-1 / 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).neg.div_const 2
  have hright : HasDerivAt (fun ε : ℝ => ε / 2) (1 / 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const 2
  have hp := hleft.prodMk hright
  have hcomp := hi.comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp)
  have hd : HasDerivAt (fun ε : ℝ => ∫ t in (-ε / 2)..(ε / 2), f t) (f 0) 0 := by
    convert hcomp using 1; simp; ring
  simpa only [zero_add, neg_zero, zero_div, intervalIntegral.integral_same, sub_zero,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

/-- The source local intensity's centered-window mean converges to (5.5). -/
theorem sharp_centered_average_limit {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ)
    (K : ℕ) (hK : 2 ≤ K) (i : Fin d) :
    Tendsto (fun ε : ℝ => (∫ t in (-ε / 2)..(ε / 2),
      (localIntensity (independentUniformModel (uniformWeights d (Real.sqrt 3 * σ)) B hB)
        K (t • axis i) (axis i)).toReal) / ε)
      (𝓝[>] 0) (𝓝 ((K : ℝ) / Real.sqrt 3 * B * σ)) := by
  let m := independentUniformModel (uniformWeights d (Real.sqrt 3 * σ)) B hB
  have hI := tendsto_sharp_localIntensity hB hσ K hK i
  have hc : ContinuousAt (fun t : ℝ => (localIntensity m K (t • axis i) (axis i)).toReal) 0 := by
    have h := (ENNReal.continuousAt_toReal ENNReal.ofReal_ne_top).tendsto.comp hI
    simpa only [ContinuousAt, m, Function.comp_def, zero_smul, origin_sharp_intensity hσ hB K hK i,
      ENNReal.toReal_ofReal (show 0 ≤ (K : ℝ) / Real.sqrt 3 * B * σ by positivity)] using h
  have h := tendsto_centered_average (measurable_line_localIntensity m K (axis i)).ennreal_toReal hc
  simpa only [m, zero_smul, origin_sharp_intensity hσ hB K hK i,
    ENNReal.toReal_ofReal (show 0 ≤ (K : ℝ) / Real.sqrt 3 * B * σ by positivity)] using h

/-- The positive-length, centered coordinate-axis segment in the paper. -/
def centeredCurve (i : Fin d) (ε s : ℝ) : Space d := (-ε / 2 + s) • axis i

lemma centeredCurve_isometry (i : Fin d) (ε : ℝ) : Isometry (centeredCurve i ε) := by
  apply isometry_iff_dist_eq.mpr
  intro s t
  have hn : ‖axis i‖ = 1 := by simp [axis]
  simp only [centeredCurve, dist_eq_norm, ← sub_smul, norm_smul, hn, mul_one, Real.norm_eq_abs]
  congr 1
  ring

/-- These are genuine `Probe`s with their actual geometric arclength. -/
def centeredProbe (i : Fin d) (ε : ℝ) (hε : 0 < ε) : Probe d where
  curve := centeredCurve i ε
  length := ε
  length_pos := hε
  lipschitz := (centeredCurve_isometry i ε).lipschitz.lipschitzOnWith
  arclength := by
    have hid : eVariationOn (id : ℝ → ℝ) (Icc 0 ε) ≤ ENNReal.ofReal ε := by
      have h := (monotone_id.monotoneOn univ : MonotoneOn (id : ℝ → ℝ) univ).eVariationOn_le
        (a := 0) (b := ε) (mem_univ _) (mem_univ _)
      simpa only [univ_inter, id_eq, sub_zero] using h
    have hupper : eVariationOn (centeredCurve i ε) (Icc 0 ε) ≤ ENNReal.ofReal ε := by
      have h := (centeredCurve_isometry i ε).lipschitz.lipschitzOnWith.comp_eVariationOn_le
        (g := (id : ℝ → ℝ)) (s := Icc 0 ε) (mapsTo_univ _ _)
      have hle : eVariationOn (centeredCurve i ε) (Icc 0 ε) ≤ eVariationOn (id : ℝ → ℝ) (Icc 0 ε) := by
        simpa using h
      exact hle.trans hid
    have hlower := eVariationOn.edist_le (centeredCurve i ε)
      (left_mem_Icc.mpr hε.le) (right_mem_Icc.mpr hε.le)
    have hed : edist (centeredCurve i ε 0) (centeredCurve i ε ε) = ENNReal.ofReal ε := by
      rw [(centeredCurve_isometry i ε).edist_eq]
      simp [edist_dist, Real.dist_eq, abs_of_nonneg hε.le]
    rw [hed] at hlower
    exact le_antisymm hupper hlower

lemma centeredCurve_deriv (i : Fin d) (ε s : ℝ) : deriv (centeredCurve i ε) s = axis i := by
  have h := ((hasDerivAt_id s).const_add (-ε / 2)).smul_const (axis i)
  have hd : HasDerivAt (centeredCurve i ε) (axis i) s := by
    simpa only [centeredCurve, one_smul] using h
  exact hd.deriv

/-- Bounded projected slopes make every actual local intensity finite. -/
lemma uniform_localIntensity_finite (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (u : Space d)
    (hμ : ∀ᵐ w ∂μ, |inner ℝ w u| ≤ a) (K : ℕ) (t : ℝ) :
    localIntensity (independentUniformModel μ B hB) K (t • u) u ≠ ∞ := by
  let m := independentUniformModel μ B hB
  let C := ENNReal.ofReal (2 * a) * ENNReal.ofReal B * ENNReal.ofReal B
  let H := biasHalfWidth B + a * |t|
  let D : ℝ → ℝ≥0∞ := (Icc (-H) H).indicator (fun _ => C)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hD : (∫⁻ y, D y) ≠ ∞ := by
    dsimp only [D]
    rw [lintegral_indicator measurableSet_Icc]
    simp only [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top hC (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hdom (y : ℝ) : m.scoreCDF (t • u) y ^ (K - 2) * m.crossingKernel (t • u) u y ≤ D y := by
    have hpow : m.scoreCDF (t • u) y ^ (K - 2) ≤ 1 :=
      pow_le_one₀ (zero_le _) (scoreCDF_le_one m (t • u) y)
    calc
      _ ≤ m.crossingKernel (t • u) u y := (mul_le_mul_right' hpow _).trans_eq (one_mul _)
      _ ≤ D y := uniform_crossingKernel_domination μ ha hB (abs_nonneg t) u hμ le_rfl y
  unfold localIntensity
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ne_top_of_le_ne_top hD (lintegral_mono hdom))

/-- The original expected switch count on a positive centered segment,
normalized by its actual length. -/
def centeredExpectedDensity (m : WeightedModel d) (K : ℕ) (i : Fin d) (ε : ℝ) : ℝ :=
  if hε : 0 < ε then (m.expectedCount K (centeredProbe i ε hε)).toReal / ε else 0

/-- Exact-crossing assembly is kept as the explicit internal dependency.
All continuity, domination, and positive-length segment construction here
are already proved independently of it. -/
theorem centeredExpectedDensity_eq_average (hcross : ExactCrossingClaim (d := d))
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B)
    (i : Fin d) (hμ : ∀ᵐ w ∂μ, |w i| ≤ a) (K : ℕ) (hK : 2 ≤ K)
    {ε : ℝ} (hε : 0 < ε) :
    centeredExpectedDensity (independentUniformModel μ B hB) K i ε =
      (∫ t in (-ε / 2)..(ε / 2),
        (localIntensity (independentUniformModel μ B hB) K (t • axis i) (axis i)).toReal) / ε := by
  let m := independentUniformModel μ B hB
  have hμ' : ∀ᵐ w ∂μ, |inner ℝ w (axis i)| ≤ a := by simpa only [inner_axis] using hμ
  have hcount : m.expectedCount K (centeredProbe i ε hε) =
      ∫⁻ s in Icc 0 ε, localIntensity m K ((-ε / 2 + s) • axis i) (axis i) := by
    have h := hcross m K hK (centeredProbe i ε hε)
    change m.expectedCount K (centeredProbe i ε hε) = (K.choose 2 : ℝ≥0∞) *
      ∫⁻ s in Icc 0 ε, ∫⁻ y, m.scoreCDF (centeredCurve i ε s) y ^ (K - 2) *
        m.crossingKernel (centeredCurve i ε s) (deriv (centeredCurve i ε) s) y at h
    simp_rw [centeredCurve_deriv] at h
    rw [h]
    exact (lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)).symm
  have hm : Measurable (fun s : ℝ => localIntensity m K ((-ε / 2 + s) • axis i) (axis i)) :=
    (measurable_line_localIntensity m K (axis i)).comp (by fun_prop)
  have hr : (∫⁻ s in Icc 0 ε, localIntensity m K ((-ε / 2 + s) • axis i) (axis i)).toReal =
      ∫ s in Icc 0 ε, (localIntensity m K ((-ε / 2 + s) • axis i) (axis i)).toReal := by
    symm
    apply integral_toReal hm.aemeasurable.restrict
    exact Filter.Eventually.of_forall fun s => (uniform_localIntensity_finite μ ha hB
      (axis i) hμ' K (-ε / 2 + s)).lt_top
  rw [centeredExpectedDensity, dif_pos hε, hcount, hr]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hε.le,
    intervalIntegral.integral_comp_add_left
      (fun t : ℝ => (localIntensity m K (t • axis i) (axis i)).toReal) (-ε / 2)]
  congr 1 <;> ring

/-- Positive-length shrinking segments realize the sharp intensity limit;
its sole remaining internal dependency is the original exact crossing lemma. -/
theorem sharp_expectedDensity_limit (hcross : ExactCrossingClaim (d := d))
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (K : ℕ) (hK : 2 ≤ K) (i : Fin d) :
    Tendsto (centeredExpectedDensity
      (independentUniformModel (uniformWeights d (Real.sqrt 3 * σ)) B hB) K i)
      (𝓝[>] 0) (𝓝 ((K : ℝ) / Real.sqrt 3 * B * σ)) := by
  have ha : 0 < Real.sqrt 3 * σ := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hσ
  have h := sharp_centered_average_limit hB hσ K hK i
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (centeredExpectedDensity_eq_average hcross (uniformWeights d (Real.sqrt 3 * σ))
    ha.le hB i (uniformWeights_coordinate_bounded ha i) K hK hε).symm

/-- The normalized expected count is exactly the expectation of the source's
visible-switch density on the same positive-length probe. -/
theorem centeredExpectedDensity_source (m : WeightedModel d) (K : ℕ) (i : Fin d)
    {ε : ℝ} (hε : 0 < ε) :
    centeredExpectedDensity m K i ε =
      (∫⁻ θ, switchDensity (scores (centeredProbe i ε hε) θ) ε ∂m.iid K).toReal := by
  rw [centeredExpectedDensity, dif_pos hε]
  change (∫⁻ θ, switchCount (scores (centeredProbe i ε hε) θ) ε ∂m.iid K).toReal / ε = _
  unfold switchDensity
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const' _ _
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hε))]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hε.le]

/-- The same genuine construction never exceeds its limiting sharp value.
This uses the already-proved visibility inequality and the shared exact
crossing lemma, not a conjectural covariance or sharpness bound. -/
theorem centeredExpectedDensity_le_sharp (hcross : ExactCrossingClaim (d := d))
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (K : ℕ) (hK : 2 ≤ K) (i : Fin d)
    {ε : ℝ} (hε : 0 < ε) :
    centeredExpectedDensity (independentUniformModel (uniformWeights d (Real.sqrt 3 * σ)) B hB)
      K i ε ≤ (K : ℝ) / Real.sqrt 3 * B * σ := by
  let a := Real.sqrt 3 * σ
  let m := independentUniformModel (uniformWeights d a) B hB
  have ha : 0 ≤ a := mul_nonneg (Real.sqrt_nonneg _) hσ.le
  have hG : m.directionalGini (axis i) = ENNReal.ofReal (2 * a / 3) :=
    uniformWeights_directionalGini a ha i hB
  have hcoef : ((K : ℝ≥0∞) * ENNReal.ofReal B / 2) * ENNReal.ofReal (2 * a / 3) =
      ENNReal.ofReal ((K : ℝ) / Real.sqrt 3 * B * σ) := by
    have h := origin_sharp_intensity hσ hB K hK i
    rw [origin_rank_intensity _ ha i hB K hK] at h
    exact h
  have hv := weightedVisibility_of_crossing_visibility hcross
    (VisibilityKernel.visibilityLemmaClaim d) m K hK (centeredProbe i ε hε)
  change m.expectedCount K (centeredProbe i ε hε) ≤
    ((K : ℝ≥0∞) * m.average / 2) *
      ∫⁻ s in Icc 0 ε, m.directionalGini (deriv (centeredCurve i ε) s) at hv
  simp_rw [centeredCurve_deriv] at hv
  rw [uniformModel_average, hG] at hv
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero] at hv
  have hv' : m.expectedCount K (centeredProbe i ε hε) ≤
      ENNReal.ofReal ((K : ℝ) / Real.sqrt 3 * B * σ) * ENNReal.ofReal ε := by
    calc
      _ ≤ _ := hv
      _ = _ := by rw [← mul_assoc, hcoef]
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hv'
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0 ≤ (K : ℝ) / Real.sqrt 3 * B * σ by positivity),
    ENNReal.toReal_ofReal hε.le] at hr
  rw [centeredExpectedDensity, dif_pos hε]
  exact (div_le_iff₀ hε).2 hr

/-- Every fixed rank and dimension is sharp even on this one explicit
family of positive-length straight probes and iid uniform coordinates. -/
theorem sharp_centered_supremum (hcross : ExactCrossingClaim (d := d))
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (K : ℕ) (hK : 2 ≤ K) (i : Fin d) :
    (⨆ ε : {ε : ℝ // 0 < ε}, ENNReal.ofReal (centeredExpectedDensity
      (independentUniformModel (uniformWeights d (Real.sqrt 3 * σ)) B hB) K i ε)) =
      ENNReal.ofReal ((K : ℝ) / Real.sqrt 3 * B * σ) := by
  apply le_antisymm
  · apply iSup_le
    intro ε
    exact ENNReal.ofReal_le_ofReal (centeredExpectedDensity_le_sharp hcross hB hσ K hK i ε.property)
  · have hlim := (ENNReal.continuous_ofReal.tendsto
        ((K : ℝ) / Real.sqrt 3 * B * σ)).comp (sharp_expectedDensity_limit hcross hB hσ K hK i)
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact le_iSup_of_le (⟨ε, hε⟩ : {ε : ℝ // 0 < ε}) le_rfl

/-- No smaller fixed-rank coefficient can control even the explicit uniform
construction on all positive-length centered segments. -/
theorem sharp_fixed_rank_coefficient (hcross : ExactCrossingClaim (d := d))
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (K : ℕ) (hK : 2 ≤ K) (i : Fin d) (C : ℝ)
    (hbound : ∀ ε : ℝ, 0 < ε → centeredExpectedDensity
      (independentUniformModel (uniformWeights d (Real.sqrt 3 * σ)) B hB) K i ε ≤ C * B * σ) :
    (K : ℝ) / Real.sqrt 3 ≤ C := by
  have h := sharp_expectedDensity_limit hcross hB hσ K hK i
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0, centeredExpectedDensity
      (independentUniformModel (uniformWeights d (Real.sqrt 3 * σ)) B hB) K i ε ≤ C * B * σ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hbound ε hε
  have hle := le_of_tendsto h hevent
  apply (mul_le_mul_iff_left₀ (mul_pos hB hσ)).1
  convert hle using 1 <;> ring

/-- Rank two forces the universal `(K-1)`-normalized coefficient `2/sqrt(3)`.
An all-ranks bound must, in particular, bound this rank-two construction. -/
theorem sharp_universal_rank_coefficient (hcross : ExactCrossingClaim (d := d))
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (i : Fin d) (C : ℝ)
    (hbound : ∀ ε : ℝ, 0 < ε → centeredExpectedDensity
      (independentUniformModel (uniformWeights d (Real.sqrt 3 * σ)) B hB) 2 i ε ≤ C * B * σ) :
    2 / Real.sqrt 3 ≤ C :=
  sharp_fixed_rank_coefficient hcross hB hσ 2 (by norm_num) i C hbound

/-- The actual constructed coordinates satisfy the original finite second
moment hypothesis, in addition to the already computed variance. -/
theorem uniformWeights_coordinate_memLp (a : ℝ) (i : Fin d) :
    MemLp (fun w : Space d => w i) 2 (uniformWeights d a) := by
  have hd : ProbabilityTheory.IdentDistrib (fun w : Space d => w i) (affineUniform a)
      (uniformWeights d a) Gini.unitLaw :=
    ⟨(measurable_coordinate i).aemeasurable, (measurable_affineUniform a).aemeasurable,
      uniformWeights_coordinate_marginal a i⟩
  exact hd.memLp_iff.2 ((memLp_const (-a)).add (Gini.unitLaw_memLp.const_mul (2 * a)))

/-- The coordinates are genuinely independent, with identical laws. This
is a consequence of the constructed product measure, not a model field. -/
theorem uniformWeights_coordinates_iid (a : ℝ) :
    ProbabilityTheory.iIndepFun (fun (i : Fin d) (w : Space d) => w i) (uniformWeights d a) ∧
      ∀ i j : Fin d, ProbabilityTheory.IdentDistrib (fun w : Space d => w i) (fun w : Space d => w j)
        (uniformWeights d a) (uniformWeights d a) := by
  constructor
  · apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin d => (measurable_coordinate i).aemeasurable)).2
    change (uniformWeights d a).map (EuclideanSpace.measurableEquiv (Fin d)) = _
    rw [uniformWeights_coordinate_product]
    congr 1
    funext i
    exact (uniformWeights_coordinate_marginal a i).symm
  · intro i j
    exact ⟨(measurable_coordinate i).aemeasurable, (measurable_coordinate j).aemeasurable,
      (uniformWeights_coordinate_marginal a i).trans (uniformWeights_coordinate_marginal a j).symm⟩

end Paper35.Sharpness

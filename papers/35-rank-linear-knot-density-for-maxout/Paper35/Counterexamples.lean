import Paper35.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
Section 5 counterexamples. The sample space is the actual product law of the
candidate parameters. Counts below count transverse intersections in the open
probe interval; for two affine candidates every such intersection is visible.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Paper35.Counterexamples

/-- A transverse equality of two affine scores. With two candidates it is visible. -/
def BinarySwitchAt (a b c d x : ℝ) : Prop :=
  a * x + b = c * x + d ∧ a ≠ c

/-- The (unique, when the slopes differ) meeting point. -/
def meetingPoint (a b c d : ℝ) : ℝ := (d - b) / (a - c)

lemma binarySwitchAt_iff (a b c d x : ℝ) :
    BinarySwitchAt a b c d x ↔ a ≠ c ∧ x = meetingPoint a b c d := by
  unfold BinarySwitchAt meetingPoint
  constructor
  · rintro ⟨heq, hne⟩
    refine ⟨hne, (eq_div_iff (sub_ne_zero.mpr hne)).2 ?_⟩
    nlinarith
  · rintro ⟨hne, rfl⟩
    refine ⟨?_, hne⟩
    have h := div_mul_cancel₀ (d - b) (sub_ne_zero.mpr hne)
    nlinarith

/-- A binary transverse meeting reverses the upper-envelope order on both sides. -/
lemma binarySwitch_order_exchange {a b c d x : ℝ}
    (h : BinarySwitchAt a b c d x) (δ : ℝ) (hδ : 0 < δ) :
    ((a * (x - δ) + b < c * (x - δ) + d ∧
        c * (x + δ) + d < a * (x + δ) + b) ∨
      (c * (x - δ) + d < a * (x - δ) + b ∧
        a * (x + δ) + b < c * (x + δ) + d)) := by
  rcases lt_or_gt_of_ne h.2 with hlt | hgt
  · right
    have hp : 0 < (c - a) * δ := mul_pos (sub_pos.mpr hlt) hδ
    constructor <;> nlinarith [h.1]
  · left
    have hp : 0 < (a - c) * δ := mul_pos (sub_pos.mpr hgt) hδ
    constructor <;> nlinarith [h.1]

/-- Number of visible switches for two affine scores on an open interval. -/
def binarySwitchCount (lo hi a b c d : ℝ) : ℝ :=
  if a ≠ c ∧ lo < meetingPoint a b c d ∧ meetingPoint a b c d < hi then 1 else 0

lemma binarySwitchCount_eq_one_iff (lo hi a b c d : ℝ) :
    binarySwitchCount lo hi a b c d = 1 ↔
      ∃ x ∈ Ioo lo hi, BinarySwitchAt a b c d x := by
  classical
  unfold binarySwitchCount
  rw [ite_eq_left_iff]
  simp only [zero_ne_one, imp_false, not_not]
  constructor
  · rintro ⟨hne, hlo, hhi⟩
    exact ⟨meetingPoint a b c d, ⟨hlo, hhi⟩,
      (binarySwitchAt_iff _ _ _ _ _).2 ⟨hne, rfl⟩⟩
  · rintro ⟨x, ⟨hlo, hhi⟩, hx⟩
    rcases (binarySwitchAt_iff _ _ _ _ _).1 hx with ⟨hne, rfl⟩
    exact ⟨hne, hlo, hhi⟩

lemma binarySwitch_unique {a b c d x y : ℝ}
    (hx : BinarySwitchAt a b c d x) (hy : BinarySwitchAt a b c d y) : x = y := by
  exact ((binarySwitchAt_iff _ _ _ _ _).1 hx).2.trans
    ((binarySwitchAt_iff _ _ _ _ _).1 hy).2.symm

lemma binarySwitchCount_nonneg (lo hi a b c d : ℝ) :
    0 ≤ binarySwitchCount lo hi a b c d := by
  unfold binarySwitchCount; split_ifs <;> norm_num

lemma binarySwitchCount_le_one (lo hi a b c d : ℝ) :
    binarySwitchCount lo hi a b c d ≤ 1 := by
  unfold binarySwitchCount; split_ifs <;> norm_num

lemma binarySwitchCount_centered {ε x₀ a c : ℝ} (hε : 0 < ε) (hne : a ≠ c) :
    binarySwitchCount (x₀ - ε) (x₀ + ε) a (-x₀ * a) c (-x₀ * c) = 1 := by
  apply (binarySwitchCount_eq_one_iff _ _ _ _ _ _).2
  refine ⟨x₀, ⟨by linarith, by linarith⟩, ?_⟩
  exact ⟨by ring, hne⟩

/-- Independent copies of an atomless real law differ almost surely. -/
lemma iid_slopes_ne (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    ∀ᵐ z ∂μ.prod μ, z.1 ≠ z.2 := by
  apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).2
  exact Filter.Eventually.of_forall fun a => by
    simpa only [mem_singleton_iff, ne_eq, eq_comm] using
      (Set.countable_singleton a).ae_notMem μ

/-- The sample law has two independent slopes and two independent biases. -/
def independentLaw (μ ν : Measure ℝ) : Measure ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (μ.prod μ).prod (ν.prod ν)

/-- Expected count divided by the geometric length of the probe interval. -/
def independentExpectedDensity (μ ν : Measure ℝ) (lo hi : ℝ) : ℝ :=
  (∫ z, binarySwitchCount lo hi z.1.1 z.2.1 z.1.2 z.2.2 ∂independentLaw μ ν) /
    (hi - lo)

lemma measurable_binarySwitchCount (lo hi : ℝ) :
    Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      binarySwitchCount lo hi z.1.1 z.2.1 z.1.2 z.2.2) := by
  unfold binarySwitchCount meetingPoint
  have hq : Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      (z.2.2 - z.2.1) / (z.1.1 - z.1.2)) := by fun_prop
  apply Measurable.ite _ measurable_const measurable_const
  exact (isClosed_eq continuous_fst.fst continuous_fst.snd).measurableSet.compl.inter
    ((measurableSet_lt measurable_const hq).inter
      (measurableSet_lt hq measurable_const))

lemma integrable_binarySwitchCount (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (lo hi : ℝ) :
    Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      binarySwitchCount lo hi z.1.1 z.2.1 z.1.2 z.2.2) (independentLaw μ ν) := by
  haveI : IsProbabilityMeasure (independentLaw μ ν) := by
    unfold independentLaw; infer_instance
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_binarySwitchCount lo hi).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (binarySwitchCount_nonneg _ _ _ _ _ _)]
    exact binarySwitchCount_le_one _ _ _ _ _ _

/-- Proposition 5.1: a common bias atom forces a length-independent chance of a switch. -/
theorem atomic_bias_expected_density (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [NoAtoms μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (hε : 0 < ε) :
    (ν.real {0}) ^ 2 / (2 * ε) ≤ independentExpectedDensity μ ν (-ε) ε := by
  classical
  let E : Set ((ℝ × ℝ) × (ℝ × ℝ)) := univ ×ˢ ({0} ×ˢ {0})
  have hE : MeasurableSet E := by dsimp [E]; measurability
  haveI : IsProbabilityMeasure (independentLaw μ ν) := by
    unfold independentLaw; infer_instance
  have hslopes : ∀ᵐ z ∂independentLaw μ ν, z.1.1 ≠ z.1.2 := by
    exact (Measure.quasiMeasurePreserving_fst.ae (iid_slopes_ne μ))
  have hmono : (∫ z, E.indicator (fun _ => (1 : ℝ)) z ∂independentLaw μ ν) ≤
      ∫ z, binarySwitchCount (-ε) ε z.1.1 z.2.1 z.1.2 z.2.2 ∂independentLaw μ ν := by
    apply integral_mono_ae ((integrable_const (1 : ℝ)).indicator hE)
      (integrable_binarySwitchCount μ ν (-ε) ε)
    filter_upwards [hslopes] with z hne
    by_cases hz : z ∈ E
    · have hb : z.2.1 = 0 ∧ z.2.2 = 0 := by
        exact ⟨hz.2.1, hz.2.2⟩
      rw [Set.indicator_of_mem hz]
      rw [hb.1, hb.2]
      simpa using (binarySwitchCount_centered (x₀ := 0) hε hne).ge
    · rw [Set.indicator_of_notMem hz]
      exact binarySwitchCount_nonneg _ _ _ _ _ _
  have hprob : (∫ z, E.indicator (fun _ => (1 : ℝ)) z ∂independentLaw μ ν) =
      (ν.real {0}) ^ 2 := by
    rw [integral_indicator_const (1 : ℝ) hE]
    simp only [smul_eq_mul, mul_one, E, independentLaw, measureReal_def, Measure.prod_prod,
      measure_univ, one_mul, ENNReal.toReal_mul, pow_two]
  rw [hprob] at hmono
  unfold independentExpectedDensity
  convert div_le_div_of_nonneg_right hmono (show 0 ≤ 2 * ε by positivity) using 1; ring

/-- For dependent candidate pairs with bias `-x₀ W`, two iid atomless slopes give one switch. -/
def dependentExpectedDensity (μ : Measure ℝ) (x₀ ε : ℝ) : ℝ :=
  (∫ z, binarySwitchCount (x₀ - ε) (x₀ + ε)
    z.1 (-x₀ * z.1) z.2 (-x₀ * z.2) ∂μ.prod μ) / (2 * ε)

/-- The probabilistic switch conclusion of Proposition 5.2, for every atomless slope law. -/
theorem dependent_bias_expected_density (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NoAtoms μ] (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    dependentExpectedDensity μ x₀ ε = 1 / (2 * ε) := by
  unfold dependentExpectedDensity
  congr 1
  calc
    _ = ∫ _ : ℝ × ℝ, (1 : ℝ) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [iid_slopes_ne μ] with z hz
      exact binarySwitchCount_centered hε hz
    _ = 1 := by simp

/-- The uniform slope distribution in Proposition 5.2. -/
def uniformSlope (a : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Icc (-a) a)

lemma uniformSlope_isProbabilityMeasure {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (uniformSlope a) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

/-- An explicit bounded Lebesgue density for the slope marginal. -/
lemma uniformSlope_density (a : ℝ) :
    uniformSlope a = volume.withDensity
      ((Icc (-a) a).indicator (fun _ => (ENNReal.ofReal (2 * a))⁻¹)) := by
  rw [withDensity_indicator measurableSet_Icc, withDensity_const]
  simp [uniformSlope, ProbabilityTheory.cond, Real.volume_Icc, sub_neg_eq_add, two_mul]

lemma uniformSlope_noAtoms (a : ℝ) : NoAtoms (uniformSlope a) := by
  rw [uniformSlope_density]
  infer_instance

/-- The dependent bias law is the actual pushforward under `W ↦ -x₀ W`. -/
def dependentBiasLaw (a x₀ : ℝ) : Measure ℝ :=
  Measure.map (fun w => -x₀ * w) (uniformSlope a)

/-- Support of the dependent bias density, written through the inverse linear map. -/
def biasSupport (a x₀ : ℝ) : Set ℝ :=
  {y | y / (-x₀) ∈ Icc (-a) a}

lemma measurableSet_biasSupport (a x₀ : ℝ) : MeasurableSet (biasSupport a x₀) := by
  unfold biasSupport
  exact measurableSet_Icc.preimage (measurable_id.div_const _)

/-- An explicit bounded density for the dependent bias marginal. -/
theorem dependentBiasLaw_density (a : ℝ) {x₀ : ℝ} (hx₀ : x₀ ≠ 0) :
    dependentBiasLaw a x₀ = volume.withDensity
      ((biasSupport a x₀).indicator (fun _ =>
        (ENNReal.ofReal (2 * a))⁻¹ * ENNReal.ofReal |(-x₀)⁻¹|)) := by
  let c : ℝ≥0∞ := (ENNReal.ofReal (2 * a))⁻¹
  have hx : -x₀ ≠ 0 := neg_ne_zero.mpr hx₀
  rw [withDensity_indicator (measurableSet_biasSupport a x₀),
    withDensity_const]
  ext s hs
  have hm : Measurable (fun w : ℝ => -x₀ * w) := by fun_prop
  rw [dependentBiasLaw, Measure.map_apply hm hs]
  simp only [uniformSlope, ProbabilityTheory.cond, Measure.smul_apply,
    Measure.restrict_apply (hs.preimage hm),
    Real.volume_Icc, sub_neg_eq_add]
  have hset : (fun w : ℝ => -x₀ * w) ⁻¹' s ∩ Icc (-a) a =
      (fun w : ℝ => -x₀ * w) ⁻¹' (s ∩ biasSupport a x₀) := by
    ext w
    simp [biasSupport, hx₀]
  rw [hset, Real.volume_preimage_mul_left hx]
  simp only [Measure.restrict_apply hs]
  rw [show a + a = 2 * a by ring]
  simp only [smul_eq_mul]
  ring

/-- Proposition 5.2, with the specified uniform law and every positive probe length. -/
theorem marginal_densities_insufficient {a : ℝ} (ha : 0 < a)
    (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    dependentExpectedDensity (uniformSlope a) x₀ ε = 1 / (2 * ε) := by
  letI := uniformSlope_isProbabilityMeasure ha
  letI := uniformSlope_noAtoms a
  exact dependent_bias_expected_density (uniformSlope a) x₀ hε

/-- Affine scores along the unit-speed probe `s ↦ lo+s`. -/
def binaryScores (lo a b c d : ℝ) : Fin 2 → ℝ → ℝ :=
  fun j s => if j = 0 then a * (lo + s) + b else c * (lo + s) + d

/-- Two scalar weights and biases in the original `d=1`, `K=2` score model. -/
def binaryWeights (a c : ℝ) : Fin 2 → Fin 1 → ℝ :=
  fun j _ => if j = 0 then a else c

def binaryBiases (b d : ℝ) : Fin 2 → ℝ :=
  fun j => if j = 0 then b else d

/-- Unit-speed straight probe of the real line. -/
def straightProbe (lo : ℝ) : ℝ → Fin 1 → ℝ := fun s _ => lo + s

lemma binaryScores_eq_affineScores (lo a b c d : ℝ) :
    binaryScores lo a b c d =
      affineScores (binaryWeights a c) (binaryBiases b d) (straightProbe lo) := by
  funext j s
  by_cases h : j = 0 <;>
    simp [binaryScores, affineScores, binaryWeights, binaryBiases, straightProbe, h]

lemma signChanges_of_binarySwitch {lo a b c d s : ℝ}
    (h : BinarySwitchAt a b c d (lo + s)) :
    SignChanges (fun t => binaryScores lo a b c d 0 t -
      binaryScores lo a b c d 1 t) s := by
  have heq (t : ℝ) : binaryScores lo a b c d 0 t -
      binaryScores lo a b c d 1 t = (a - c) * (t - s) := by
    simp [binaryScores]
    linear_combination h.1
  refine ⟨1, zero_lt_one, ?_⟩
  rcases lt_or_gt_of_ne h.2 with hlt | hgt
  · right
    constructor
    · intro t ht
      dsimp only
      rw [heq]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hlt) (sub_neg.mpr ht.2)
    · intro t ht
      dsimp only
      rw [heq]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt) (sub_pos.mpr ht.1)
  · left
    constructor
    · intro t ht
      dsimp only
      rw [heq]
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hgt) (sub_neg.mpr ht.2)
    · intro t ht
      dsimp only
      rw [heq]
      exact mul_pos (sub_pos.mpr hgt) (sub_pos.mpr ht.1)

lemma activeSwitch_binaryScores_iff (lo hi a b c d s : ℝ) :
    ActiveSwitch (binaryScores lo a b c d) (hi - lo) s ↔
      s ∈ Ioo 0 (hi - lo) ∧ BinarySwitchAt a b c d (lo + s) := by
  constructor
  · rintro ⟨h0, hL, i, j, hij, heq, _, hsign⟩
    refine ⟨⟨h0, hL⟩, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all [binaryScores]
    · intro hac
      have hbd : b = d := by
        fin_cases i <;> fin_cases j <;> simp_all [binaryScores]
      have hz : (fun t => binaryScores lo a b c d i t -
          binaryScores lo a b c d j t) = (fun _ => 0) := by
        funext t
        simp [binaryScores, hac, hbd]
      rw [hz] at hsign
      exact signChanges_zero s hsign
  · rintro ⟨⟨h0, hL⟩, hbin⟩
    refine ⟨h0, hL, 0, 1, by decide, ?_, ?_, signChanges_of_binarySwitch hbin⟩
    · simpa [binaryScores] using hbin.1
    · intro k hk0 hk1
      fin_cases k <;> simp_all

/-- The simplified binary count agrees with the paper's parameter-counting definition. -/
theorem switchCount_binaryScores (lo hi a b c d : ℝ) :
    switchCount (binaryScores lo a b c d) (hi - lo) =
      ENNReal.ofReal (binarySwitchCount lo hi a b c d) := by
  classical
  let q := meetingPoint a b c d
  by_cases h : a ≠ c ∧ lo < q ∧ q < hi
  · have hs : switchSet (binaryScores lo a b c d) (hi - lo) = {q - lo} := by
      ext s
      simp only [switchSet, Set.mem_setOf_eq, activeSwitch_binaryScores_iff,
        binarySwitchAt_iff, mem_singleton_iff]
      constructor
      · rintro ⟨_, _, heq⟩
        change lo + s = q at heq
        linarith
      · intro heq
        subst s
        refine ⟨⟨by linarith [h.2.1], by linarith [h.2.2]⟩, h.1, ?_⟩
        dsimp [q]
        ring
    simp [switchCount, hs, binarySwitchCount, h, q]
  · have hs : switchSet (binaryScores lo a b c d) (hi - lo) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro s hs
      rcases (activeSwitch_binaryScores_iff _ _ _ _ _ _ _).1 hs with ⟨⟨h0, hL⟩, hb⟩
      rcases (binarySwitchAt_iff _ _ _ _ _).1 hb with ⟨hne, heq⟩
      apply h
      change lo + s = q at heq
      exact ⟨hne, by linarith, by linarith⟩
    simp [switchCount, hs, binarySwitchCount, h, q]

/-- Expected binary counts also agree with the source-semantic nonnegative integral. -/
theorem independentExpectedDensity_source (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (lo hi : ℝ) :
    independentExpectedDensity μ ν lo hi =
      (expectedSwitchCount (independentLaw μ ν)
        (fun z => binaryScores lo z.1.1 z.2.1 z.1.2 z.2.2) (hi - lo)).toReal /
          (hi - lo) := by
  unfold independentExpectedDensity expectedSwitchCount
  simp_rw [switchCount_binaryScores]
  congr 1
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun z => binarySwitchCount_nonneg _ _ _ _ _ _)
    (measurable_binarySwitchCount lo hi).aestronglyMeasurable

/-- Explicit finite bound on the slope density; no regularity hypothesis is supplied. -/
theorem uniformSlope_has_bounded_density {a : ℝ} (ha : 0 < a) :
    ∃ f : ℝ → ℝ≥0∞, ∃ C : ℝ≥0∞, Measurable f ∧ C ≠ ∞ ∧
      (∀ y, f y ≤ C) ∧ uniformSlope a = volume.withDensity f := by
  refine ⟨(Icc (-a) a).indicator (fun _ => (ENNReal.ofReal (2 * a))⁻¹),
    (ENNReal.ofReal (2 * a))⁻¹, measurable_const.indicator measurableSet_Icc, ?_, ?_,
    uniformSlope_density a⟩
  · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  · intro y
    by_cases hy : y ∈ Icc (-a) a <;> simp [hy]

/-- Explicit finite bound on the dependent bias density. -/
theorem dependentBiasLaw_has_bounded_density {a x₀ : ℝ} (ha : 0 < a) (hx₀ : x₀ ≠ 0) :
    ∃ f : ℝ → ℝ≥0∞, ∃ C : ℝ≥0∞, Measurable f ∧ C ≠ ∞ ∧
      (∀ y, f y ≤ C) ∧ dependentBiasLaw a x₀ = volume.withDensity f := by
  let C : ℝ≥0∞ := (ENNReal.ofReal (2 * a))⁻¹ * ENNReal.ofReal |(-x₀)⁻¹|
  refine ⟨(biasSupport a x₀).indicator (fun _ => C), C,
    measurable_const.indicator (measurableSet_biasSupport a x₀), ?_, ?_,
    dependentBiasLaw_density a hx₀⟩
  · exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)))
      ENNReal.ofReal_ne_top
  · intro y
    by_cases hy : y ∈ biasSupport a x₀ <;> simp [hy]

/-- A deterministic conditional bias is singular with respect to Lebesgue measure. -/
theorem dependent_conditional_bias_not_absolutelyContinuous (x₀ w : ℝ) :
    ¬ Measure.dirac (-x₀ * w) ≪ (volume : Measure ℝ) := by
  intro h
  have hz := h (measure_singleton (-x₀ * w) : volume {-x₀ * w} = 0)
  simp at hz

/-- The expected source-defined switch density, on the same independent sample space. -/
def expectedIndependentSourceDensity (μ ν : Measure ℝ) (lo hi : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, switchDensity (binaryScores lo z.1.1 z.2.1 z.1.2 z.2.2) (hi - lo)
    ∂independentLaw μ ν

lemma expectedIndependentSourceDensity_eq (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {lo hi : ℝ} (hL : lo < hi) :
    expectedIndependentSourceDensity μ ν lo hi =
      ENNReal.ofReal (independentExpectedDensity μ ν lo hi) := by
  unfold expectedIndependentSourceDensity switchDensity independentExpectedDensity
  simp_rw [switchCount_binaryScores, div_eq_mul_inv]
  rw [lintegral_mul_const _ (measurable_binarySwitchCount lo hi).ennreal_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_binarySwitchCount μ ν lo hi)
    (Filter.Eventually.of_forall fun z => binarySwitchCount_nonneg _ _ _ _ _ _)]
  exact (ENNReal.ofReal_div_of_pos (sub_pos.mpr hL)).symm

/-- Proposition 5.1 stated using the original visible-switch set and its density. -/
theorem atomic_bias_source_density (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [NoAtoms μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal ((ν.real {0}) ^ 2 / (2 * ε)) ≤
      expectedIndependentSourceDensity μ ν (-ε) ε := by
  rw [expectedIndependentSourceDensity_eq μ ν (by linarith)]
  exact ENNReal.ofReal_le_ofReal (atomic_bias_expected_density μ ν hε)

/-- Proposition 5.2: the source-defined visible-switch density has the claimed exact mean. -/
theorem dependent_bias_source_density (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NoAtoms μ] (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ z : ℝ × ℝ,
      switchDensity (binaryScores (x₀ - ε) z.1 (-x₀ * z.1) z.2 (-x₀ * z.2))
        (2 * ε) ∂μ.prod μ) = (1 : ℝ≥0∞) / ENNReal.ofReal (2 * ε) := by
  have hL : (x₀ + ε) - (x₀ - ε) = 2 * ε := by ring
  calc
    _ = ∫⁻ _ : ℝ × ℝ, (1 : ℝ≥0∞) / ENNReal.ofReal (2 * ε) ∂μ.prod μ := by
      apply lintegral_congr_ae
      filter_upwards [iid_slopes_ne μ] with z hz
      unfold switchDensity
      rw [← hL, switchCount_binaryScores, binarySwitchCount_centered hε hz]
      simp
    _ = _ := by simp

/-- Both bounded marginal densities coexist with the exact divergent local switch density. -/
theorem proposition_5_2 {a x₀ : ℝ} (ha : 0 < a) (hx₀ : x₀ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    (∃ f : ℝ → ℝ≥0∞, ∃ C : ℝ≥0∞, Measurable f ∧ C ≠ ∞ ∧
      (∀ y, f y ≤ C) ∧ uniformSlope a = volume.withDensity f) ∧
    (∃ f : ℝ → ℝ≥0∞, ∃ C : ℝ≥0∞, Measurable f ∧ C ≠ ∞ ∧
      (∀ y, f y ≤ C) ∧ dependentBiasLaw a x₀ = volume.withDensity f) ∧
    (∫⁻ z : ℝ × ℝ,
      switchDensity (binaryScores (x₀ - ε) z.1 (-x₀ * z.1) z.2 (-x₀ * z.2))
        (2 * ε) ∂(uniformSlope a).prod (uniformSlope a)) =
      (1 : ℝ≥0∞) / ENNReal.ofReal (2 * ε) := by
  letI := uniformSlope_isProbabilityMeasure ha
  letI := uniformSlope_noAtoms a
  exact ⟨uniformSlope_has_bounded_density ha, dependentBiasLaw_has_bounded_density ha hx₀,
    dependent_bias_source_density (uniformSlope a) x₀ hε⟩

/-- The atomic-bias expected local densities admit no finite uniform bound. -/
theorem atomic_bias_densities_unbounded (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [NoAtoms μ] [IsProbabilityMeasure ν]
    (hp : 0 < ν.real {0}) (C : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ C < independentExpectedDensity μ ν (-ε) ε := by
  let p := ν.real {0}
  let ε := p ^ 2 / (2 * (|C| + 1))
  have hp' : 0 < p := hp
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hp0 : p ≠ 0 := ne_of_gt hp'
  have hc0 : |C| + 1 ≠ 0 := by positivity
  have hratio : p ^ 2 / (2 * ε) = |C| + 1 := by
    dsimp [ε]
    field_simp [hp0, hc0]
  refine ⟨ε, hε, lt_of_lt_of_le ?_ (atomic_bias_expected_density μ ν hε)⟩
  change C < p ^ 2 / (2 * ε)
  rw [hratio]
  linarith [le_abs_self C]

end Paper35.Counterexamples

import Paper35.ExactCrossing
import Paper35.SharpnessLimit

/-! Shrinking-segment sharpness of the heterogeneous common-reference bound
at rank two. The two slopes are deterministic and opposite; biases have the
actual independent uniform conditional densities. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
namespace Paper35.HeterogeneousSharpness
open Source Source.WeightedModel Sharpness Source.CrossingSlice Source.ExactCrossing
variable {d : ℕ}

def slope (i : Fin d) (k : Fin 2) : Space d := if k = 0 then axis i else -axis i

def candidate (i : Fin d) (k : Fin 2) : WeightedModel d :=
  independentUniformModel (Measure.dirac (slope i k)) 1 (by norm_num)

/-- An actual admissible heterogeneous source model with deterministic slopes
+1 and -1 and independent uniform biases of density height one. -/
def model (i : Fin d) : Heterogeneous.Model d 2 where
  candidate := candidate i
  B := fun _ => 1
  constantEnvelope := fun _ => Filter.Eventually.of_forall fun _ => by
    simp [candidate,independentUniformModel]
  firstMoment := fun _ => by
    simp only [candidate, independentUniformModel]
    exact integrable_dirac (by simp)

lemma inner_axis_self (i : Fin d) : inner ℝ (axis i) (axis i) = 1 := by
  rw [real_inner_self_eq_norm_sq]
  simp [axis]

lemma mixedKernel_opposite (i : Fin d) (t y : ℝ) :
    mixedKernel (candidate i 0) (candidate i 1) (t • axis i) (axis i) y =
      2 * biasDensity 1 (y-t) * biasDensity 1 (y+t) := by
  rw [mixedKernel_eq_weights]
  simp only [candidate,independentUniformModel,lintegral_dirac]
  simp only [slope, Fin.isValue, ↓reduceIte, one_ne_zero, inner_add_left,
    inner_neg_left, inner_smul_right, inner_axis_self, mul_one, sub_neg_eq_add]
  norm_num

lemma pairIntensity_opposite (i : Fin d) (t y : ℝ) :
    (model i).pairIntensity (t • axis i) (axis i) y =
      2 * biasDensity 1 (y-t) * biasDensity 1 (y+t) := by
  have hprod : ((Finset.univ : Finset (Fin 2)).erase 0).erase 1 = ∅ := by decide
  have hm := mixedKernel_opposite i t y
  simpa [Heterogeneous.Model.pairIntensity, Heterogeneous.Model.visibility,
    Heterogeneous.Model.kernel, model, Fin.sum_univ_two, Source.CrossingSlice.mixedKernel, hprod] using hm

lemma commonReference_opposite (i : Fin d) :
    (⨅ c : ℝ, ∑ k : Fin 2, ((model i).B k : ℝ≥0∞) *
      (model i).centeredMoment (axis i) c k) = 2 := by
  have heq (c : ℝ) :
      (∑ k : Fin 2, ((model i).B k : ℝ≥0∞) * (model i).centeredMoment (axis i) c k) =
        ENNReal.ofReal (|1-c| + |-1-c|) := by
    simp only [Fin.sum_univ_two, model, Heterogeneous.Model.centeredMoment,
      candidate, independentUniformModel, slope, ↓reduceIte, one_ne_zero,
      lintegral_dirac, inner_neg_left, inner_axis_self, ENNReal.coe_one, one_mul]
    exact (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).symm
  simp_rw [heq]
  apply le_antisymm
  · exact (iInf_le _ 0).trans_eq (by norm_num)
  · apply le_iInf
    intro c
    have hreal : (2 : ℝ) ≤ |1-c| + |-1-c| := by
      calc
        2 = |1-(-1 : ℝ)| := by norm_num
        _ ≤ |1-c| + |c-(-1)| := abs_sub_le _ _ _
        _ = _ := by rw [abs_sub_comm c (-1)]
    simpa using ENNReal.ofReal_le_ofReal hreal

lemma integrated_pairIntensity_bounds (i : Fin d) {ε t : ℝ}
    (ht : |t| ≤ ε/2) :
    ENNReal.ofReal (2*(1-ε)) ≤
      (∫⁻ y, (model i).pairIntensity (t • axis i) (axis i) y) ∧
      (∫⁻ y, (model i).pairIntensity (t • axis i) (axis i) y) ≤ 2 := by
  simp_rw [pairIntensity_opposite]
  constructor
  · let D : Set ℝ := Icc (-1/2 + ε/2) (1/2 - ε/2)
    have hD : MeasurableSet D := measurableSet_Icc
    have hlow (y : ℝ) : D.indicator (fun _ => (2 : ℝ≥0∞)) y ≤
        2 * biasDensity 1 (y-t) * biasDensity 1 (y+t) := by
      by_cases hy : y ∈ D
      · obtain ⟨ht0,ht1⟩ := abs_le.mp ht
        have hm : y-t ∈ Icc (-biasHalfWidth 1) (biasHalfWidth 1) := by
          simp only [biasHalfWidth, mul_one]
          constructor <;> dsimp only [D] at hy <;> linarith [hy.1,hy.2]
        have hp : y+t ∈ Icc (-biasHalfWidth 1) (biasHalfWidth 1) := by
          simp only [biasHalfWidth, mul_one]
          constructor <;> dsimp only [D] at hy <;> linarith [hy.1,hy.2]
        simp only [Set.indicator_of_mem hy, biasDensity, Set.indicator_of_mem hm,
          Set.indicator_of_mem hp, ENNReal.ofReal_one, mul_one, le_refl]
      · rw [Set.indicator_of_notMem hy]
        exact zero_le _
    have hmass : (∫⁻ y, D.indicator (fun _ => (2 : ℝ≥0∞)) y) =
        ENNReal.ofReal (2*(1-ε)) := by
      rw [lintegral_indicator hD]
      simp only [lintegral_const, Measure.restrict_apply_univ, D, Real.volume_Icc]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [← hmass]
    exact lintegral_mono hlow
  · calc
      _ ≤ ∫⁻ y, 2 * biasDensity 1 (y-t) := by
        apply lintegral_mono
        intro y
        simpa only [ENNReal.ofReal_one, mul_one] using mul_le_mul_left' (biasDensity_le 1 (y+t))
          (2 * biasDensity 1 (y-t))
      _ = 2 * ∫⁻ y, biasDensity 1 (y-t) :=
        lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
      _ = 2 := by
        rw [lintegral_sub_right_eq_self, biasDensity_normalized (by norm_num : (0:ℝ) < 1), mul_one]

/-- Actual source expectation on the positive-length centered segment,
with lower and upper bounds converging to the common-reference intensity two. -/
theorem expectedCount_bounds (i : Fin d) {ε : ℝ} (hε : 0 < ε)
    (hLN : VisibleCrossing.LusinNovikovInput (Fin 2 → Candidate d)
      (VisibleCrossing.ProbeParameter (centeredProbe i ε hε)))
    (hUP : VisibleCrossing.BorelProjectionNullMeasurableInput
      (VisibleCrossing.WeightPair d × VisibleCrossing.BiasPair)
      (VisibleCrossing.ProbeParameter (centeredProbe i ε hε))) :
    ENNReal.ofReal ε * ENNReal.ofReal (2*(1-ε)) ≤
        (model i).expectedCount (centeredProbe i ε hε) ∧
      (model i).expectedCount (centeredProbe i ε hε) ≤ ENNReal.ofReal ε * 2 := by
  have hc := heterogeneous_crossing_identity (centeredProbe i ε hε) (candidate i) hLN hUP
  have hprod : ((Finset.univ : Finset (Fin 2)).erase 0).erase 1 = ∅ := by decide
  have hsum (x u : Space d) (y : ℝ) :
      (∑ q : OrderedCandidatePair 2,
        (∏ k ∈ (Finset.univ.erase q.1.1).erase q.1.2, (candidate i k).scoreCDF x y) *
          mixedKernel (candidate i q.1.1) (candidate i q.1.2) x u y) =
        (model i).pairIntensity x u y :=
    sum_orderedCandidatePair 2 (fun a b =>
      (model i).visibility x y a b * (model i).kernel x u y a b)
  simp_rw [hsum] at hc
  change (model i).expectedCount (centeredProbe i ε hε) =
    ∫⁻ s in Icc 0 ε, ∫⁻ y,
      (model i).pairIntensity (centeredCurve i ε s) (deriv (centeredCurve i ε) s) y at hc
  simp_rw [centeredCurve_deriv] at hc
  rw [hc]
  have hp (s : ℝ) (hs : s ∈ Icc 0 ε) :
      ENNReal.ofReal (2*(1-ε)) ≤
        (∫⁻ y, (model i).pairIntensity (centeredCurve i ε s) (axis i) y) ∧
      (∫⁻ y, (model i).pairIntensity (centeredCurve i ε s) (axis i) y) ≤ 2 :=
    integrated_pairIntensity_bounds i (abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩)
  constructor
  · calc
      _ = ∫⁻ _s in Icc 0 ε, ENNReal.ofReal (2*(1-ε)) := by
        simp [Real.volume_Icc, mul_comm]
      _ ≤ _ := setLIntegral_mono' measurableSet_Icc (fun s hs => (hp s hs).1)
  · calc
      _ ≤ ∫⁻ _s in Icc 0 ε, (2 : ℝ≥0∞) :=
        setLIntegral_mono' measurableSet_Icc (fun s hs => (hp s hs).2)
      _ = _ := by simp [Real.volume_Icc, mul_comm]

/-- Expected switches divided by actual positive geometric segment length. -/
def expectedDensity (i : Fin d) (ε : ℝ) : ℝ :=
  if hε : 0 < ε then
    ((model i).expectedCount (centeredProbe i ε hε) / ENNReal.ofReal ε).toReal else 0

theorem expectedDensity_bounds (i : Fin d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hLN : VisibleCrossing.LusinNovikovInput (Fin 2 → Candidate d)
      (VisibleCrossing.ProbeParameter (centeredProbe i ε hε)))
    (hUP : VisibleCrossing.BorelProjectionNullMeasurableInput
      (VisibleCrossing.WeightPair d × VisibleCrossing.BiasPair)
      (VisibleCrossing.ProbeParameter (centeredProbe i ε hε))) :
    2*(1-ε) ≤ expectedDensity i ε ∧ expectedDensity i ε ≤ 2 := by
  obtain ⟨hl,hu⟩ := expectedCount_bounds i hε hLN hUP
  have hL0 : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hlo := ENNReal.div_le_div_right hl (ENNReal.ofReal ε)
  have hup := ENNReal.div_le_div_right hu (ENNReal.ofReal ε)
  rw [mul_comm (ENNReal.ofReal ε), ENNReal.mul_div_cancel_right hL0 ENNReal.ofReal_ne_top] at hlo hup
  have hfin := ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hup
  have hrlo := ENNReal.toReal_mono hfin hlo
  have hrup := ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hup
  rw [expectedDensity,dif_pos hε]
  constructor
  · simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*(1-ε))] using hrlo
  · simpa only [ENNReal.toReal_ofNat] using hrup

/-- Rank-two pointwise common-reference sharpness, realized by actual
positive-length probes and actual independent candidate laws. -/
theorem expectedDensity_tendsto_two (i : Fin d)
    (hLN : ∀ p : Probe d, VisibleCrossing.LusinNovikovInput
      (Fin 2 → Candidate d) (VisibleCrossing.ProbeParameter p))
    (hUP : ∀ p : Probe d, VisibleCrossing.BorelProjectionNullMeasurableInput
      (VisibleCrossing.WeightPair d × VisibleCrossing.BiasPair) (VisibleCrossing.ProbeParameter p)) :
    Tendsto (expectedDensity i) (𝓝[>] (0 : ℝ)) (𝓝 2) := by
  have hlo : Tendsto (fun ε : ℝ => 2*(1-ε)) (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    have hzero : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := tendsto_const_nhds
    have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := tendsto_const_nhds
    simpa only [sub_zero, mul_one] using htwo.mul (hone.sub hzero)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with ε hε hε1
    exact (expectedDensity_bounds i hε hε1 (hLN _) (hUP _)).1
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with ε hε hε1
    exact (expectedDensity_bounds i hε hε1 (hLN _) (hUP _)).2

/-- The normalized expectation above is exactly the expectation of the
original random switch-density observable, rather than a replacement variable. -/
theorem expectedDensity_eq_actual (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    expectedDensity i ε =
      (∫⁻ θ, switchDensity (scores (centeredProbe i ε hε) θ) ε ∂(model i).joint).toReal := by
  rw [expectedDensity,dif_pos hε]
  congr 1
  unfold Heterogeneous.Model.expectedCount expectedSwitchCount switchDensity
  simp only [div_eq_mul_inv]
  exact (lintegral_mul_const' _ _
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hε).ne')).symm

theorem integrated_commonReference (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ s in Icc 0 ε, ⨅ c : ℝ, ∑ k : Fin 2, ((model i).B k : ℝ≥0∞) *
      (model i).centeredMoment (deriv (centeredProbe i ε hε).curve s) c k) =
        ENNReal.ofReal ε * 2 := by
  change (∫⁻ s in Icc 0 ε, ⨅ c : ℝ, ∑ k : Fin 2, ((model i).B k : ℝ≥0∞) *
    (model i).centeredMoment (deriv (centeredCurve i ε) s) c k) = _
  simp_rw [centeredCurve_deriv,commonReference_opposite]
  simp [Real.volume_Icc,mul_comm]

/-- No coefficient below one can multiply the pointwise-infimum common
reference bound uniformly, already on these rank-two positive-length probes. -/
theorem commonReference_coefficient_optimal (i : Fin d)
    (hLN : ∀ p : Probe d, VisibleCrossing.LusinNovikovInput
      (Fin 2 → Candidate d) (VisibleCrossing.ProbeParameter p))
    (hUP : ∀ p : Probe d, VisibleCrossing.BorelProjectionNullMeasurableInput
      (VisibleCrossing.WeightPair d × VisibleCrossing.BiasPair) (VisibleCrossing.ProbeParameter p))
    (C : ℝ) (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 → expectedDensity i ε ≤ C*2) :
    1 ≤ C := by
  have hlim := expectedDensity_tendsto_two i hLN hUP
  have hle : (2 : ℝ) ≤ C*2 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with ε hε hε1
    exact hbound ε hε hε1
  linarith

end Paper35.HeterogeneousSharpness

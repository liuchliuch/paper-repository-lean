import Paper35.SourceModel
import Paper35.VisibleCrossing
import Paper35.Visibility
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Sharp weighted visibility for the actual conditional maxout model

This module proves Lemma 4.1 with the source's score CDF, conditional-density
slope slices, crossing kernel, envelope tilt, and directional Gini functional.
The proof combines the sharp opposite-mass estimate with two actual layer-cake
identities and Tonelli; the CDF normalization is proved in `VisibleCrossing`.
All integrals remain nonnegative extended-valued, so no first moment is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Paper35.VisibilityKernel

/-- The real opposite-mass estimate extends to nonnegative integrals without
assuming a finite first projected-weight moment. -/
theorem lintegral_opposite_mass_bound {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (qplus qminus : α → ℝ≥0∞)
    (hplus : Measurable qplus) (hminus : Measurable qminus)
    {B p T : ℝ} (hB : 0 ≤ B) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT0 : 0 ≤ T)
    (hplusB : ∀ y, qplus y ≤ ENNReal.ofReal (B * p))
    (hminusB : ∀ y, qminus y ≤ ENNReal.ofReal (B * (1 - p)))
    (hT : (∫⁻ y, qplus y + qminus y ∂ν) = ENNReal.ofReal T) :
    (∫⁻ y, qplus y * qminus y ∂ν) ≤ ENNReal.ofReal (B * T * p * (1 - p)) := by
  have hpfin (y) : qplus y ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hplusB y)
  have hmfin (y) : qminus y ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hminusB y)
  have hpint : Integrable (fun y => (qplus y).toReal) ν := by
    apply integrable_toReal_of_lintegral_ne_top hplus.aemeasurable
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    rw [← hT]
    exact lintegral_mono fun y => le_add_right le_rfl
  have hmint : Integrable (fun y => (qminus y).toReal) ν := by
    apply integrable_toReal_of_lintegral_ne_top hminus.aemeasurable
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    rw [← hT]
    exact lintegral_mono fun y => le_add_left le_rfl
  have hnorm : (∫ y, (qplus y).toReal + (qminus y).toReal ∂ν) = T := by
    calc
      _ = ∫ y, (qplus y + qminus y).toReal ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => (ENNReal.toReal_add (hpfin y) (hmfin y)).symm
      _ = (∫⁻ y, qplus y + qminus y ∂ν).toReal :=
        integral_toReal (hplus.add hminus).aemeasurable
          (Filter.Eventually.of_forall fun y => ENNReal.add_lt_top.2 ⟨(hpfin y).lt_top, (hmfin y).lt_top⟩)
      _ = T := by rw [hT, ENNReal.toReal_ofReal hT0]
  have hpB : ∀ᵐ y ∂ν, (qplus y).toReal ≤ B * p :=
    Filter.Eventually.of_forall fun y => by
      simpa [ENNReal.toReal_ofReal (mul_nonneg hB hp0)] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hplusB y)
  have hmB : ∀ᵐ y ∂ν, (qminus y).toReal ≤ B * (1 - p) :=
    Filter.Eventually.of_forall fun y => by
      simpa [ENNReal.toReal_ofReal (mul_nonneg hB (sub_nonneg.mpr hp1))] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hminusB y)
  obtain ⟨hprod, hbound⟩ := Visibility.integrated_opposite_mass_bound hB hp0 hp1 hpint hmint
    (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hpB hmB hnorm
  calc
    _ = ∫⁻ y, ENNReal.ofReal ((qplus y).toReal * (qminus y).toReal) ∂ν := by
      apply lintegral_congr
      intro y
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (hpfin y), ENNReal.ofReal_toReal (hmfin y)]
    _ = ENNReal.ofReal (∫ y, (qplus y).toReal * (qminus y).toReal ∂ν) :=
      (ofReal_integral_eq_lintegral_ofReal hprod
        (Filter.Eventually.of_forall fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

open Source Source.WeightedModel

/-- The genuine conditional bias-density slice at score height `y`. -/
def sliceDensity {d : ℕ} (m : WeightedModel d) (x : Space d) (w : Space d) (y : ℝ) : ℝ≥0∞ :=
  m.g w (y - inner ℝ w x)

lemma measurable_sliceDensity {d : ℕ} (m : WeightedModel d) (x : Space d) :
    Measurable (Function.uncurry (sliceDensity m x)) := by
  change Measurable (fun p : Space d × ℝ => m.g p.1 (p.2 - inner ℝ p.1 x))
  exact m.measurable_g.comp
    (measurable_fst.prodMk (measurable_snd.sub (by fun_prop)))

lemma sliceMass_le_average {d : ℕ} (m : WeightedModel d) (x : Space d) (y : ℝ) :
    (∫⁻ w, sliceDensity m x w y ∂m.weights) ≤ m.average := by
  apply lintegral_mono_ae
  filter_upwards [m.bound] with w hw
  exact hw (y - inner ℝ w x)

lemma slopeSlice_finite {d : ℕ} (m : WeightedModel d) (x u : Space d) (y : ℝ) :
    IsFiniteMeasure (m.slopeSlice x u y) := by
  haveI := m.probability
  haveI : IsFiniteMeasure (m.weights.withDensity (fun w => sliceDensity m x w y)) :=
    isFiniteMeasure_withDensity
      (ne_top_of_le_ne_top m.average_finite.ne (sliceMass_le_average m x y))
  change IsFiniteMeasure ((m.weights.withDensity (fun w => sliceDensity m x w y)).map
    (fun w => inner ℝ w u))
  exact Measure.isFiniteMeasure_map _ _

/-- Actual slope-slice tail masses, exactly (4.3) and (4.4). -/
def qplus {d : ℕ} (m : WeightedModel d) (x u : Space d) (y r : ℝ) : ℝ≥0∞ :=
  m.slopeSlice x u y (Ioi r)

def qminus {d : ℕ} (m : WeightedModel d) (x u : Space d) (y r : ℝ) : ℝ≥0∞ :=
  m.slopeSlice x u y (Iic r)

lemma qplus_integral {d : ℕ} (m : WeightedModel d) (x u : Space d) (y r : ℝ) :
    qplus m x u y r = ∫⁻ w in {w | r < inner ℝ w u}, sliceDensity m x w y ∂m.weights := by
  have hA : Measurable (fun w : Space d => inner ℝ w u) := by fun_prop
  unfold qplus slopeSlice
  rw [Measure.map_apply hA measurableSet_Ioi]
  change (m.weights.withDensity (fun w => sliceDensity m x w y))
    {w | r < inner ℝ w u} = _
  rw [withDensity_apply _ (measurableSet_lt measurable_const hA)]

lemma qminus_integral {d : ℕ} (m : WeightedModel d) (x u : Space d) (y r : ℝ) :
    qminus m x u y r = ∫⁻ w in {w | inner ℝ w u ≤ r}, sliceDensity m x w y ∂m.weights := by
  have hA : Measurable (fun w : Space d => inner ℝ w u) := by fun_prop
  unfold qminus slopeSlice
  rw [Measure.map_apply hA measurableSet_Iic]
  change (m.weights.withDensity (fun w => sliceDensity m x w y))
    {w | inner ℝ w u ≤ r} = _
  rw [withDensity_apply _ (measurableSet_le hA measurable_const)]

lemma crossingKernel_layerCake {d : ℕ} (m : WeightedModel d) (x u : Space d) (y : ℝ) :
    m.crossingKernel x u y = 2 * ∫⁻ r, qminus m x u y r * qplus m x u y r := by
  haveI := slopeSlice_finite m x u y
  unfold crossingKernel
  rw [← lintegral_prod (fun z : ℝ × ℝ => ENNReal.ofReal |z.1 - z.2|)
    ((measurable_fst.sub measurable_snd).abs).ennreal_ofReal.aemeasurable]
  exact Visibility.gini_layer_cake (m.slopeSlice x u y)

lemma measurable_qplus {d : ℕ} (m : WeightedModel d) (x u : Space d) :
    Measurable (Function.uncurry (qplus m x u)) := by
  letI := m.probability
  have hg : Measurable (fun p : (ℝ × ℝ) × Space d => sliceDensity m x p.2 p.1.1) :=
    (measurable_sliceDensity m x).comp (measurable_snd.prodMk measurable_fst.fst)
  have hs : MeasurableSet {p : (ℝ × ℝ) × Space d | p.1.2 < inner ℝ p.2 u} :=
    measurableSet_lt measurable_fst.snd (by fun_prop)
  have hmeas := (hg.indicator hs).lintegral_prod_right' (ν := m.weights)
  convert hmeas using 1
  funext p
  dsimp only [Function.uncurry]
  rw [qplus_integral, ← lintegral_indicator]
  · rfl
  · exact measurableSet_lt measurable_const (by fun_prop)

lemma measurable_qminus {d : ℕ} (m : WeightedModel d) (x u : Space d) :
    Measurable (Function.uncurry (qminus m x u)) := by
  letI := m.probability
  have hg : Measurable (fun p : (ℝ × ℝ) × Space d => sliceDensity m x p.2 p.1.1) :=
    (measurable_sliceDensity m x).comp (measurable_snd.prodMk measurable_fst.fst)
  have hs : MeasurableSet {p : (ℝ × ℝ) × Space d | inner ℝ p.2 u ≤ p.1.2} :=
    measurableSet_le (by fun_prop) measurable_fst.snd
  have hmeas := (hg.indicator hs).lintegral_prod_right' (ν := m.weights)
  convert hmeas using 1
  funext p
  dsimp only [Function.uncurry]
  rw [qminus_integral, ← lintegral_indicator]
  · rfl
  · exact measurableSet_le (by fun_prop) measurable_const

lemma qplus_add_qminus {d : ℕ} (m : WeightedModel d) (x u : Space d) (y r : ℝ) :
    qplus m x u y r + qminus m x u y r = ∫⁻ w, sliceDensity m x w y ∂m.weights := by
  rw [qplus_integral, qminus_integral]
  have hA : Measurable (fun w : Space d => inner ℝ w u) := by fun_prop
  have hc : {w : Space d | r < inner ℝ w u}ᶜ = {w | inner ℝ w u ≤ r} := by
    ext w; simp
  rw [← hc]
  exact lintegral_add_compl _ (measurableSet_lt measurable_const hA)

lemma tilted_probability {d : ℕ} (m : WeightedModel d) : IsProbabilityMeasure m.tilted := by
  constructor
  rw [tilted, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const _ m.measurable_b₀.coe_nnreal_ennreal]
  exact ENNReal.mul_inv_cancel m.average_pos.ne' m.average_finite.ne

/-- The true tilted projected-slope law. -/
def tiltedProjection {d : ℕ} (m : WeightedModel d) (u : Space d) : Measure ℝ :=
  m.tilted.map (fun w => inner ℝ w u)

lemma tiltedProjection_probability {d : ℕ} (m : WeightedModel d) (u : Space d) :
    IsProbabilityMeasure (tiltedProjection m u) := by
  letI := tilted_probability m
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma envelope_mass_eq {d : ℕ} (m : WeightedModel d) (S : Set (Space d)) (hS : MeasurableSet S) :
    (∫⁻ w in S, (m.b₀ w : ℝ≥0∞) ∂m.weights) = m.average * m.tilted S := by
  rw [tilted, withDensity_apply _ hS]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const _ m.measurable_b₀.coe_nnreal_ennreal]
  exact (ENNReal.mul_div_cancel m.average_pos.ne' m.average_finite.ne).symm

lemma qplus_le_tilt {d : ℕ} (m : WeightedModel d) (x u : Space d) (y r : ℝ) :
    qplus m x u y r ≤ m.average * tiltedProjection m u (Ioi r) := by
  have hA : Measurable (fun w : Space d => inner ℝ w u) := by fun_prop
  rw [qplus_integral, tiltedProjection, Measure.map_apply hA measurableSet_Ioi]
  change (∫⁻ w in {w | r < inner ℝ w u}, sliceDensity m x w y ∂m.weights) ≤
    m.average * m.tilted {w | r < inner ℝ w u}
  rw [← envelope_mass_eq m _ (measurableSet_lt measurable_const hA)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae m.bound] with w hw
  exact hw (y - inner ℝ w x)

lemma qminus_le_tilt {d : ℕ} (m : WeightedModel d) (x u : Space d) (y r : ℝ) :
    qminus m x u y r ≤ m.average * tiltedProjection m u (Iic r) := by
  have hA : Measurable (fun w : Space d => inner ℝ w u) := by fun_prop
  rw [qminus_integral, tiltedProjection, Measure.map_apply hA measurableSet_Iic]
  change (∫⁻ w in {w | inner ℝ w u ≤ r}, sliceDensity m x w y ∂m.weights) ≤
    m.average * m.tilted {w | inner ℝ w u ≤ r}
  rw [← envelope_mass_eq m _ (measurableSet_le hA measurable_const)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae m.bound] with w hw
  exact hw (y - inner ℝ w x)

/-- The exact projected Gini identity for the source's own tilted measure. -/
lemma directionalGini_layerCake {d : ℕ} (m : WeightedModel d) (u : Space d) :
    m.directionalGini u =
      2 * ∫⁻ r, tiltedProjection m u (Iic r) * tiltedProjection m u (Ioi r) := by
  letI := tilted_probability m
  letI := tiltedProjection_probability m u
  have hA : Measurable (fun w : Space d => inner ℝ w u) := by fun_prop
  have hid (w w' : Space d) : inner ℝ u (w - w') = inner ℝ w u - inner ℝ w' u := by
    rw [inner_sub_right, real_inner_comm u w, real_inner_comm u w']
  unfold directionalGini
  simp_rw [hid]
  calc
    _ = ∫⁻ z : Space d × Space d,
        ENNReal.ofReal |inner ℝ z.1 u - inner ℝ z.2 u| ∂m.tilted.prod m.tilted :=
      (lintegral_prod _ ((hA.comp measurable_fst).sub
        (hA.comp measurable_snd)).abs.ennreal_ofReal.aemeasurable).symm
    _ = ∫⁻ z : ℝ × ℝ, ENNReal.ofReal |z.1 - z.2|
        ∂(tiltedProjection m u).prod (tiltedProjection m u) := by
      symm
      rw [tiltedProjection, Measure.map_prod_map m.tilted m.tilted hA hA,
        lintegral_map ((measurable_fst.sub measurable_snd).abs.ennreal_ofReal)
          (hA.prodMap hA)]
      rfl
    _ = _ := Visibility.gini_layer_cake (tiltedProjection m u)

lemma measurable_scoreCDF {d : ℕ} (m : WeightedModel d) (x : Space d) :
    Measurable (m.scoreCDF x) := by
  apply Monotone.measurable
  intro a b hab
  apply measure_mono
  intro θ hθ
  exact hθ.trans hab

/-- The actual crossing kernel is integrated in both score height and threshold.
This is the Tonelli equality in (4.9), with no moment or finiteness assumption. -/
theorem crossingKernel_tonelli {d : ℕ} (m : WeightedModel d) (n : ℕ) (x u : Space d) :
    (∫⁻ y, m.scoreCDF x y ^ n * m.crossingKernel x u y) =
      2 * ∫⁻ r, ∫⁻ y,
        m.scoreCDF x y ^ n * (qminus m x u y r * qplus m x u y r) := by
  have hF := (measurable_scoreCDF m x).pow_const n
  have hm : Measurable (fun p : ℝ × ℝ => m.scoreCDF x p.1 ^ n *
      (qminus m x u p.1 p.2 * qplus m x u p.1 p.2)) :=
    (hF.comp measurable_fst).mul ((measurable_qminus m x u).mul (measurable_qplus m x u))
  calc
    _ = ∫⁻ y, 2 * ∫⁻ r, m.scoreCDF x y ^ n *
        (qminus m x u y r * qplus m x u y r) := by
      apply lintegral_congr
      intro y
      rw [crossingKernel_layerCake, mul_left_comm (m.scoreCDF x y ^ n) 2]
      congr 1
      exact (lintegral_const_mul _
        (((measurable_qminus m x u).comp measurable_prodMk_left).mul
          ((measurable_qplus m x u).comp measurable_prodMk_left))).symm
    _ = 2 * ∫⁻ y, ∫⁻ r, m.scoreCDF x y ^ n *
        (qminus m x u y r * qplus m x u y r) :=
      lintegral_const_mul _ hm.lintegral_prod_right'
    _ = _ := congrArg (fun z : ℝ≥0∞ => 2 * z)
      (lintegral_lintegral_swap hm.aemeasurable)

/-- The sharp threshold bound for the actual source slices, conditional solely
on the CDF-power normalization (4.6). -/
theorem threshold_bound_of_normalization {d : ℕ} (m : WeightedModel d)
    (n : ℕ) (x u : Space d)
    (hnorm : (∫⁻ y, m.scoreCDF x y ^ n *
      (∫⁻ w, sliceDensity m x w y ∂m.weights)) = (n + 1 : ℝ≥0∞)⁻¹) (r : ℝ) :
    (∫⁻ y, m.scoreCDF x y ^ n * (qminus m x u y r * qplus m x u y r)) ≤
      (m.average / (n + 1 : ℝ≥0∞)) *
        (tiltedProjection m u (Iic r) * tiltedProjection m u (Ioi r)) := by
  let τ := tiltedProjection m u
  letI := tiltedProjection_probability m u
  let p : ℝ := τ.real (Ioi r)
  let B : ℝ := m.average.toReal
  let T : ℝ := 1 / (n + 1 : ℝ)
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT : ENNReal.ofReal T = (n + 1 : ℝ≥0∞)⁻¹ := by
    change ENNReal.ofReal (1 / (n + 1 : ℝ)) = _
    rw [ENNReal.ofReal_div_of_pos (show 0 < (n + 1 : ℝ) by positivity)]
    simp only [ENNReal.ofReal_one, one_div]
    congr 1
    simpa only [Nat.cast_add, Nat.cast_one] using (ENNReal.ofReal_natCast (n + 1))
  have hBback : ENNReal.ofReal B = m.average := ENNReal.ofReal_toReal m.average_finite.ne
  have hpback : ENNReal.ofReal p = τ (Ioi r) := ENNReal.ofReal_toReal (measure_ne_top τ _)
  have hmp : 1 - p = τ.real (Iic r) := by
    rw [← compl_Ioi, measureReal_compl measurableSet_Ioi]
    simp only [measureReal_univ_eq_one, p]
  have hmpback : ENNReal.ofReal (1 - p) = τ (Iic r) := by
    rw [hmp]
    exact ENNReal.ofReal_toReal (measure_ne_top τ _)
  have hplus := (measurable_qplus m x u).of_uncurry_right (y := r)
  have hminus := (measurable_qminus m x u).of_uncurry_right (y := r)
  have hpbound (y) : qplus m x u y r ≤ ENNReal.ofReal (B * p) := by
    calc
      _ ≤ m.average * τ (Ioi r) := qplus_le_tilt m x u y r
      _ = ENNReal.ofReal B * ENNReal.ofReal p :=
        congrArg₂ (fun a b : ℝ≥0∞ => a * b) hBback.symm hpback.symm
      _ = _ := (ENNReal.ofReal_mul hB).symm
  have hmbound (y) : qminus m x u y r ≤ ENNReal.ofReal (B * (1 - p)) := by
    calc
      _ ≤ m.average * τ (Iic r) := qminus_le_tilt m x u y r
      _ = ENNReal.ofReal B * ENNReal.ofReal (1 - p) :=
        congrArg₂ (fun a b : ℝ≥0∞ => a * b) hBback.symm hmpback.symm
      _ = _ := (ENNReal.ofReal_mul hB).symm
  let ν : Measure ℝ := volume.withDensity (fun y => m.scoreCDF x y ^ n)
  have hF := (measurable_scoreCDF m x).pow_const n
  have hsum : (∫⁻ y, qplus m x u y r + qminus m x u y r ∂ν) = ENNReal.ofReal T := by
    dsimp only [ν]
    rw [lintegral_withDensity_eq_lintegral_mul _ hF (hplus.add hminus), hT]
    simp_rw [qplus_add_qminus]
    exact hnorm
  have hbound := lintegral_opposite_mass_bound ν _ _ hplus hminus hB hp0 hp1 hT0
    hpbound hmbound hsum
  have hleft : (∫⁻ y, qplus m x u y r * qminus m x u y r ∂ν) =
      ∫⁻ y, m.scoreCDF x y ^ n * (qminus m x u y r * qplus m x u y r) := by
    dsimp only [ν]
    rw [lintegral_withDensity_eq_lintegral_mul _ hF (hplus.mul hminus)]
    apply lintegral_congr
    intro y
    exact congrArg (fun z : ℝ≥0∞ => m.scoreCDF x y ^ n * z)
      (mul_comm (qplus m x u y r) (qminus m x u y r))
  have hright : ENNReal.ofReal (B * T * p * (1 - p)) =
      (m.average / (n + 1 : ℝ≥0∞)) * (τ (Iic r) * τ (Ioi r)) := by
    calc
      _ = (ENNReal.ofReal B * ENNReal.ofReal T) *
          (ENNReal.ofReal p * ENNReal.ofReal (1 - p)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hB hT0) hp0),
          ENNReal.ofReal_mul (mul_nonneg hB hT0), ENNReal.ofReal_mul hB]
        ac_rfl
      _ = (m.average * (n + 1 : ℝ≥0∞)⁻¹) * (τ (Ioi r) * τ (Iic r)) :=
        congrArg₂ (fun a b : ℝ≥0∞ => a * b)
          (congrArg₂ (fun a b : ℝ≥0∞ => a * b) hBback hT)
          (congrArg₂ (fun a b : ℝ≥0∞ => a * b) hpback hmpback)
      _ = _ := by simp only [div_eq_mul_inv]; ac_rfl
  calc
    _ = ∫⁻ y, qplus m x u y r * qminus m x u y r ∂ν := hleft.symm
    _ ≤ ENNReal.ofReal (B * T * p * (1 - p)) := hbound
    _ = _ := hright

/-- The complete sharp visibility estimate, with (4.6) exposed as its only
technical premise. This is an auxiliary theorem, not an assertion of the
unconditional source claim. All kernels and tilted measures are the actual
objects from `SourceModel`. -/
theorem visibility_of_normalization {d : ℕ} (m : WeightedModel d)
    (n : ℕ) (x u : Space d)
    (hnorm : (∫⁻ y, m.scoreCDF x y ^ n *
      (∫⁻ w, sliceDensity m x w y ∂m.weights)) = (n + 1 : ℝ≥0∞)⁻¹) :
    (∫⁻ y, m.scoreCDF x y ^ n * m.crossingKernel x u y) ≤
      m.average / (n + 1 : ℝ≥0∞) * m.directionalGini u := by
  rw [crossingKernel_tonelli, directionalGini_layerCake]
  calc
    2 * (∫⁻ r, ∫⁻ y, m.scoreCDF x y ^ n *
        (qminus m x u y r * qplus m x u y r)) ≤
        2 * ∫⁻ r, (m.average / (n + 1 : ℝ≥0∞)) *
          (tiltedProjection m u (Iic r) * tiltedProjection m u (Ioi r)) := by
      exact mul_le_mul_left' (lintegral_mono (threshold_bound_of_normalization m n x u hnorm)) 2
    _ = (m.average / (n + 1 : ℝ≥0∞)) *
        (2 * ∫⁻ r, tiltedProjection m u (Iic r) * tiltedProjection m u (Ioi r)) := by
      rw [lintegral_const_mul']
      · ac_rfl
      · exact ENNReal.div_ne_top m.average_finite.ne (by simp)

/-- Lemma 4.1: sharp weighted distribution-free visibility for the source's
actual conditional score density, crossing kernel, envelope tilt, and Gini
functional. Extended values are allowed, and no first-moment hypothesis is
added. -/
theorem weighted_visibility {d : ℕ} (m : WeightedModel d) (n : ℕ) (x u : Space d) :
    (∫⁻ y, m.scoreCDF x y ^ n * m.crossingKernel x u y) ≤
      m.average / (n + 1 : ℝ≥0∞) * m.directionalGini u := by
  apply visibility_of_normalization
  simpa only [VisibleCrossing.scoreDensity, sliceDensity] using
    VisibleCrossing.scoreCDF_power_density m x n

/-- The exact source-model claim, with all its original quantifiers. -/
theorem visibilityLemmaClaim (d : ℕ) : VisibilityLemmaClaim (d := d) := by
  intro m n x u
  simpa only [Nat.cast_add, Nat.cast_one] using weighted_visibility m n x u

end Paper35.VisibilityKernel

import Paper35.GaussianSegments
import Paper35.RandomCount
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace Paper35.GaussianMarked

/-- The actual local upper-envelope switching condition on the entire parameter line. -/
def GlobalSwitch {K : ℕ} (f : Fin K → ℝ → ℝ) (s : ℝ) : Prop :=
  ∃ i j, i ≠ j ∧ f i s = f j s ∧
    (∀ k, k ≠ i → k ≠ j → f k s < f i s) ∧ SignChanges (fun t => f i t-f j t) s

def globalSwitchSet {K : ℕ} (f : Fin K → ℝ → ℝ) : Set ℝ := {s | GlobalSwitch f s}
def wholeSwitchCount {K : ℕ} (f : Fin K → ℝ → ℝ) : ℝ≥0∞ :=
  (globalSwitchSet f).encard

def switchWindow {K : ℕ} (f : Fin K → ℝ → ℝ) (R : ℝ) : Set ℝ :=
  globalSwitchSet f ∩ Ioo (-R) R

def windowRadius (n : ℕ) : ℝ := (n:ℝ)+1

theorem signChanges_comp_shift (f : ℝ → ℝ) (a s : ℝ) :
    SignChanges (fun t => f (a+t)) s ↔ SignChanges f (a+s) := by
  constructor
  · rintro ⟨δ,hδ,hsign⟩
    refine ⟨δ,hδ,?_⟩
    rcases hsign with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · left
      constructor
      · intro t ht
        have h := hl (t-a) ⟨by linarith [ht.1],by linarith [ht.2]⟩
        simpa only [add_sub_cancel] using h
      · intro t ht
        have h := hr (t-a) ⟨by linarith [ht.1],by linarith [ht.2]⟩
        simpa only [add_sub_cancel] using h
    · right
      constructor
      · intro t ht
        have h := hl (t-a) ⟨by linarith [ht.1],by linarith [ht.2]⟩
        simpa only [add_sub_cancel] using h
      · intro t ht
        have h := hr (t-a) ⟨by linarith [ht.1],by linarith [ht.2]⟩
        simpa only [add_sub_cancel] using h
  · rintro ⟨δ,hδ,hsign⟩
    refine ⟨δ,hδ,?_⟩
    rcases hsign with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact Or.inl ⟨fun t ht => hl (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩,
        fun t ht => hr (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩⟩
    · exact Or.inr ⟨fun t ht => hl (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩,
        fun t ht => hr (a+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩⟩

theorem signChanges_comp_affine (f : ℝ → ℝ) (a c s : ℝ) (hc : 0 < c) :
    SignChanges (fun t => f (a+c*t)) s ↔ SignChanges f (a+c*s) := by
  exact (RandomCount.signChanges_comp_pos_mul (f := fun x => f (a+x)) (c := c) (s := s) hc).trans
    (signChanges_comp_shift f a (c*s))

theorem globalSwitch_comp_affine {K : ℕ} (f : Fin K → ℝ → ℝ)
    (a c s : ℝ) (hc : 0 < c) :
    GlobalSwitch (fun j t => f j (a+c*t)) s ↔ GlobalSwitch f (a+c*s) := by
  constructor
  · rintro ⟨i,j,hij,heq,hvis,hsgn⟩
    exact ⟨i,j,hij,heq,hvis,(signChanges_comp_affine (fun t => f i t-f j t) a c s hc).mp hsgn⟩
  · rintro ⟨i,j,hij,heq,hvis,hsgn⟩
    exact ⟨i,j,hij,heq,hvis,(signChanges_comp_affine (fun t => f i t-f j t) a c s hc).mpr hsgn⟩

theorem switchWindow_eq_image {K : ℕ} (f : Fin K → ℝ → ℝ) (R : ℝ) (hR : 0 < R) :
    switchWindow f R = (fun s => -R+2*R*s) ''
      switchSet (fun j s => f j (-R+2*R*s)) 1 := by
  ext t
  constructor
  · rintro ⟨ht,hl,hr⟩
    let s := (t+R)/(2*R)
    have hs0 : 0 < s := div_pos (by linarith) (by positivity)
    have hs1 : s < 1 := (div_lt_one (by positivity : 0<2*R)).mpr (by linarith)
    have heq : -R+2*R*s = t := by dsimp [s]; field_simp; ring
    refine ⟨s,⟨hs0,hs1,?_⟩,heq⟩
    apply (globalSwitch_comp_affine f (-R) (2*R) s (by positivity)).mpr
    simpa only [heq] using ht
  · rintro ⟨s,hs,rfl⟩
    exact ⟨(globalSwitch_comp_affine f (-R) (2*R) s (by positivity)).mp hs.2.2,
      by nlinarith [hs.1],by nlinarith [hs.2.1]⟩

theorem switchWindow_count {K : ℕ} (f : Fin K → ℝ → ℝ) (R : ℝ) (hR : 0 < R) :
    ((switchWindow f R).encard : ℝ≥0∞) =
      switchCount (fun j s => f j (-R+2*R*s)) 1 := by
  unfold switchCount
  rw [switchWindow_eq_image f R hR]
  congr 1
  exact ((add_right_injective (-R)).comp
    (mul_right_injective₀ (by positivity : (2*R:ℝ)≠0))).encard_image _

theorem switchWindow_monotone {K : ℕ} (f : Fin K → ℝ → ℝ) :
    Monotone (fun n : ℕ => switchWindow f (windowRadius n)) := by
  intro n k hnk t ht
  have hR : windowRadius n ≤ windowRadius k := by
    exact add_le_add_right (Nat.cast_le.mpr hnk) 1
  exact ⟨ht.1,⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩⟩

theorem globalSwitchSet_eq_iUnion {K : ℕ} (f : Fin K → ℝ → ℝ) :
    globalSwitchSet f = ⋃ n : ℕ, switchWindow f (windowRadius n) := by
  ext t
  constructor
  · intro ht
    obtain ⟨n,hn⟩ := exists_nat_gt |t|
    refine mem_iUnion.mpr ⟨n,ht,?_⟩
    have habs : |t| < windowRadius n := by dsimp [windowRadius]; linarith
    exact abs_lt.mp habs
  · intro ht
    obtain ⟨n,hn⟩ := mem_iUnion.mp ht
    exact hn.1

theorem switchWindow_countable {K : ℕ} (f : Fin K → ℝ → ℝ) (R : ℝ) (hR : 0 < R) :
    (switchWindow f R).Countable := by
  rw [switchWindow_eq_image f R hR]
  exact (switchSet_countable _ _).image _

theorem wholeSwitchCount_eq_iSup {K : ℕ} (f : Fin K → ℝ → ℝ) :
    wholeSwitchCount f = ⨆ n : ℕ, ((switchWindow f (windowRadius n)).encard : ℝ≥0∞) := by
  have hm (n : ℕ) : MeasurableSet (switchWindow f (windowRadius n)) :=
    (switchWindow_countable f _ (by dsimp [windowRadius]; positivity)).measurableSet
  unfold wholeSwitchCount
  rw [globalSwitchSet_eq_iUnion]
  rw [← Measure.count_apply (MeasurableSet.iUnion hm),
    (switchWindow_monotone f).measure_iUnion]
  congr 1
  funext n
  exact Measure.count_apply (hm n)

def lineCurve {m : ℕ} (a b : Source.Space m) (t : ℝ) : Source.Space m := a+t•b

theorem lineCurve_window {m : ℕ} (a b : Source.Space m) (R t : ℝ) :
    lineCurve a b (-R+2*R*t) = segment (a-R•b) (a+R•b) t := by
  dsimp [lineCurve,segment]
  module

theorem line_segment_nonzero {m : ℕ} (a b : Source.Space m)
    (hnz : ∀ t : ℝ, lineCurve a b t ≠ 0) (R : ℝ) :
    ∀ t ∈ Icc (0:ℝ) 1, segment (a-R•b) (a+R•b) t ≠ 0 := by
  intro t _
  rw [← lineCurve_window]
  exact hnz _

theorem aemeasurable_gaussian_window_count
    (hregular : ClassicalCroftonRegularityLaw) (hrot : GaussianPairReconstructionLaw)
    (m n : ℕ) (hm : 1 ≤ m) (a b : Source.Space m) (mean : ℝ → ℝ)
    (hnz : ∀ t : ℝ, lineCurve a b t ≠ 0) (R : ℝ) (hR : 0 < R)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter 1)) :
    AEMeasurable (fun Z => ((switchWindow
      (fun j t => mean t+inner ℝ (Z j) (lineCurve a b t)) R).encard : ℝ≥0∞))
      (gaussianIid m (n+2)) := by
  simp_rw [switchWindow_count _ R hR,lineCurve_window]
  exact aemeasurable_gaussian_segment_count hregular hrot m n hm (a-R•b) (a+R•b)
    (fun s => mean (-R+2*R*s)) (line_segment_nonzero a b hnz R) hLN

theorem gaussian_window_expectedCount
    (hcrofton : ClassicalCroftonLaw) (hregular : ClassicalCroftonRegularityLaw)
    (hproj : GaussianUnitProjectionLaw) (hrot : GaussianPairReconstructionLaw)
    (hmax : GaussianMaxIntegralLaw) (hlength : ACCurveLengthLaw)
    (m n : ℕ) (hm : 1 ≤ m) (a b : Source.Space m) (mean : ℝ → ℝ)
    (hnz : ∀ t : ℝ, lineCurve a b t ≠ 0) (R : ℝ) (hR : 0 < R)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter 1)) :
    (∫⁻ Z, ((switchWindow
      (fun j t => mean t+inner ℝ (Z j) (lineCurve a b t)) R).encard : ℝ≥0∞)
        ∂gaussianIid m (n+2)) =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2) *
        Real.arccos (inner ℝ (a-R•b) (a+R•b)/(‖a-R•b‖*‖a+R•b‖))) := by
  simp_rw [switchWindow_count _ R hR,lineCurve_window]
  exact gaussian_segment_expectedSwitchCount hcrofton hregular hproj hrot hmax hlength
    m n hm (a-R•b) (a+R•b) (fun s => mean (-R+2*R*s))
    (line_segment_nonzero a b hnz R) hLN

theorem continuousAt_normalize {m : ℕ} (x : Source.Space m) (hx : x ≠ 0) :
    ContinuousAt Gaussian.normalize x := by
  unfold Gaussian.normalize
  exact (continuousAt_id.norm.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

theorem normalize_window_left {m : ℕ} (a b : Source.Space m) (R : ℝ) (hR : 0 < R) :
    Gaussian.normalize (a-R•b) = Gaussian.normalize (R⁻¹•a-b) := by
  have h : a-R•b = R•(R⁻¹•a-b) := by
    rw [smul_sub,smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
  rw [h,normalize_smul_pos _ R hR]

theorem normalize_window_right {m : ℕ} (a b : Source.Space m) (R : ℝ) (hR : 0 < R) :
    Gaussian.normalize (a+R•b) = Gaussian.normalize (R⁻¹•a+b) := by
  have h : a+R•b = R•(R⁻¹•a+b) := by
    rw [smul_add,smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
  rw [h,normalize_smul_pos _ R hR]

/-- Normalized endpoint directions of increasing windows tend to antipodes;
therefore the actual endpoint-kernel arccos tends to π. -/
theorem window_angle_tendsto_pi {m : ℕ} (a b : Source.Space m) (hb : b ≠ 0) :
    Tendsto (fun k : ℕ => Real.arccos
      (inner ℝ (a-windowRadius k•b) (a+windowRadius k•b)/
        (‖a-windowRadius k•b‖*‖a+windowRadius k•b‖))) atTop (𝓝 Real.pi) := by
  have hi : Tendsto (fun k : ℕ => (windowRadius k)⁻¹) atTop (𝓝 (0:ℝ)) := by
    simpa only [windowRadius,one_div] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hs : Tendsto (fun k : ℕ => (windowRadius k)⁻¹•a) atTop (𝓝 (0:Source.Space m)) := by
    simpa only [zero_smul] using hi.smul_const a
  have hl : Tendsto (fun k : ℕ => Gaussian.normalize (a-windowRadius k•b))
      atTop (𝓝 (Gaussian.normalize (-b))) := by
    have hsleft : Tendsto (fun k : ℕ => (windowRadius k)⁻¹•a-b) atTop (𝓝 (-b)) := by
      simpa only [zero_sub] using hs.sub_const b
    have h := (continuousAt_normalize (-b) (neg_ne_zero.mpr hb)).tendsto.comp hsleft
    apply h.congr'
    filter_upwards [] with k
    exact (normalize_window_left a b (windowRadius k) (by dsimp [windowRadius]; positivity)).symm
  have hr : Tendsto (fun k : ℕ => Gaussian.normalize (a+windowRadius k•b))
      atTop (𝓝 (Gaussian.normalize b)) := by
    have hsright : Tendsto (fun k : ℕ => (windowRadius k)⁻¹•a+b) atTop (𝓝 b) := by
      simpa only [zero_add] using hs.add_const b
    have h := (continuousAt_normalize b hb).tendsto.comp hsright
    apply h.congr'
    filter_upwards [] with k
    exact (normalize_window_right a b (windowRadius k) (by dsimp [windowRadius]; positivity)).symm
  have hk := Filter.Tendsto.inner (𝕜 := ℝ) hl hr
  have hinner : inner ℝ (Gaussian.normalize (-b)) (Gaussian.normalize b) = -1 := by
    have hneg : Gaussian.normalize (-b) = -Gaussian.normalize b := by
      simp only [Gaussian.normalize,norm_neg,smul_neg]
    rw [hneg,inner_neg_left,real_inner_self_eq_norm_sq,Gaussian.normalize_norm b hb]
    norm_num
  rw [hinner] at hk
  have hangle := Real.continuous_arccos.tendsto (-1) |>.comp hk
  simpa only [Gaussian.inner_normalize,Real.arccos_neg_one] using hangle

theorem aemeasurable_gaussian_whole_count
    (hregular : ClassicalCroftonRegularityLaw) (hrot : GaussianPairReconstructionLaw)
    (m n : ℕ) (hm : 1 ≤ m) (a b : Source.Space m) (mean : ℝ → ℝ)
    (hnz : ∀ t : ℝ, lineCurve a b t ≠ 0)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter 1)) :
    AEMeasurable (fun Z => wholeSwitchCount
      (fun j t => mean t+inner ℝ (Z j) (lineCurve a b t))) (gaussianIid m (n+2)) := by
  simp only [wholeSwitchCount_eq_iSup]
  exact AEMeasurable.iSup (fun k => aemeasurable_gaussian_window_count hregular hrot m n hm a b
    mean hnz (windowRadius k) (by dsimp [windowRadius]; positivity) hLN)

/-- Formula (7.8), before simplifying πc_K, for actual switches over the entire
line. The proof exhausts the line by actual finite windows and uses monotone
convergence; no whole-line or upper-envelope identity is supplied as an input. -/
theorem gaussian_whole_line_expectedCount
    (hcrofton : ClassicalCroftonLaw) (hregular : ClassicalCroftonRegularityLaw)
    (hproj : GaussianUnitProjectionLaw) (hrot : GaussianPairReconstructionLaw)
    (hmax : GaussianMaxIntegralLaw) (hlength : ACCurveLengthLaw)
    (m n : ℕ) (hm : 1 ≤ m) (a b : Source.Space m) (hb : b ≠ 0) (mean : ℝ → ℝ)
    (hnz : ∀ t : ℝ, lineCurve a b t ≠ 0)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter 1)) :
    (∫⁻ Z, wholeSwitchCount (fun j t => mean t+inner ℝ (Z j) (lineCurve a b t))
      ∂gaussianIid m (n+2)) = ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2)*Real.pi) := by
  let f (Z : Fin (n+2) → Source.Space m) : Fin (n+2) → ℝ → ℝ :=
    fun j t => mean t+inner ℝ (Z j) (lineCurve a b t)
  let C (k : ℕ) (Z : Fin (n+2) → Source.Space m) : ℝ≥0∞ :=
    (switchWindow (f Z) (windowRadius k)).encard
  have hCm (k : ℕ) : AEMeasurable (C k) (gaussianIid m (n+2)) :=
    aemeasurable_gaussian_window_count hregular hrot m n hm a b mean hnz (windowRadius k)
      (by dsimp [windowRadius]; positivity) hLN
  have hCmono (Z : Fin (n+2) → Source.Space m) : Monotone (fun k => C k Z) := by
    intro j k hjk
    exact ENat.toENNReal_mono (Set.encard_mono (switchWindow_monotone (f Z) hjk))
  have hval (k : ℕ) : (∫⁻ Z, C k Z ∂gaussianIid m (n+2)) =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2)*Real.arccos
        (inner ℝ (a-windowRadius k•b) (a+windowRadius k•b)/
          (‖a-windowRadius k•b‖*‖a+windowRadius k•b‖))) :=
    gaussian_window_expectedCount hcrofton hregular hproj hrot hmax hlength m n hm a b mean
      hnz (windowRadius k) (by dsimp [windowRadius]; positivity) hLN
  have hlim : Tendsto (fun k => ∫⁻ Z, C k Z ∂gaussianIid m (n+2)) atTop
      (𝓝 (ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2)*Real.pi))) := by
    simp only [hval]
    exact ENNReal.tendsto_ofReal (tendsto_const_nhds.mul (window_angle_tendsto_pi a b hb))
  have hmono : Monotone (fun k => ∫⁻ Z, C k Z ∂gaussianIid m (n+2)) := by
    intro j k hjk
    exact lintegral_mono (fun Z => hCmono Z hjk)
  calc
    _ = ∫⁻ Z, ⨆ k, C k Z ∂gaussianIid m (n+2) := by
      simp only [wholeSwitchCount_eq_iSup,C,f]
    _ = ⨆ k, ∫⁻ Z, C k Z ∂gaussianIid m (n+2) :=
      lintegral_iSup' hCm (Filter.Eventually.of_forall hCmono)
    _ = _ := tendsto_nhds_unique (tendsto_atTop_iSup hmono) hlim

/-- The source form √π m_K follows by the definition of c_K. -/
theorem gaussian_whole_line_formula_7_8
    (hcrofton : ClassicalCroftonLaw) (hregular : ClassicalCroftonRegularityLaw)
    (hproj : GaussianUnitProjectionLaw) (hrot : GaussianPairReconstructionLaw)
    (hmax : GaussianMaxIntegralLaw) (hlength : ACCurveLengthLaw)
    (m n : ℕ) (hm : 1 ≤ m) (a b : Source.Space m) (hb : b ≠ 0) (mean : ℝ → ℝ)
    (hnz : ∀ t : ℝ, lineCurve a b t ≠ 0)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter 1)) :
    (∫⁻ Z, wholeSwitchCount (fun j t => mean t+inner ℝ (Z j) (lineCurve a b t))
      ∂gaussianIid m (n+2)) =
        ENNReal.ofReal (Real.sqrt Real.pi*Paper35.gaussianMaxMean (n+2)) := by
  rw [gaussian_whole_line_expectedCount hcrofton hregular hproj hrot hmax hlength
    m n hm a b hb mean hnz hLN]
  congr 1
  unfold Paper35.gaussianRankCoefficient
  have hsq := Real.sq_sqrt Real.pi_pos.le
  have hne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  nlinarith [congrArg (fun x : ℝ => Paper35.gaussianMaxMean (n+2)*x) hsq]
end Paper35.GaussianMarked

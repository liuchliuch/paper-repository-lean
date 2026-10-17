import Paper35.GaussianOneDimensional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Module
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Paper35.GaussianMarked

def circle {m : ℕ} (u v : Source.Space m) (θ : ℝ) : Source.Space m :=
  Real.cos θ • u + Real.sin θ • v

def circleVelocity {m : ℕ} (u v : Source.Space m) (θ : ℝ) : Source.Space m :=
  (-Real.sin θ) • u + Real.cos θ • v

theorem circle_hasDerivAt {m : ℕ} (u v : Source.Space m) (θ : ℝ) :
    HasDerivAt (circle u v) (circleVelocity u v θ) θ := by
  exact ((Real.hasDerivAt_cos θ).smul_const u).add ((Real.hasDerivAt_sin θ).smul_const v)

theorem circleVelocity_norm {m : ℕ} (u v : Source.Space m)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (horth : inner ℝ u v = 0) (θ : ℝ) :
    ‖circleVelocity u v θ‖ = 1 := by
  have hsq : ‖circleVelocity u v θ‖ ^ 2 = 1 := by
    simp only [circleVelocity, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      sq_abs, hu, hv, mul_one, real_inner_smul_left, inner_smul_right, horth,
      mul_zero, add_zero, neg_sq]
    exact Real.sin_sq_add_cos_sq θ
  nlinarith [norm_nonneg (circleVelocity u v θ)]

/-- Circle arclength follows from the classical AC curve-length theorem and the
explicit unit-speed derivative, with no affine-segment geometry in the input. -/
theorem circle_variation {m : ℕ} (hlength : ACCurveLengthLaw)
    (u v : Source.Space m) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (horth : inner ℝ u v = 0) (a b : ℝ) (hab : a ≤ b) :
    eVariationOn (circle u v) (Icc a b) = ENNReal.ofReal (b-a) := by
  by_cases heq : a = b
  · subst b
    simp
  have hpos : 0 < b-a := sub_pos.mpr (lt_of_le_of_ne hab heq)
  let c : ℝ → Source.Space m := fun s => circle u v (s+a)
  have hd (s : ℝ) : HasDerivAt c (circleVelocity u v (s+a)) s := by
    simpa only [Function.comp_def, one_smul, c] using
      (circle_hasDerivAt u v (s+a)).scomp s ((hasDerivAt_id s).add_const a)
  have hlip : LipschitzOnWith 1 c (Icc 0 (b-a)) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc 0 (b-a)) (fun s _ => (hd s).hasDerivWithinAt)
    intro s _
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, circleVelocity_norm u v hu hv horth]
  have hac : AbsolutelyContinuousOnInterval c 0 (b-a) := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := 1)
    simpa only [uIcc_of_le hpos.le] using hlip
  have hvary := hlength m (b-a) hpos c hac
  have hspeed (s : ℝ) : ‖deriv c s‖ = 1 := by
    rw [(hd s).deriv, circleVelocity_norm u v hu hv horth]
  have hcvar : eVariationOn c (Icc 0 (b-a)) = ENNReal.ofReal (b-a) := by
    rw [hvary, sphericalLength]
    simp only [hspeed, ENNReal.ofReal_one, lintegral_one]
    simp [Real.volume_Icc]
  have hmono : MonotoneOn (fun s : ℝ => s+a) (Icc 0 (b-a)) := by
    intro x _ y _ hxy
    exact add_le_add_right hxy a
  have himage : (fun s : ℝ => s+a) '' Icc 0 (b-a) = Icc a b := by
    rw [ContinuousOn.image_Icc_of_monotoneOn hpos.le (by fun_prop) hmono]
    simp
  have hvar := eVariationOn.comp_eq_of_monotoneOn (circle u v) (fun s : ℝ => s+a) hmono
  rw [himage] at hvar
  exact hvar.symm.trans hcvar

/-- The normalized graph of an orthogonal pair is the circle at its arctangent
coordinate. This is an explicit identity, independent of probabilistic inputs. -/
theorem normalize_orthogonal_graph {m : ℕ} (u v : Source.Space m)
    (hu : u ≠ 0) (hv : v ≠ 0) (horth : inner ℝ u v = 0) (t : ℝ) :
    Gaussian.normalize (u+t•v) =
      circle (Gaussian.normalize u) (Gaussian.normalize v)
        (Real.arctan (t*‖v‖/‖u‖)) := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hn : ‖u+t•v‖ = ‖u‖ * Real.sqrt (1+(t*‖v‖/‖u‖)^2) := by
    have hsq : ‖u+t•v‖^2 = ‖u‖^2+t^2*‖v‖^2 := by
      simp only [norm_add_sq_real, inner_smul_right, horth, mul_zero, add_zero,
        norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hsqrt := Real.sq_sqrt (show 0 ≤ 1+(t*‖v‖/‖u‖)^2 by positivity)
    have hright : 0 ≤ ‖u‖ * Real.sqrt (1+(t*‖v‖/‖u‖)^2) := by positivity
    have hrightsq : (‖u‖ * Real.sqrt (1+(t*‖v‖/‖u‖)^2))^2 = ‖u+t•v‖^2 := by
      rw [mul_pow, hsqrt, hsq]
      field_simp
    nlinarith [norm_nonneg (u+t•v)]
  have hsqrtne : Real.sqrt (1+(t*‖v‖/‖u‖)^2) ≠ 0 := by positivity
  rw [circle, Real.cos_arctan, Real.sin_arctan]
  simp only [Gaussian.normalize, smul_add, smul_smul, hn]
  congr 1 <;> field_simp

theorem normalize_smul_pos {m : ℕ} (x : Source.Space m) (r : ℝ) (hr : 0 < r) :
    Gaussian.normalize (r•x) = Gaussian.normalize x := by
  simp only [Gaussian.normalize, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv_rev,
    smul_smul]
  congr 1
  field_simp

theorem double_arctan_eq_arccos (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    2*Real.arctan (b/a) = Real.arccos ((a^2-b^2)/(a^2+b^2)) := by
  have hs : Real.sqrt (1+(b/a)^2) ^ 2 = 1+(b/a)^2 := Real.sq_sqrt (by positivity)
  have hc : Real.cos (2*Real.arctan (b/a)) = (a^2-b^2)/(a^2+b^2) := by
    rw [Real.cos_two_mul, Real.cos_arctan, div_pow, one_pow, hs]
    field_simp
    ring
  symm
  rw [← hc, Real.arccos_cos]
  · positivity
  · have h := Real.arctan_lt_pi_div_two (b/a)
    linarith

theorem normalized_orthogonal_graph_variation {m : ℕ} (hlength : ACCurveLengthLaw)
    (u v : Source.Space m) (hu : u ≠ 0) (hv : v ≠ 0)
    (horth : inner ℝ u v = 0) (a b : ℝ) (hab : a ≤ b) :
    eVariationOn (fun t => Gaussian.normalize (u+t•v)) (Icc a b) =
      ENNReal.ofReal (Real.arctan (b*‖v‖/‖u‖)-Real.arctan (a*‖v‖/‖u‖)) := by
  let θ : ℝ → ℝ := fun t => Real.arctan (t*‖v‖/‖u‖)
  have hmono : MonotoneOn θ (Icc a b) := by
    intro x _ y _ hxy
    apply Real.arctan_mono
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hxy (norm_nonneg _))
      (norm_nonneg _)
  have himage : θ '' Icc a b = Icc (θ a) (θ b) :=
    ContinuousOn.image_Icc_of_monotoneOn hab
      (Real.continuous_arctan.comp (by fun_prop)).continuousOn hmono
  have hident : (fun t => Gaussian.normalize (u+t•v)) =
      circle (Gaussian.normalize u) (Gaussian.normalize v) ∘ θ := by
    funext t
    exact normalize_orthogonal_graph u v hu hv horth t
  rw [hident, eVariationOn.comp_eq_of_monotoneOn _ _ hmono, himage]
  apply circle_variation hlength
  · exact Gaussian.normalize_norm u hu
  · exact Gaussian.normalize_norm v hv
  · rw [Gaussian.inner_normalize, horth, zero_div]
  · exact hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

def segment {m : ℕ} (a b : Source.Space m) (t : ℝ) : Source.Space m :=
  (1-t)•a+t•b

theorem normalized_unit_segment_variation {m : ℕ} (hlength : ACCurveLengthLaw)
    (a b : Source.Space m) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hne : a ≠ -b) :
    eVariationOn (fun t => Gaussian.normalize (segment a b t)) (Icc 0 1) =
      ENNReal.ofReal (Real.arccos (inner ℝ a b)) := by
  by_cases heq : a = b
  · subst b
    have hid : (fun t => Gaussian.normalize (segment a a t)) = fun _ => a := by
      funext t
      have hs : segment a a t = a := by dsimp [segment]; module
      simp only [hs, Gaussian.normalize, ha, inv_one, one_smul]
    rw [hid, eVariationOn.constant_on (by simp)]
    rw [real_inner_self_eq_norm_sq, ha, one_pow, Real.arccos_one, ENNReal.ofReal_zero]
  let u : Source.Space m := (1/2:ℝ)•(a+b)
  let v : Source.Space m := (1/2:ℝ)•(b-a)
  have hune : u ≠ 0 := by
    intro h
    apply hne
    have hh : a+b = 0 := (smul_eq_zero.mp h).resolve_left (by norm_num)
    exact eq_neg_iff_add_eq_zero.mpr hh
  have hvne : v ≠ 0 := by
    intro h
    apply heq
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left (by norm_num))).symm
  have horth : inner ℝ u v = 0 := by
    simp only [u,v,real_inner_smul_left,inner_smul_right,inner_add_left,inner_sub_right,
      real_inner_self_eq_norm_sq,ha,hb,real_inner_comm b a]
    ring
  have hsum : u+v = b := by dsimp [u,v]; module
  have hsub : u-v = a := by dsimp [u,v]; module
  have hsq : ‖u‖^2+‖v‖^2 = 1 := by
    have hh := norm_add_sq_real u v
    rw [hsum,hb,horth] at hh
    nlinarith
  have habinner : inner ℝ a b = ‖u‖^2-‖v‖^2 := by
    rw [← hsub,← hsum]
    simp only [inner_sub_left,inner_add_right,real_inner_self_eq_norm_sq,
      real_inner_comm v u]
    ring
  have hseg : (fun t => Gaussian.normalize (segment a b t)) =
      (fun r => Gaussian.normalize (u+r•v)) ∘ (fun t : ℝ => 2*t-1) := by
    funext t
    congr 1
    dsimp [segment,u,v]
    module
  have hmono : MonotoneOn (fun t : ℝ => 2*t-1) (Icc 0 1) := by
    intro x _ y _ hxy
    linarith
  have himage : (fun t : ℝ => 2*t-1) '' Icc 0 1 = Icc (-1) 1 := by
    rw [ContinuousOn.image_Icc_of_monotoneOn (by norm_num : (0:ℝ)≤1) (by fun_prop) hmono]
    norm_num
  rw [hseg,eVariationOn.comp_eq_of_monotoneOn _ _ hmono,himage,
    normalized_orthogonal_graph_variation hlength u v hune hvne horth (-1) 1 (by norm_num)]
  congr 1
  simp only [one_mul,neg_mul,one_mul,neg_div,Real.arctan_neg,sub_neg_eq_add]
  rw [show Real.arctan (‖v‖/‖u‖)+Real.arctan (‖v‖/‖u‖) =
    2*Real.arctan (‖v‖/‖u‖) by ring,
    double_arctan_eq_arccos ‖u‖ ‖v‖ (norm_pos_iff.mpr hune) (norm_nonneg _),hsq,div_one,
    habinner]

def radialWeight (A B t : ℝ) : ℝ := t*B/((1-t)*A+t*B)

theorem radialWeight_den_pos (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (t : ℝ) (ht : t ∈ Icc 0 1) : 0 < (1-t)*A+t*B := by
  by_cases ht0 : t = 0
  · subst t
    simpa using hA
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hA.le) (mul_pos htpos hB)

theorem radialWeight_monotone (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    MonotoneOn (radialWeight A B) (Icc 0 1) := by
  intro x hx y hy hxy
  apply (div_le_div_iff₀ (radialWeight_den_pos A B hA hB x hx)
    (radialWeight_den_pos A B hA hB y hy)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (mul_pos hA hB).le]

theorem radialWeight_image (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    radialWeight A B '' Icc 0 1 = Icc 0 1 := by
  have hc : ContinuousOn (radialWeight A B) (Icc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact (radialWeight_den_pos A B hA hB t ht).ne'
  rw [hc.image_Icc_of_monotoneOn (by norm_num : (0:ℝ)≤1) (radialWeight_monotone A B hA hB)]
  simp [radialWeight,ne_of_gt hB]

theorem normalize_segment_radialWeight {m : ℕ} (a b : Source.Space m)
    (ha : a ≠ 0) (hb : b ≠ 0) (t : ℝ) (ht : t ∈ Icc 0 1) :
    Gaussian.normalize (segment a b t) =
      Gaussian.normalize (segment (Gaussian.normalize a) (Gaussian.normalize b)
        (radialWeight ‖a‖ ‖b‖ t)) := by
  let d : ℝ := (1-t)*‖a‖+t*‖b‖
  have hd : 0 < d := radialWeight_den_pos ‖a‖ ‖b‖ (norm_pos_iff.mpr ha)
    (norm_pos_iff.mpr hb) t ht
  have heq : segment a b t = d • segment (Gaussian.normalize a) (Gaussian.normalize b)
      (radialWeight ‖a‖ ‖b‖ t) := by
    have hca : d*((1-radialWeight ‖a‖ ‖b‖ t)*‖a‖⁻¹) = 1-t := by
      change d*((1-t*‖b‖/d)*‖a‖⁻¹) = 1-t
      field_simp [hd.ne',norm_ne_zero_iff.mpr ha]
      dsimp [d]
      ring
    have hcb : d*(radialWeight ‖a‖ ‖b‖ t*‖b‖⁻¹) = t := by
      change d*(t*‖b‖/d*‖b‖⁻¹) = t
      field_simp
    simp only [segment,Gaussian.normalize,smul_add,smul_smul]
    rw [hca,hcb]
  rw [heq,normalize_smul_pos _ d hd]

/-- The actual radial projection of a nonzero affine segment has its endpoint
angle as metric total variation. The midpoint-plane/arctangent argument is proved
above; the only external geometric input is the ordinary AC length theorem. -/
theorem normalized_segment_variation {m : ℕ} (hlength : ACCurveLengthLaw)
    (a b : Source.Space m) (hnz : ∀ t ∈ Icc (0:ℝ) 1, segment a b t ≠ 0) :
    eVariationOn (fun t => Gaussian.normalize (segment a b t)) (Icc 0 1) =
      ENNReal.ofReal (Real.arccos (inner ℝ a b/(‖a‖*‖b‖))) := by
  have ha : a ≠ 0 := by simpa [segment] using hnz 0 (by norm_num)
  have hb : b ≠ 0 := by simpa [segment] using hnz 1 (by norm_num)
  have hA : ‖Gaussian.normalize a‖ = 1 := Gaussian.normalize_norm a ha
  have hB : ‖Gaussian.normalize b‖ = 1 := Gaussian.normalize_norm b hb
  have hne : Gaussian.normalize a ≠ -(Gaussian.normalize b) := by
    intro hneg
    have hangle := Gaussian.angle_lt_pi_of_segment_nonzero a b hnz
    have hpi : InnerProductGeometry.angle (Gaussian.normalize a) (Gaussian.normalize b) = Real.pi := by
      rw [hneg,InnerProductGeometry.angle_neg_self_of_nonzero]
      exact norm_ne_zero_iff.mp (by rw [hB]; norm_num)
    have heq : InnerProductGeometry.angle (Gaussian.normalize a) (Gaussian.normalize b) =
        InnerProductGeometry.angle a b := by
      simp only [Gaussian.normalize]
      rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr ha)),
        InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hb))]
    rw [← heq,hpi] at hangle
    exact lt_irrefl _ hangle
  have heqon : EqOn (fun t => Gaussian.normalize (segment a b t))
      ((fun r => Gaussian.normalize (segment (Gaussian.normalize a) (Gaussian.normalize b) r)) ∘
        radialWeight ‖a‖ ‖b‖) (Icc 0 1) := by
    intro t ht
    exact normalize_segment_radialWeight a b ha hb t ht
  rw [eVariationOn.eq_of_eqOn heqon,
    eVariationOn.comp_eq_of_monotoneOn _ _
      (radialWeight_monotone ‖a‖ ‖b‖ (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb)),
    radialWeight_image ‖a‖ ‖b‖ (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb),
    normalized_unit_segment_variation hlength _ _ hA hB hne,Gaussian.inner_normalize]
end Paper35.GaussianMarked

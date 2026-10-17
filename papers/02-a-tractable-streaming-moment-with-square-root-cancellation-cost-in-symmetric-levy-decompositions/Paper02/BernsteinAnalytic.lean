import Paper02.Bernstein
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The complete Bernstein kernel of Lemma B.1

We use the analytic characterization stated in Appendix B: a nonnegative
function on the positive real axis, vanishing at zero, whose holomorphic
extension to the slit plane has nonnegative imaginary part in the upper half
plane. The proofs below use the principal complex powers explicitly.
-/

noncomputable section

namespace Paper02.Bernstein

open Filter Topology Complex

/-- The analytic characterization of a complete Bernstein function with zero
killing term, as stated just before Lemma B.1. -/
def CompleteBernsteinZero (φ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 < t → 0 ≤ φ t) ∧ φ 0 = 0 ∧
  Tendsto φ (𝓝[>] 0) (𝓝 0) ∧
  ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ Complex.slitPlane ∧
    (∀ t : ℝ, 0 < t → Φ t = (φ t : ℂ)) ∧
    (∀ z : ℂ, 0 < z.im → 0 ≤ (Φ z).im)

/-- The real kernel in Lemma B.1. -/
def bernsteinKernel (a b c t : ℝ) : ℝ := t ^ a / (1 + t ^ b) ^ c

/-- Its extension defined using the principal complex powers. -/
def complexBernsteinKernel (a b c : ℝ) (z : ℂ) : ℂ :=
  z ^ (a : ℂ) / (1 + z ^ (b : ℂ)) ^ (c : ℂ)

lemma arg_pos_of_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < z.arg := by
  have ha : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hz.le
  by_contra hn
  have he : z.arg = 0 := by linarith
  have hi := (Complex.arg_eq_zero_iff.mp he).2
  linarith

lemma arg_lt_pi_of_im_pos {z : ℂ} (hz : 0 < z.im) : z.arg < Real.pi :=
  Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')

lemma arg_cpow_real {z : ℂ} (hz : z ≠ 0) (b : ℝ)
    (hlo : -Real.pi < z.arg * b) (hhi : z.arg * b ≤ Real.pi) :
    (z ^ (b : ℂ)).arg = z.arg * b := by
  rw [Complex.cpow_ofReal]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    (Complex.arg_mul_cos_add_sin_mul_I
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) b) ⟨hlo, hhi⟩)

lemma mul_arg_bounds {z : ℂ} (hz : z ∈ Complex.slitPlane) {b : ℝ}
    (hb : 0 ≤ b) (hb' : b ≤ 1) :
    -Real.pi < z.arg * b ∧ z.arg * b < Real.pi := by
  have hlo := Complex.neg_pi_lt_arg z
  have hhi : z.arg < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi z) (Complex.slitPlane_arg_ne_pi hz)
  have hpi := Real.pi_pos
  by_cases ha : 0 ≤ z.arg
  · have h1 := mul_nonneg ha hb
    have h2 := mul_le_mul_of_nonneg_left hb' ha
    constructor <;> nlinarith
  · have ha' : z.arg ≤ 0 := le_of_not_ge ha
    have h1 := mul_nonpos_of_nonpos_of_nonneg ha' hb
    have h2 := mul_le_mul_of_nonpos_left hb' ha'
    constructor <;> nlinarith

lemma cpow_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) {b : ℝ}
    (hb : 0 ≤ b) (hb' : b ≤ 1) : z ^ (b : ℂ) ∈ Complex.slitPlane := by
  have hbounds := mul_arg_bounds hz hb hb'
  have ha := arg_cpow_real (Complex.slitPlane_ne_zero hz) b hbounds.1 hbounds.2.le
  apply Complex.mem_slitPlane_iff_arg.mpr
  refine ⟨?_, Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero hz))⟩
  rw [ha]
  exact ne_of_lt hbounds.2

lemma one_add_mem_slitPlane {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    1 + w ∈ Complex.slitPlane := by
  rcases Complex.mem_slitPlane_iff.mp hw with hr | hi
  · apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using (show 0 < 1 + w.re by linarith)
  · apply Complex.mem_slitPlane_iff.mpr
    right
    simpa

lemma cpow_im_pos {z : ℂ} (hz : 0 < z.im) {b : ℝ} (hb : 0 < b)
    (hb' : b ≤ 1) : 0 < (z ^ (b : ℂ)).im := by
  have harg := arg_pos_of_im_pos hz
  have harg' := arg_lt_pi_of_im_pos hz
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  rw [Complex.cpow_ofReal_im]
  apply mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) b)
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos harg hb)
  have hmul := mul_le_mul_of_nonneg_left hb' harg.le
  nlinarith

lemma one_add_arg_sector {w : ℂ} (hw : 0 < w.im) :
    0 < (1 + w).arg ∧ (1 + w).arg < w.arg := by
  have hw1 : 0 < (1 + w).im := by simpa
  have hw0 : w ≠ 0 := by intro h; simpa [h] using hw
  have hw10 : 1 + w ≠ 0 := by intro h; simpa [h] using hw1
  have ha0 := arg_pos_of_im_pos hw
  have ha1 := arg_pos_of_im_pos hw1
  have hap := arg_lt_pi_of_im_pos hw
  have ha1p := arg_lt_pi_of_im_pos hw1
  have hqi : 0 < (w / (1 + w)).im := by
    have he : (w / (1 + w)).im = w.im / Complex.normSq (1 + w) := by
      rw [Complex.div_im]
      simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
        zero_add]
      ring
    rw [he]
    exact div_pos hw (Complex.normSq_pos.mpr hw10)
  have hqa := arg_pos_of_im_pos hqi
  have hinv : ((1 + w)⁻¹).arg = -(1 + w).arg := by
    rw [Complex.arg_inv, if_neg (ne_of_lt ha1p)]
  have hdiff : (w / (1 + w)).arg = w.arg - (1 + w).arg := by
    rw [div_eq_mul_inv, Complex.arg_mul hw0 (inv_ne_zero hw10), hinv]
    · ring
    · rw [hinv]
      constructor <;> linarith
  exact ⟨ha1, by linarith⟩

lemma complexBernsteinKernel_differentiableOn (a c : ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hb' : b ≤ 1) :
    DifferentiableOn ℂ (complexBernsteinKernel a b c) Complex.slitPlane := by
  intro z hz
  have hza : DifferentiableAt ℂ (fun z : ℂ => z ^ (a : ℂ)) z :=
    differentiableAt_id.cpow_const hz
  have hzb : DifferentiableAt ℂ (fun z : ℂ => z ^ (b : ℂ)) z :=
    differentiableAt_id.cpow_const hz
  have hw := one_add_mem_slitPlane (cpow_mem_slitPlane hz hb hb')
  have hden : DifferentiableAt ℂ (fun z : ℂ => (1 + z ^ (b : ℂ)) ^ (c : ℂ)) z :=
    (differentiableAt_const (1 : ℂ) |>.add hzb).cpow_const hw
  exact (hza.div hden
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero hw)))).differentiableWithinAt

lemma complexBernsteinKernel_real (a b c t : ℝ) (ht : 0 < t) :
    complexBernsteinKernel a b c t = (bernsteinKernel a b c t : ℂ) := by
  rw [complexBernsteinKernel, bernsteinKernel, Complex.ofReal_div,
    Complex.ofReal_cpow ht.le a,
    Complex.ofReal_cpow (by positivity : 0 ≤ 1 + t ^ b) c,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_cpow ht.le b]

lemma bernsteinKernel_nonneg (a b c t : ℝ) (ht : 0 ≤ t) :
    0 ≤ bernsteinKernel a b c t := by
  unfold bernsteinKernel
  positivity

lemma bernsteinKernel_zero {a : ℝ} (ha : 0 < a) (b c : ℝ) :
    bernsteinKernel a b c 0 = 0 := by
  simp [bernsteinKernel, Real.zero_rpow ha.ne']

lemma bernsteinKernel_tendsto_zero {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ c) : Tendsto (bernsteinKernel a b c) (𝓝[>] 0) (𝓝 0) := by
  have hnum := (Real.continuous_rpow_const ha.le).continuousAt (x := (0 : ℝ))
  have hbase : Continuous (fun t : ℝ => 1 + t ^ b) :=
    continuous_const.add (Real.continuous_rpow_const hb.le)
  have hden := ((Real.continuous_rpow_const hc).comp hbase).continuousAt (x := (0 : ℝ))
  have hden0 : (1 + (0 : ℝ) ^ b) ^ c ≠ 0 := by simp [Real.zero_rpow hb.ne']
  have hcont : ContinuousAt (bernsteinKernel a b c) 0 := hnum.div hden hden0
  simpa only [bernsteinKernel_zero ha] using
    hcont.tendsto.mono_left nhdsWithin_le_nhds

lemma complexBernsteinKernel_eq_exp (a b c : ℝ) {z : ℂ}
    (hz : z ≠ 0) (hw : 1 + z ^ (b : ℂ) ≠ 0) :
    complexBernsteinKernel a b c z =
      Complex.exp (Complex.log z * (a : ℂ) -
        Complex.log (1 + z ^ (b : ℂ)) * (c : ℂ)) := by
  rw [complexBernsteinKernel, Complex.cpow_def_of_ne_zero hz,
    Complex.cpow_def_of_ne_zero hw, Complex.exp_sub]

/-- The Pick property of the kernel follows from the sector inequalities. -/
lemma complexBernsteinKernel_im_nonneg {a b c : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1) (hb : 0 < b) (hb' : b ≤ 1)
    (hc : 0 ≤ c) (habc : b * c ≤ a) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (complexBernsteinKernel a b c z).im := by
  have hzslit : z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr hz.ne')
  have hsector := one_add_arg_sector (cpow_im_pos hz hb hb')
  have hbarg := mul_arg_bounds hzslit hb.le hb'
  have hpowarg := arg_cpow_real (Complex.slitPlane_ne_zero hzslit) b
    hbarg.1 hbarg.2.le
  rw [hpowarg] at hsector
  have hθ := arg_pos_of_im_pos hz
  have hθpi := arg_lt_pi_of_im_pos hz
  have hphase0 : 0 ≤ z.arg * a - (1 + z ^ (b : ℂ)).arg * c := by
    have hbound : (1 + z ^ (b : ℂ)).arg * c ≤ z.arg * a := by
      calc
        _ ≤ (z.arg * b) * c := mul_le_mul_of_nonneg_right hsector.2.le hc
        _ = z.arg * (b * c) := by ring
        _ ≤ z.arg * a := mul_le_mul_of_nonneg_left habc hθ.le
    linarith
  have hphasepi : z.arg * a - (1 + z ^ (b : ℂ)).arg * c ≤ Real.pi := by
    have hm := mul_le_mul_of_nonneg_left ha' hθ.le
    have hsc := mul_nonneg hsector.1.le hc
    nlinarith
  have hws := one_add_mem_slitPlane (cpow_mem_slitPlane hzslit hb.le hb')
  rw [complexBernsteinKernel_eq_exp a b c (Complex.slitPlane_ne_zero hzslit)
    (Complex.slitPlane_ne_zero hws), Complex.exp_im]
  apply mul_nonneg (Real.exp_pos _).le
  apply Real.sin_nonneg_of_mem_Icc
  simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.log_im, mul_zero, zero_add] using And.intro hphase0 hphasepi

/-- **Lemma B.1.** The complete Bernstein kernel, with the full original
parameter range and the analytic characterization stated in Appendix B. -/
theorem lemma_B1 {a b c : ℝ} (ha : 0 < a) (ha' : a ≤ 1)
    (hb : 0 < b) (hb' : b ≤ 1) (hc : 0 ≤ c) (habc : b * c ≤ a) :
    CompleteBernsteinZero (bernsteinKernel a b c) := by
  refine ⟨fun t ht => bernsteinKernel_nonneg a b c t ht.le,
    bernsteinKernel_zero ha b c, bernsteinKernel_tendsto_zero ha hb hc,
    complexBernsteinKernel a b c, complexBernsteinKernel_differentiableOn a c hb.le hb',
    complexBernsteinKernel_real a b c, ?_⟩
  intro z hz
  exact complexBernsteinKernel_im_nonneg ha ha' hb hb' hc habc hz

/-- Exact substitution `t=x²` for the damped powers in Proposition B.3. -/
lemma powerKernel_eq_bernsteinKernel (p β α : ℝ) (j : ℕ) (x : ℝ) :
    powerKernel p β α j x =
      bernsteinKernel (p / 2) (β / 2) ((j : ℝ) * α) (x ^ 2) := by
  rw [powerKernel_eq, bernsteinKernel,
    Real.rpow_div_two_eq_sqrt p (sq_nonneg x),
    Real.rpow_div_two_eq_sqrt β (sq_nonneg x), Real.sqrt_sq_eq_abs]
  rw [neg_mul, Real.rpow_neg (by positivity : 0 ≤ 1 + |x| ^ β)]
  rfl

/-- Exact substitution and positive scaling for Proposition B.2. -/
lemma singleNegative_eq_bernsteinKernel (α x : ℝ) :
    singleNegative α x = α⁻¹ * bernsteinKernel 1 (1 / 2) α (x ^ 2) := by
  rw [singleNegative, bernsteinKernel, Real.rpow_one,
    ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  ring

/-- The Bernstein kernel used in the single-logarithm construction. -/
theorem prop_B2_completeBernstein {n : ℕ} {ε : ℝ}
    (hn : 2 ≤ n) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    CompleteBernsteinZero (bernsteinKernel 1 (1 / 2) (singleAlpha n ε)) := by
  apply lemma_B1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (singleAlpha_pos hn hε).le
  have h := singleAlpha_lt_two hn hε'
  linarith

/-- Every damped kernel in Proposition B.3 meets Lemma B.1 with its actual
chosen finite-difference parameter. -/
theorem prop_B3_completeBernstein {p β ε : ℝ} {m n j : ℕ}
    (hp : 0 < p) (hp' : p ≤ 2) (hβ : 0 < β) (hβ' : β ≤ 2)
    (hm : 1 ≤ m) (hn : 2 ≤ n) (hε : 0 < ε) (hj : j ≤ m) :
    CompleteBernsteinZero
      (bernsteinKernel (p / 2) (β / 2) ((j : ℝ) * powerAlpha p β m n ε)) := by
  apply lemma_B1 (by linarith) (by linarith) (by linarith) (by linarith)
    (mul_nonneg (Nat.cast_nonneg j) (powerAlpha_pos hp hβ hm hn hε).le)
  exact powerAlpha_kernel_condition hp hβ hm hn hε hj

/-- Adding a nonnegative real number can only decrease the argument of a
point in the closed upper half plane. This includes the branch-cut boundary. -/
lemma one_add_arg_sector_nonneg {w : ℂ} (hw : 0 ≤ w.im) :
    0 ≤ (1 + w).arg ∧ (1 + w).arg ≤ w.arg := by
  rcases eq_or_lt_of_le hw with hi | hi
  · have him : w.im = 0 := hi.symm
    by_cases hr : 0 ≤ w.re
    · have hwarg : w.arg = 0 := Complex.arg_eq_zero_iff.mpr ⟨hr, him⟩
      have h1arg : (1 + w).arg = 0 := by
        apply Complex.arg_eq_zero_iff.mpr
        constructor
        · simpa using (show 0 ≤ 1 + w.re by linarith)
        · simp [him]
      simp [hwarg, h1arg]
    · have hwarg : w.arg = Real.pi :=
        Complex.arg_eq_pi_iff.mpr ⟨lt_of_not_ge hr, him⟩
      refine ⟨Complex.arg_nonneg_iff.mpr (by simp [him]), ?_⟩
      rw [hwarg]
      exact Complex.arg_le_pi _
  · have h := one_add_arg_sector hi
    exact ⟨h.1.le, h.2.le⟩

lemma cpow_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) {b : ℝ}
    (hb : 0 ≤ b) (hb' : b ≤ 1) : 0 ≤ (z ^ (b : ℂ)).im := by
  rw [Complex.cpow_ofReal_im]
  apply mul_nonneg (Real.rpow_nonneg (norm_nonneg z) b)
  apply Real.sin_nonneg_of_mem_Icc
  have harg := Complex.arg_nonneg_iff.mpr hz
  exact ⟨mul_nonneg harg hb, (by
    have h := mul_le_mul_of_nonneg_left hb' harg
    nlinarith [Complex.arg_le_pi z])⟩

/-- The same phase proof also controls the upper boundary of the branch cut.
At a pole the totalized complex quotient is zero; no representation identity
or absence of atomic Stieltjes mass is asserted here. -/
lemma complexBernsteinKernel_im_nonneg_closed {a b c : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1) (hb : 0 < b) (hb' : b ≤ 1)
    (hc : 0 ≤ c) (habc : b * c ≤ a) {z : ℂ} (hz : 0 ≤ z.im) :
    0 ≤ (complexBernsteinKernel a b c z).im := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [complexBernsteinKernel,
      Complex.zero_cpow (show (a : ℂ) ≠ 0 by exact_mod_cast ha.ne')]
  by_cases hw0 : 1 + z ^ (b : ℂ) = 0
  · by_cases hc0 : c = 0
    · subst c
      simpa [complexBernsteinKernel] using cpow_im_nonneg hz ha.le ha'
    · simp [complexBernsteinKernel, hw0,
        Complex.zero_cpow (show (c : ℂ) ≠ 0 by exact_mod_cast hc0)]
  have hθ : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hz
  have hθpi := Complex.arg_le_pi z
  have hbθ : z.arg * b ≤ Real.pi := by
    have h := mul_le_mul_of_nonneg_left hb' hθ
    nlinarith
  have hpowa := arg_cpow_real hz0 b
    (by nlinarith [mul_nonneg hθ hb.le, Real.pi_pos]) hbθ
  have hsector := one_add_arg_sector_nonneg (cpow_im_nonneg hz hb.le hb')
  rw [hpowa] at hsector
  have hphase0 : 0 ≤ z.arg * a - (1 + z ^ (b : ℂ)).arg * c := by
    have hbound : (1 + z ^ (b : ℂ)).arg * c ≤ z.arg * a := by
      calc
        _ ≤ (z.arg * b) * c := mul_le_mul_of_nonneg_right hsector.2 hc
        _ = z.arg * (b * c) := by ring
        _ ≤ z.arg * a := mul_le_mul_of_nonneg_left habc hθ
    linarith
  have hphasepi : z.arg * a - (1 + z ^ (b : ℂ)).arg * c ≤ Real.pi := by
    have hm := mul_le_mul_of_nonneg_left ha' hθ
    have hsc := mul_nonneg hsector.1 hc
    nlinarith
  rw [complexBernsteinKernel_eq_exp a b c hz0 hw0, Complex.exp_im]
  apply mul_nonneg (Real.exp_pos _).le
  apply Real.sin_nonneg_of_mem_Icc
  simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.log_im, mul_zero, zero_add] using And.intro hphase0 hphasepi

/-- The absolutely continuous Stieltjes boundary expression. Pole atoms, when
present, require a separate residue term in any integral representation. -/
def bernsteinBoundaryDensity (a b c s : ℝ) : ℝ :=
  (complexBernsteinKernel a b c (-s)).im / (Real.pi * s)

lemma bernsteinBoundaryDensity_nonneg {a b c s : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1) (hb : 0 < b) (hb' : b ≤ 1)
    (hc : 0 ≤ c) (habc : b * c ≤ a) (hs : 0 < s) :
    0 ≤ bernsteinBoundaryDensity a b c s := by
  apply div_nonneg
  · apply complexBernsteinKernel_im_nonneg_closed ha ha' hb hb' hc habc
    simp
  · exact (mul_pos Real.pi_pos hs).le

end Paper02.Bernstein

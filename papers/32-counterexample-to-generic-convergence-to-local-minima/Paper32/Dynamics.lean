import Mathlib.Data.Real.Sign
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Paper32

noncomputable section

/-- The sign used in the smooth quadrants; its value at zero is immaterial. -/
def quadrantSign (x : ℝ) : ℝ := if x < 0 then -1 else 1

lemma quadrantSign_eq_sign {x : ℝ} (hx : x ≠ 0) : quadrantSign x = Real.sign x := by
  by_cases hn : x < 0
  · simp [quadrantSign, hn, Real.sign_of_neg hn]
  · have hp : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx)
    simp [quadrantSign, hn, Real.sign_of_pos hp]

lemma quadrantSign_mul (x : ℝ) : quadrantSign x * x = |x| := by
  by_cases h : x < 0
  · simp [quadrantSign, h, abs_of_neg h]
  · simp [quadrantSign, h, abs_of_nonneg (le_of_not_gt h)]

lemma abs_quadrantSign (x : ℝ) : |quadrantSign x| = 1 := by
  unfold quadrantSign
  split_ifs <;> norm_num

lemma quadrantSign_sq (x : ℝ) : quadrantSign x * quadrantSign x = 1 := by
  unfold quadrantSign
  split_ifs <;> norm_num

/-- Lemma 5.1: a scalar attracting sign step. -/
theorem attracting_sign_step {u a δ α e : ℝ} (hu : 0 ≤ u)
    (_ha : δ < a) (_hδ : 0 ≤ δ) (hα : 0 < α) (he : |e| ≤ δ) :
    |u - α * (a + e)| ≤ max (u - (a - δ) * α) ((a + δ) * α) := by
  rcases abs_le.mp he with ⟨he₁, he₂⟩
  apply abs_le.mpr
  constructor
  · have := le_max_right (u - (a - δ) * α) ((a + δ) * α)
    nlinarith
  · have := le_max_left (u - (a - δ) * α) ((a + δ) * α)
    nlinarith

lemma abs_signed_update (x α a e : ℝ) :
    |x - α * (a * quadrantSign x + e)| =
      abs (|x| - α * (a + quadrantSign x * e)) := by
  have hs := quadrantSign_mul x
  have hsq := quadrantSign_sq x
  have heq : quadrantSign x * (x - α * (a * quadrantSign x + e)) =
      |x| - α * (a + quadrantSign x * e) := by
    calc
      _ = quadrantSign x * x - α * (a * (quadrantSign x * quadrantSign x) + quadrantSign x * e) := by ring
      _ = _ := by rw [hs, hsq]; ring
  calc
    _ = |quadrantSign x * (x - α * (a * quadrantSign x + e))| := by
      rw [abs_mul, abs_quadrantSign, one_mul]
    _ = _ := congrArg abs heq

/-- Exact numerical inequalities (A.1)--(A.3), with no invariant assumed. -/
structure TrapParameters where
  A : ℝ
  B : ℝ
  delta : ℝ
  kappa : ℝ
  X : ℝ
  Y : ℝ
  Z : ℝ
  delta_nonneg : 0 ≤ delta
  delta_lt_one : delta < 1
  delta_lt_A : delta < A
  one_lt_B : 1 < B
  one_le_kappa : 1 ≤ kappa
  X_pos : 0 < X
  Y_pos : 0 < Y
  Z_pos : 0 < Z
  B_delta_lt_X : B + delta < X
  A_delta_lt_Y : A + delta < Y
  X_ratio : X * (kappa - 1) < 1 - delta
  Y_ratio : Y * (kappa - 1) < A - delta
  vertical_cross : Y * kappa / ((B - 1) / (A + 1)) < B - delta
  vertical_Y : Y * kappa + 1 + delta < Z
  vertical_sector : Z < ((B - 1) / (A + 1)) * (B - delta) - Y * kappa
  recovery_Y : Z * kappa - (A - delta) < Y

namespace TrapParameters

def slope (p : TrapParameters) : ℝ := (p.B - 1) / (p.A + 1)

def Horizontal (p : TrapParameters) (x y : ℝ) : Prop := |y| < p.slope * |x|
local instance (p : TrapParameters) (x y : ℝ) : Decidable (p.Horizontal x y) :=
  Classical.propDecidable _

def Vertical (p : TrapParameters) (x y : ℝ) : Prop := p.slope * |x| < |y|

def Tight (p : TrapParameters) (r x y : ℝ) : Prop :=
  |x| ≤ p.X * r ∧ |y| ≤ p.Y * r

def Recovery (p : TrapParameters) (r x y : ℝ) : Prop :=
  |x| ≤ p.X * r ∧ |y| ≤ p.Z * r ∧ p.Horizontal x y

lemma slope_pos (p : TrapParameters) : 0 < p.slope := by
  apply div_pos <;> linarith [p.one_lt_B, p.delta_lt_A, p.delta_nonneg]

lemma Y_lt_Z (p : TrapParameters) : p.Y < p.Z := by
  have hk := mul_le_mul_of_nonneg_left p.one_le_kappa (le_of_lt p.Y_pos)
  nlinarith [p.vertical_Y, p.delta_nonneg]

/-- The actual smooth-sector recursion, with coordinatewise bounded additive errors.
The singular axes and sector boundary are excluded, as in Proposition A.1. -/
structure CoreStep (p : TrapParameters) (α x y x' y' : ℝ) where
  x_ne : x ≠ 0
  y_ne : y ≠ 0
  sector_ne : |y| ≠ p.slope * |x|
  ex : ℝ
  ey : ℝ
  ex_bound : |ex| ≤ p.delta
  ey_bound : |ey| ≤ p.delta
  x_update : x' = x - α * ((if p.Horizontal x y then 1 else p.B) * quadrantSign x + ex)
  y_update : y' = y - α * ((if p.Horizontal x y then p.A else -1) * quadrantSign y + ey)

lemma signed_noise_bound (p : TrapParameters) {x e : ℝ} (he : |e| ≤ p.delta) :
    |quadrantSign x * e| ≤ p.delta := by
  simpa [abs_mul, abs_quadrantSign] using he

lemma horizontal_coordinate {p : TrapParameters} {α r x e C a : ℝ}
    (hα : 0 < α) (hr : r ≤ p.kappa * α) (hx : |x| ≤ C * r)
    (hC : 0 ≤ C) (he : |e| ≤ p.delta) (ha : p.delta < a)
    (hdec : C * p.kappa - (a - p.delta) < C)
    (hsmall : a + p.delta < C) :
    |x - α * (a * quadrantSign x + e)| < C * α := by
  rw [abs_signed_update]
  have h := attracting_sign_step (abs_nonneg x) ha p.delta_nonneg hα
    (p.signed_noise_bound (x := x) he)
  apply lt_of_le_of_lt h
  apply max_lt
  · have hxr : |x| ≤ C * (p.kappa * α) :=
      hx.trans (mul_le_mul_of_nonneg_left hr hC)
    have hdecα := mul_lt_mul_of_pos_right hdec hα
    nlinarith only [hxr, hdecα]
  · exact mul_lt_mul_of_pos_right hsmall hα

/-- Tight H states return to the tight envelope. -/
theorem tight_horizontal {p : TrapParameters} {α r x y x' y' : ℝ}
    (hα : 0 < α) (hr : r ≤ p.kappa * α) (ht : p.Tight r x y)
    (hh : p.Horizontal x y) (hs : p.CoreStep α x y x' y') :
    p.Tight α x' y' := by
  rcases ht with ⟨hx, hy⟩
  constructor
  · rw [hs.x_update, if_pos hh]
    exact le_of_lt (horizontal_coordinate hα hr hx (le_of_lt p.X_pos) hs.ex_bound
      p.delta_lt_one (by nlinarith [p.X_ratio]) (by linarith [p.one_lt_B, p.B_delta_lt_X]))
  · rw [hs.y_update, if_pos hh]
    exact le_of_lt (horizontal_coordinate hα hr hy (le_of_lt p.Y_pos) hs.ey_bound
      p.delta_lt_A (by nlinarith [p.Y_ratio]) p.A_delta_lt_Y)

/-- Recovery H states return to the tight envelope. -/
theorem recovery_horizontal {p : TrapParameters} {α r x y x' y' : ℝ}
    (hα : 0 < α) (hr : r ≤ p.kappa * α) (ht : p.Recovery r x y)
    (hs : p.CoreStep α x y x' y') : p.Tight α x' y' := by
  rcases ht with ⟨hx, hy, hh⟩
  constructor
  · rw [hs.x_update, if_pos hh]
    exact le_of_lt (horizontal_coordinate hα hr hx (le_of_lt p.X_pos) hs.ex_bound
      p.delta_lt_one (by nlinarith [p.X_ratio]) (by linarith [p.one_lt_B, p.B_delta_lt_X]))
  · rw [hs.y_update, if_pos hh, abs_signed_update]
    have h := attracting_sign_step (abs_nonneg y) p.delta_lt_A p.delta_nonneg hα
      (p.signed_noise_bound (x := y) hs.ey_bound)
    apply le_of_lt (lt_of_le_of_lt h ?_)
    apply max_lt
    · have hyr := hy.trans (mul_le_mul_of_nonneg_left hr (le_of_lt p.Z_pos))
      have hrec := mul_lt_mul_of_pos_right p.recovery_Y hα
      nlinarith only [hyr, hrec]
    · exact mul_lt_mul_of_pos_right p.A_delta_lt_Y hα

/-- Tight V states cross the horizontal axis coordinate and land in recovery H. -/
theorem tight_vertical {p : TrapParameters} {α r x y x' y' : ℝ}
    (hα : 0 < α) (hr : r ≤ p.kappa * α) (ht : p.Tight r x y)
    (hv : p.Vertical x y) (hs : p.CoreStep α x y x' y') :
    p.Recovery α x' y' := by
  rcases ht with ⟨hx, hy⟩
  have hh : ¬ p.Horizontal x y := by
    unfold Horizontal Vertical at *
    linarith
  have hnx := abs_le.mp (p.signed_noise_bound (x := x) hs.ex_bound)
  have hny := abs_le.mp (p.signed_noise_bound (x := y) hs.ey_bound)
  have hpre : p.slope * |x| < (p.Y * p.kappa) * α := by
    calc
      _ < |y| := hv
      _ ≤ p.Y * r := hy
      _ ≤ p.Y * (p.kappa * α) := mul_le_mul_of_nonneg_left hr (le_of_lt p.Y_pos)
      _ = _ := by ring
  have hc : p.Y * p.kappa < p.slope * (p.B - p.delta) := by
    have h := p.vertical_cross
    change p.Y * p.kappa / p.slope < p.B - p.delta at h
    simpa only [mul_comm] using (div_lt_iff₀ p.slope_pos).mp h
  have hxpre : |x| < α * (p.B - p.delta) := by
    have hcα := mul_lt_mul_of_pos_right hc hα
    apply (mul_lt_mul_iff_right₀ p.slope_pos).mp
    nlinarith only [hpre, hcα]
  have hxneg : |x| - α * (p.B + quadrantSign x * hs.ex) < 0 := by
    nlinarith [hnx.1]
  have hxformula : |x'| = α * (p.B + quadrantSign x * hs.ex) - |x| := by
    calc
      |x'| = |x - α * ((if p.Horizontal x y then 1 else p.B) * quadrantSign x + hs.ex)| :=
        congrArg abs hs.x_update
      _ = _ := by rw [if_neg hh, abs_signed_update, abs_of_neg hxneg]; ring
  have hypos : 0 < |y| - α * (-1 + quadrantSign y * hs.ey) := by
    nlinarith [abs_nonneg y, hny.2, p.delta_lt_one]
  have hyformula : |y'| = |y| + α * (1 - quadrantSign y * hs.ey) := by
    calc
      |y'| = |y - α * ((if p.Horizontal x y then p.A else -1) * quadrantSign y + hs.ey)| :=
        congrArg abs hs.y_update
      _ = _ := by rw [if_neg hh, abs_signed_update, abs_of_pos hypos]; ring
  have hxbound : |x'| < p.X * α := by
    rw [hxformula]
    have hx0 := abs_nonneg x
    have hb := mul_lt_mul_of_pos_right p.B_delta_lt_X hα
    nlinarith [hnx.2]
  have hybound : |y'| < p.Z * α := by
    rw [hyformula]
    have hyr := hy.trans (mul_le_mul_of_nonneg_left hr (le_of_lt p.Y_pos))
    have hz := mul_lt_mul_of_pos_right p.vertical_Y hα
    nlinarith [hny.1]
  refine ⟨le_of_lt hxbound, le_of_lt hybound, ?_⟩
  change |y'| < p.slope * |x'|
  have hxnoise : α * (p.B - p.delta) ≤ α * (p.B + quadrantSign x * hs.ex) := by
    nlinarith [hnx.1]
  have hxnoise' := mul_le_mul_of_nonneg_left hxnoise (le_of_lt p.slope_pos)
  have hz := mul_lt_mul_of_pos_right p.vertical_sector hα
  change p.Z * α < (p.slope * (p.B - p.delta) - p.Y * p.kappa) * α at hz
  rw [hxformula]
  nlinarith only [hpre, hxnoise', hz, hybound]

/-- One invariant step: tight and recovery states are the two induction states. -/
theorem invariant_step {p : TrapParameters} {α r x y x' y' : ℝ}
    (hα : 0 < α) (hr : r ≤ p.kappa * α)
    (ht : p.Tight r x y ∨ p.Recovery r x y)
    (hs : p.CoreStep α x y x' y') :
    p.Tight α x' y' ∨ p.Recovery α x' y' := by
  rcases ht with ht | ht
  · by_cases hh : p.Horizontal x y
    · exact Or.inl (tight_horizontal hα hr ht hh hs)
    · have hv : p.Vertical x y := by
        unfold Horizontal at hh
        exact lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm hs.sector_ne)
      exact Or.inr (tight_vertical hα hr ht hv hs)
  · exact Or.inl (recovery_horizontal hα hr ht hs)

/-- The pathwise invariant in Proposition A.1, with its preceding-step scale. -/
theorem parameterized_invariant (p : TrapParameters)
    (α x y : ℕ → ℝ) (hα : ∀ k, 0 < α k)
    (hratio : ∀ k, α k ≤ p.kappa * α (k + 1))
    (hstep : ∀ k, p.CoreStep (α (k + 1)) (x (k + 1)) (y (k + 1))
      (x (k + 2)) (y (k + 2)))
    (hinit : p.Tight (α 0) (x 1) (y 1)) :
    ∀ k, p.Tight (α k) (x (k + 1)) (y (k + 1)) ∨
      p.Recovery (α k) (x (k + 1)) (y (k + 1)) := by
  intro k
  induction k with
  | zero => exact Or.inl hinit
  | succ k ih =>
      simpa [Nat.add_assoc] using invariant_step (hα (k + 1)) (hratio k) ih (hstep k)

/-- Local-to-global form: the smooth core recursion need only be available
on the envelope being proved invariant. This closes the induction for F=g+8. -/
theorem parameterized_invariant_local (p : TrapParameters)
    (α x y : ℕ → ℝ) (hα : ∀ k, 0 < α k)
    (hratio : ∀ k, α k ≤ p.kappa * α (k + 1))
    (hstep : ∀ k,
      (p.Tight (α k) (x (k + 1)) (y (k + 1)) ∨
        p.Recovery (α k) (x (k + 1)) (y (k + 1))) →
      p.CoreStep (α (k + 1)) (x (k + 1)) (y (k + 1))
        (x (k + 2)) (y (k + 2)))
    (hinit : p.Tight (α 0) (x 1) (y 1)) :
    ∀ k, p.Tight (α k) (x (k + 1)) (y (k + 1)) ∨
      p.Recovery (α k) (x (k + 1)) (y (k + 1)) := by
  intro k
  induction k with
  | zero => exact Or.inl hinit
  | succ k ih =>
      simpa [Nat.add_assoc] using
        invariant_step (hα (k + 1)) (hratio k) ih (hstep k ih)

/-- The asserted rectangular bounds, obtained from the two-state invariant. -/
theorem parameterized_bounds (p : TrapParameters)
    (α x y : ℕ → ℝ) (hα : ∀ k, 0 < α k)
    (hratio : ∀ k, α k ≤ p.kappa * α (k + 1))
    (hstep : ∀ k, p.CoreStep (α (k + 1)) (x (k + 1)) (y (k + 1))
      (x (k + 2)) (y (k + 2)))
    (hinit : p.Tight (α 0) (x 1) (y 1)) :
    ∀ k, |x (k + 1)| ≤ p.X * α k ∧ |y (k + 1)| ≤ p.Z * α k := by
  intro k
  rcases parameterized_invariant p α x y hα hratio hstep hinit k with ht | ht
  · exact ⟨ht.1, ht.2.trans (mul_le_mul_of_nonneg_right (le_of_lt p.Y_lt_Z) (le_of_lt (hα k)))⟩
  · exact ⟨ht.1, ht.2.1⟩

/-- The shrinking bounds imply convergence of each coordinate, without any
monotonicity hypothesis beyond the preceding-step ratio bound. -/
theorem parameterized_convergence (p : TrapParameters)
    (α x y : ℕ → ℝ) (hα : ∀ k, 0 < α k)
    (hlim : Filter.Tendsto α Filter.atTop (nhds 0))
    (hratio : ∀ k, α k ≤ p.kappa * α (k + 1))
    (hstep : ∀ k, p.CoreStep (α (k + 1)) (x (k + 1)) (y (k + 1))
      (x (k + 2)) (y (k + 2)))
    (hinit : p.Tight (α 0) (x 1) (y 1)) :
    Filter.Tendsto x Filter.atTop (nhds 0) ∧
      Filter.Tendsto y Filter.atTop (nhds 0) := by
  have hb := parameterized_bounds p α x y hα hratio hstep hinit
  have hx : Filter.Tendsto (fun k => x (k + 1)) Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm (fun k => ?_)
      (show Filter.Tendsto (fun k => p.X * α k) Filter.atTop (nhds 0) by
        simpa using hlim.const_mul p.X)
    simpa only [Real.norm_eq_abs] using (hb k).1
  have hy : Filter.Tendsto (fun k => y (k + 1)) Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm (fun k => ?_)
      (show Filter.Tendsto (fun k => p.Z * α k) Filter.atTop (nhds 0) by
        simpa using hlim.const_mul p.Z)
    simpa only [Real.norm_eq_abs] using (hb k).2
  exact ⟨(Filter.tendsto_add_atTop_iff_nat 1).mp hx,
    (Filter.tendsto_add_atTop_iff_nat 1).mp hy⟩

/-- The stronger invariant rules out two consecutive vertical-sector updates. -/
theorem no_consecutive_vertical (p : TrapParameters)
    (α x y : ℕ → ℝ) (hα : ∀ k, 0 < α k)
    (hratio : ∀ k, α k ≤ p.kappa * α (k + 1))
    (hstep : ∀ k, p.CoreStep (α (k + 1)) (x (k + 1)) (y (k + 1))
      (x (k + 2)) (y (k + 2)))
    (hinit : p.Tight (α 0) (x 1) (y 1)) (k : ℕ)
    (hv : p.Vertical (x (k + 1)) (y (k + 1))) :
    p.Horizontal (x (k + 2)) (y (k + 2)) := by
  rcases parameterized_invariant p α x y hα hratio hstep hinit k with ht | ht
  · exact (tight_vertical (hα (k + 1)) (hratio k) ht hv (hstep k)).2.2
  · have hh := ht.2.2
    unfold Horizontal Vertical at *
    linarith

/-- Proposition 5.2's constants satisfy every strict parameter-family inequality. -/
def numericalParameters : TrapParameters where
  A := 2
  B := 7
  delta := 0.02
  kappa := 1.13
  X := 7.2
  Y := 2.5
  Z := 3.9
  delta_nonneg := by norm_num
  delta_lt_one := by norm_num
  delta_lt_A := by norm_num
  one_lt_B := by norm_num
  one_le_kappa := by norm_num
  X_pos := by norm_num
  Y_pos := by norm_num
  Z_pos := by norm_num
  B_delta_lt_X := by norm_num
  A_delta_lt_Y := by norm_num
  X_ratio := by norm_num
  Y_ratio := by norm_num
  vertical_cross := by norm_num
  vertical_Y := by norm_num
  vertical_sector := by norm_num
  recovery_Y := by norm_num

/-- Proposition 5.2, explicitly specialized to the paper's numerical constants. -/
theorem two_state_pathwise_invariant
    (α x y : ℕ → ℝ) (hα : ∀ k, 0 < α k)
    (hlim : Filter.Tendsto α Filter.atTop (nhds 0))
    (hratio : ∀ k, α k ≤ 1.13 * α (k + 1))
    (hstep : ∀ k, numericalParameters.CoreStep (α (k + 1))
      (x (k + 1)) (y (k + 1)) (x (k + 2)) (y (k + 2)))
    (hinit : |x 1| ≤ 7.2 * α 0 ∧ |y 1| ≤ 2.5 * α 0) :
    (∀ k, |x (k + 1)| ≤ 7.2 * α k ∧ |y (k + 1)| ≤ 3.9 * α k) ∧
    Filter.Tendsto x Filter.atTop (nhds 0) ∧
    Filter.Tendsto y Filter.atTop (nhds 0) ∧
    (∀ k, 2 * |x (k + 1)| < |y (k + 1)| →
      |y (k + 2)| < 2 * |x (k + 2)|) := by
  refine ⟨parameterized_bounds numericalParameters α x y hα hratio hstep hinit,
    (parameterized_convergence numericalParameters α x y hα hlim hratio hstep hinit).1,
    (parameterized_convergence numericalParameters α x y hα hlim hratio hstep hinit).2, ?_⟩
  intro k hv
  have h := no_consecutive_vertical numericalParameters α x y hα hratio hstep hinit k
  norm_num [Horizontal, Vertical, slope, numericalParameters] at h
  exact h hv

end TrapParameters
end
end Paper32

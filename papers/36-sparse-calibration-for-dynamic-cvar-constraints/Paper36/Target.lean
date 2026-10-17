import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! The deterministic target of (4.4)--(4.8), with its numerical parameters exposed.
The inequalities on the parameters below are the numerical consequences of (4.4),
not assumptions of subadditivity or of a residual estimate. -/
namespace Paper36.Target

noncomputable section
open Real

/-- The target in (4.5), including its specified value at zero. -/
def target (c A ν M : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else c * Real.sqrt ((n : ℝ) * (A + ν * Real.log n) * (M + Real.log n))

def G₀ (A M : ℝ) : ℝ := Real.sqrt (A * M)
def gamma₀ (A ν M : ℝ) : ℝ := (A + ν * M) / (2 * G₀ A M)
def residual (c A ν M δ : ℝ) : ℝ :=
  c ^ 2 / (2 * δ) *
    (G₀ A M + 2 * gamma₀ A ν M * Real.log (1 + 4 * gamma₀ A ν M * c / δ)) ^ 2

@[simp] theorem target_zero (c A ν M : ℝ) : target c A ν M 0 = 0 := by simp [target]

theorem target_nonneg {c A ν M : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ target c A ν M n := by
  unfold target
  split_ifs
  · rfl
  · exact mul_nonneg hc (Real.sqrt_nonneg _)

private theorem log_ge_zero {x : ℝ} (hx : 1 ≤ x) : 0 ≤ Real.log x :=
  Real.log_nonneg hx

/-- Each affine log factor grows no faster than the square root of its argument. -/
theorem affine_log_ratio {a v x y : ℝ} (hv : 0 ≤ v) (ha : 2 * v ≤ a)
    (hx : 1 ≤ x) (hxy : x ≤ y) :
    a + v * Real.log y ≤ Real.sqrt (y / x) * (a + v * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hrat : 1 ≤ y / x := (le_div_iff₀ hx0).2 (by simpa using hxy)
  have hr : 1 ≤ Real.sqrt (y / x) := (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ y / x)).2 (by simpa using hrat)
  have hr0 : 0 < Real.sqrt (y / x) := by linarith
  have hlog := Real.log_le_sub_one_of_pos hr0
  have hlogeq : Real.log y = Real.log x + 2 * Real.log (Real.sqrt (y / x)) := by
    rw [Real.log_sqrt (le_of_lt (div_pos hy0 hx0)), Real.log_div hy0.ne' hx0.ne']
    ring
  have hxlog := log_ge_zero hx
  have hbase : 2 * v ≤ a + v * Real.log x := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hbase (sub_nonneg.2 hr)
  rw [hlogeq]
  nlinarith [mul_le_mul_of_nonneg_left hlog hv]

/-- The normalized squared target is antitone on [1,∞). -/
theorem normalized_antitone {A ν M x y : ℝ} (hν : 0 ≤ ν)
    (hA : 2 * ν ≤ A) (hM : 2 ≤ M) (hx : 1 ≤ x) (hxy : x ≤ y) :
    (A + ν * Real.log y) * (M + Real.log y) / y ≤
      (A + ν * Real.log x) * (M + Real.log x) / x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hy : 1 ≤ y := hx.trans hxy
  have hAx : 0 ≤ A + ν * Real.log x := by
    have := log_ge_zero hx
    nlinarith
  have hMx : 0 ≤ M + Real.log x := by have := log_ge_zero hx; linarith
  have hAy : 0 ≤ A + ν * Real.log y := by
    have := log_ge_zero hy
    nlinarith
  have hMy : 0 ≤ M + Real.log y := by have := log_ge_zero hy; linarith
  have h1 := affine_log_ratio hν hA hx hxy
  have h2 := affine_log_ratio (v := 1) (a := M) (by norm_num) (by simpa using hM) hx hxy
  simp only [one_mul] at h2
  have hp := mul_le_mul h1 h2 hMy (mul_nonneg (Real.sqrt_nonneg _) hAx)
  have hs := Real.sq_sqrt (show 0 ≤ y / x by positivity)
  have hp' : (A + ν * Real.log y) * (M + Real.log y) ≤
      (y / x) * ((A + ν * Real.log x) * (M + Real.log x)) := by
    calc
      _ ≤ (Real.sqrt (y / x) * (A + ν * Real.log x)) *
          (Real.sqrt (y / x) * (M + Real.log x)) := hp
      _ = (Real.sqrt (y / x))^2 * ((A + ν * Real.log x) * (M + Real.log x)) := by ring
      _ = (y / x) * ((A + ν * Real.log x) * (M + Real.log x)) := by rw [hs]
  apply (div_le_div_iff₀ hy0 hx0).2
  calc
    _ ≤ ((y / x) * ((A + ν * Real.log x) * (M + Real.log x))) * x :=
      mul_le_mul_of_nonneg_right hp' hx0.le
    _ = _ := by field_simp

/-- An equivalent expression useful for the bank's subadditivity argument. -/
theorem target_normalized {c A ν M : ℝ} {n : ℕ} (hn : n ≠ 0) :
    target c A ν M n = c * (n : ℝ) *
      Real.sqrt ((A + ν * Real.log n) * (M + Real.log n) / n) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [target, if_neg hn]
  have heq : (n : ℝ) * (A + ν * Real.log n) * (M + Real.log n) =
      (n : ℝ) ^ 2 * ((A + ν * Real.log n) * (M + Real.log n) / n) := by
    field_simp
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hn0)]
  ring

/-- The actual target (4.5) is subadditive on the natural numbers. -/
theorem target_subadditive {c A ν M : ℝ} (hc : 0 ≤ c) (hν : 0 ≤ ν)
    (hA : 2 * ν ≤ A) (hM : 2 ≤ M) (j n : ℕ) :
    target c A ν M (j + n) ≤ target c A ν M j + target c A ν M n := by
  by_cases hj : j = 0
  · simp [hj]
  by_cases hn : n = 0
  · simp [hn]
  have hsum : j + n ≠ 0 := by omega
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have hjle : (j : ℝ) ≤ j + n := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hnle : (n : ℝ) ≤ j + n := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have h1 := Real.sqrt_le_sqrt (normalized_antitone hν hA hM hj1 hjle)
  have h2 := Real.sqrt_le_sqrt (normalized_antitone hν hA hM hn1 hnle)
  rw [target_normalized hsum, target_normalized hj, target_normalized hn]
  push_cast
  have hh1 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ c * (j : ℝ) by positivity)
  have hh2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ c * (n : ℝ) by positivity)
  nlinarith

/-- The square-root product lies below its tangent at zero (Appendix D). -/
theorem G_tangent {A ν M x : ℝ} (hA : 0 < A) (hM : 0 < M)
    (hν : 0 ≤ ν) (hx : 0 ≤ x) :
    Real.sqrt ((A + ν * x) * (M + x)) ≤ G₀ A M + gamma₀ A ν M * x := by
  have hg : 0 < G₀ A M := Real.sqrt_pos.2 (mul_pos hA hM)
  have hg2 : G₀ A M ^ 2 = A * M := Real.sq_sqrt (le_of_lt (mul_pos hA hM))
  have hγ : 0 ≤ gamma₀ A ν M := by unfold gamma₀; positivity
  have hcross : 2 * G₀ A M * gamma₀ A ν M = A + ν * M := by
    unfold gamma₀
    field_simp
  have hsq : ν ≤ gamma₀ A ν M ^ 2 := by
    have heq : gamma₀ A ν M ^ 2 = (A + ν * M)^2 / (4 * A * M) := by
      unfold gamma₀
      rw [div_pow]
      congr 1
      nlinarith [hg2]
    rw [heq]
    apply (le_div_iff₀ (show 0 < 4 * A * M by positivity)).2
    nlinarith [sq_nonneg (A - ν * M)]
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have hzero : 2 * G₀ A M * gamma₀ A ν M - A - ν * M = 0 := by linarith
    have hdiff : (G₀ A M + gamma₀ A ν M * x)^2 - (A + ν * x) * (M + x) =
        (gamma₀ A ν M ^ 2 - ν) * x^2 := by
      calc
        _ = (G₀ A M ^ 2 - A * M) +
            (2 * G₀ A M * gamma₀ A ν M - A - ν * M) * x +
            (gamma₀ A ν M ^ 2 - ν) * x^2 := by ring
        _ = _ := by rw [hg2, hzero]; ring
    have := mul_nonneg (sub_nonneg.2 hsq) (sq_nonneg x)
    linarith

/-- A logarithm estimate with the exact coefficient used in Appendix D. -/
theorem log_linear_bound {y b : ℝ} (hy : 0 < y) (hb : 0 < b) :
    Real.log y ≤ y / b + Real.log (1 + b) := by
  have hb1 : 0 < 1 + b := by positivity
  have hz := Real.log_le_sub_one_of_pos (div_pos hy hb1)
  rw [Real.log_div hy.ne' hb1.ne'] at hz
  have hdiv : y / (1 + b) ≤ y / b := by
    exact div_le_div_of_nonneg_left (le_of_lt hy) hb (by linarith)
  linarith

/-- The explicit residual estimate in (4.8), pointwise in every integer episode count. -/
theorem target_drift_bound {c A ν M δ : ℝ} (hc : 0 ≤ c) (hA : 0 < A)
    (hM : 0 < M) (hν : 0 ≤ ν) (hδ : 0 < δ) (n : ℕ) :
    target c A ν M n - (n : ℝ) * δ ≤ residual c A ν M δ := by
  have hR : 0 ≤ residual c A ν M δ := by unfold residual; positivity
  by_cases hn : n = 0
  · simpa [hn] using hR
  by_cases hc0 : c = 0
  · simp [target, hn, hc0, residual]
    positivity
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hγpos : 0 < gamma₀ A ν M := by
    unfold gamma₀ G₀
    positivity
  let y := Real.sqrt (n : ℝ)
  let γ := gamma₀ A ν M
  let g := G₀ A M
  let b := 4 * γ * c / δ
  let B := g + 2 * γ * Real.log (1 + b)
  have hy : 0 < y := Real.sqrt_pos.2 hnpos
  have hy2 : y ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hb : 0 < b := by dsimp [b, γ]; positivity
  have hlogy := log_linear_bound hy hb
  have hlogn : Real.log (n : ℝ) = 2 * Real.log y := by
    dsimp [y]
    rw [Real.log_sqrt hnpos.le]
    ring
  have htang := G_tangent hA hM hν hlog
  have htarget : target c A ν M n ≤ c * y * (g + 2 * γ * Real.log y) := by
    rw [target, if_neg hn]
    have heq : (n : ℝ) * (A + ν * Real.log n) * (M + Real.log n) =
        (n : ℝ) * ((A + ν * Real.log n) * (M + Real.log n)) := by ring
    rw [heq, Real.sqrt_mul hnpos.le]
    calc
      _ ≤ c * y * (g + γ * Real.log n) := by
        simpa only [g, γ, y, mul_assoc] using
          mul_le_mul_of_nonneg_left htang (show 0 ≤ c * y by positivity)
      _ = _ := by rw [hlogn]; ring
  have hcoeff : c * y * (g + 2 * γ * Real.log y) ≤ c * y * B + δ / 2 * y ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlogy (show 0 ≤ c * y * (2 * γ) by
      dsimp [γ]; positivity)
    have hbne : b ≠ 0 := hb.ne'
    have hcalc : c * y * (2 * γ) * (y / b) = δ / 2 * y^2 := by
      dsimp [b]
      field_simp [show γ ≠ 0 from hγpos.ne', hcpos.ne', hδ.ne']
      <;> ring
    dsimp [B]
    nlinarith [hcalc]
  have hquad : c * y * B - δ / 2 * y ^ 2 ≤ c ^ 2 / (2 * δ) * B ^ 2 := by
    have h := sq_nonneg (δ * y - c * B)
    have heq : c ^ 2 / (2 * δ) * B ^ 2 = (c ^ 2 * B ^ 2) / (2 * δ) := by ring
    rw [heq]
    apply (le_div_iff₀ (show 0 < 2 * δ by positivity)).2
    nlinarith
  have hReq : residual c A ν M δ = c ^ 2 / (2 * δ) * B ^ 2 := rfl
  rw [hReq]
  nlinarith

/-- Positive parts are bounded as well, the form used in (5.14). -/
theorem target_drift_pos_bound {c A ν M δ : ℝ} (hc : 0 ≤ c) (hA : 0 < A)
    (hM : 0 < M) (hν : 0 ≤ ν) (hδ : 0 < δ) (n : ℕ) :
    max (target c A ν M n - (n : ℝ) * δ) 0 ≤ residual c A ν M δ := by
  apply max_le
  · exact target_drift_bound hc hA hM hν hδ n
  · unfold residual
    positivity

/-- Constants from (4.4). Dimensions are real numbers here so natural dimensions
can be inserted by coercion without changing the source formulas. -/
def nu (s : ℝ) : ℝ := s + 2
def lambda0 (s a h : ℝ) : ℝ := s * Real.log (h + 1) + Real.log (8 * s * a * h)
def m0 (h : ℝ) : ℝ := Real.log (Real.exp 1 * h)
def A0 (s a h : ℝ) : ℝ := lambda0 s a h + 2 * nu s
def M0 (h : ℝ) : ℝ := m0 h + 2
def scale (w s a : ℝ) : ℝ := 4 * Real.sqrt 2 * w * Real.sqrt (s * a)
def Lambda (s a h : ℝ) (k : ℕ) : ℝ :=
  s * Real.log ((k : ℝ) * h + 1) + Real.log (8 * s * a * h * (k : ℝ)^2)
/-- (4.3), after factoring sqrt(S A) into c as in (4.4). -/
def confidence (c s a h : ℝ) (k : ℕ) : ℝ :=
  c * Real.sqrt (Lambda s a h k * Real.log (Real.exp 1 * (k : ℝ) * h))

private theorem base_one_le {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    1 ≤ 8 * s * a * h := by
  have hsa := one_le_mul_of_one_le_of_one_le hs ha
  have hsah := one_le_mul_of_one_le_of_one_le hsa hh
  nlinarith

theorem lambda0_nonneg {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    0 ≤ lambda0 s a h := by
  unfold lambda0
  have h1 : 0 ≤ Real.log (h + 1) := Real.log_nonneg (by linarith)
  have h2 := Real.log_nonneg (base_one_le hs ha hh)
  positivity

theorem parameter_bounds {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    0 < nu s ∧ 2 * nu s ≤ A0 s a h ∧ 2 ≤ M0 h := by
  have hlam := lambda0_nonneg hs ha hh
  have hm : 0 ≤ m0 h := by
    unfold m0
    apply Real.log_nonneg
    have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.2 (by norm_num)
    exact one_le_mul_of_one_le_of_one_le he hh
  dsimp [nu, A0, M0] at *
  constructor
  · linarith
  constructor <;> linarith

/-- The confidence log is bounded by the log factor used by the anytime target. -/
theorem Lambda_le {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h)
    {k : ℕ} (hk : 1 ≤ k) :
    Lambda s a h k ≤ lambda0 s a h + nu s * Real.log k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hh0 : 0 < h := by linarith
  have hb : 0 < 8 * s * a * h := by have := base_one_le hs ha hh; linarith
  have hlog := Real.log_le_log (show 0 < (k : ℝ) * h + 1 by positivity)
    (show (k : ℝ) * h + 1 ≤ (k : ℝ) * (h + 1) by nlinarith)
  rw [Real.log_mul hk0.ne' (show h + 1 ≠ 0 by linarith)] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ s by linarith)
  unfold Lambda lambda0 nu
  rw [Real.log_mul hb.ne' (pow_ne_zero 2 hk0.ne'), Real.log_pow]
  norm_num only at *
  nlinarith

/-- The first inequality of (5.14), retaining the original confidence and target logs. -/
theorem confidence_majorization {c s a h : ℝ} (hc : 0 ≤ c)
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) {k : ℕ} (hk : 1 ≤ k) :
    confidence c s a h k * Real.sqrt (k : ℝ) ≤
      target c (A0 s a h) (nu s) (M0 h) k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hk)
  have hkn : k ≠ 0 := by omega
  have hh0 : 0 < h := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hb1 := base_one_le hs ha hh
  have hlam : 0 ≤ Lambda s a h k := by
    unfold Lambda
    have h1 : 0 ≤ Real.log ((k : ℝ) * h + 1) := Real.log_nonneg (by
      have : 0 ≤ (k : ℝ) * h := by positivity
      linarith)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h2 : 1 ≤ 8 * s * a * h * (k : ℝ)^2 := by
      apply one_le_mul_of_one_le_of_one_le hb1
      nlinarith
    have h3 := Real.log_nonneg h2
    positivity
  have hν := parameter_bounds hs ha hh
  have hA : Lambda s a h k ≤ A0 s a h + nu s * Real.log k := by
    have h := Lambda_le hs ha hh hk
    have h0 := lambda0_nonneg hs ha hh
    dsimp [A0]
    linarith [hν.1]
  have hlogeq : Real.log (Real.exp 1 * (k : ℝ) * h) = m0 h + Real.log k := by
    have heq : Real.exp 1 * (k : ℝ) * h = (Real.exp 1 * h) * k := by ring
    rw [heq, Real.log_mul (mul_pos (Real.exp_pos _) hh0).ne' hk0.ne']
    rfl
  have hm : 0 ≤ Real.log (Real.exp 1 * (k : ℝ) * h) := by
    apply Real.log_nonneg
    have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.2 (by norm_num)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le he hk1) hh
  have hM : Real.log (Real.exp 1 * (k : ℝ) * h) ≤ M0 h + Real.log k := by
    rw [hlogeq]
    unfold M0
    linarith
  have hp := mul_le_mul hA hM hm (by linarith : 0 ≤ A0 s a h + nu s * Real.log k)
  have hroot := Real.sqrt_le_sqrt hp
  unfold confidence target
  rw [if_neg hkn]
  have heq : (k : ℝ) * (A0 s a h + nu s * Real.log k) * (M0 h + Real.log k) =
      (k : ℝ) * ((A0 s a h + nu s * Real.log k) * (M0 h + Real.log k)) := by ring
  rw [heq, Real.sqrt_mul hk0.le]
  have := mul_le_mul_of_nonneg_left hroot (show 0 ≤ c * Real.sqrt (k : ℝ) by positivity)
  nlinarith

/-- The residual supremum in the literal statement of (5.14). -/
theorem target_drift_sup_bound {c A ν M δ : ℝ} (hc : 0 ≤ c) (hA : 0 < A)
    (hM : 0 < M) (hν : 0 ≤ ν) (hδ : 0 < δ) :
    sSup (Set.range (fun n : ℕ => max (target c A ν M n - (n : ℝ) * δ) 0)) ≤
      residual c A ν M δ := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact target_drift_pos_bound hc hA hM hν hδ n

/-- The target has sublinear growth. This uses the already established drift
bound for every positive slope, so does not assume a logarithmic asymptotic. -/
theorem target_sublinear {c A ν M : ℝ} (hc : 0 ≤ c) (hA : 0 < A)
    (hM : 0 < M) (hν : 0 ≤ ν) :
    Filter.Tendsto (fun n : ℕ => target c A ν M n / (n : ℝ)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let R := residual c A ν M δ
  have hR : 0 ≤ R := by dsimp [R, residual]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R / ε + 1)
  refine ⟨N, fun n hn => ?_⟩
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnn' : 2 * R / ε + 1 < (n : ℝ) := hN.trans_le hnn
  have hnpos : (0 : ℝ) < n := by
    have : 0 ≤ 2 * R / ε := by positivity
    linarith
  have hsmall : R < (n : ℝ) * δ := by
    have hdiv : 2 * R / ε < (n : ℝ) := by linarith
    have := (div_lt_iff₀ hε).1 hdiv
    dsimp [δ]
    nlinarith
  have hbound := target_drift_bound hc hA hM hν hδ n
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (target_nonneg hc n) hnpos.le)]
  apply (div_lt_iff₀ hnpos).2
  dsimp [R] at hsmall
  dsimp [δ] at hbound hsmall
  nlinarith

/-- Monotonicity needed when comparing the last deposit with the terminal target. -/
theorem target_monotone {c A ν M : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hν : 0 ≤ ν) (hM : 0 ≤ M) : Monotone (target c A ν M) := by
  intro j n hjn
  by_cases hj : j = 0
  · simpa [hj] using target_nonneg (A := A) (ν := ν) (M := M) hc n
  have hn : n ≠ 0 := by omega
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have hjpos : (0 : ℝ) < j := by linarith
  have hcast : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hlog := Real.log_le_log hjpos hcast
  have hlogj : 0 ≤ Real.log j := Real.log_nonneg hj1
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hAj : 0 ≤ A + ν * Real.log j := by positivity
  have hAn : 0 ≤ A + ν * Real.log n := by positivity
  have hMj : 0 ≤ M + Real.log j := by positivity
  have hfacA : A + ν * Real.log j ≤ A + ν * Real.log n := by nlinarith
  have hfacM : M + Real.log j ≤ M + Real.log n := by linarith
  rw [target, if_neg hj, target, if_neg hn]
  apply mul_le_mul_of_nonneg_left _ hc
  apply Real.sqrt_le_sqrt
  exact mul_le_mul (mul_le_mul hcast hfacA hAj (Nat.cast_nonneg _))
    hfacM hMj (mul_nonneg (Nat.cast_nonneg _) hAn)

theorem scale_nonneg {w s a : ℝ} (hw : 0 ≤ w) : 0 ≤ scale w s a := by
  unfold scale
  positivity

/-- Lemma 5.9 with every constant instantiated by its source formula. -/
theorem lemma_5_9 {s a h w δ : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (hw : 0 ≤ w) (hδ : 0 < δ) (k : ℕ) (hk : 1 ≤ k) (j n : ℕ) :
    (confidence (scale w s a) s a h k * Real.sqrt (k : ℝ) ≤
      target (scale w s a) (A0 s a h) (nu s) (M0 h) k) ∧
    (target (scale w s a) (A0 s a h) (nu s) (M0 h) (j + n) ≤
      target (scale w s a) (A0 s a h) (nu s) (M0 h) j +
      target (scale w s a) (A0 s a h) (nu s) (M0 h) n) ∧
    (sSup (Set.range (fun m : ℕ => max
      (target (scale w s a) (A0 s a h) (nu s) (M0 h) m - (m : ℝ) * δ) 0)) ≤
      residual (scale w s a) (A0 s a h) (nu s) (M0 h) δ) := by
  have hp := parameter_bounds hs ha hh
  have hApos : 0 < A0 s a h := by linarith [hp.1, hp.2.1]
  have hMpos : 0 < M0 h := by linarith [hp.2.2]
  exact ⟨confidence_majorization (scale_nonneg hw) hs ha hh hk,
    target_subadditive (scale_nonneg hw) hp.1.le hp.2.1 hp.2.2 j n,
    target_drift_sup_bound (scale_nonneg hw) hApos hMpos hp.1.le hδ⟩

/-- H=1 gives W=0 and therefore exactly zero target, as specified after (4.5). -/
@[simp] theorem target_scale_zero (s a h : ℝ) (n : ℕ) :
    target (scale 0 s a) (A0 s a h) (nu s) (M0 h) n = 0 := by
  simp [target, scale]

/-- Factoring the scale does not change the confidence quantity of (4.3). -/
theorem confidence_source_formula {s a h w : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (k : ℕ) :
    confidence (scale w s a) s a h k = 4 * Real.sqrt 2 * w *
      Real.sqrt (s * a * Lambda s a h k * Real.log (Real.exp 1 * (k : ℝ) * h)) := by
  unfold confidence scale
  calc
    _ = (4 * Real.sqrt 2 * w) * (Real.sqrt (s * a) *
        Real.sqrt (Lambda s a h k * Real.log (Real.exp 1 * (k : ℝ) * h))) := by ring
    _ = (4 * Real.sqrt 2 * w) * Real.sqrt
        ((s * a) * (Lambda s a h k * Real.log (Real.exp 1 * (k : ℝ) * h))) := by
      rw [Real.sqrt_mul (mul_nonneg hs ha)]
    _ = _ := by congr 2; ring

end
end Paper36.Target

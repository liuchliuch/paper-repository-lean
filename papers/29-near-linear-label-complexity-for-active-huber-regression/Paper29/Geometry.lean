import Paper29.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Scalar and finite weighted Huber geometry, including all of Lemma 3.1. -/
noncomputable section
open scoped BigOperators

namespace Paper29

@[simp] theorem huber_zero : huber 0 = 0 := by norm_num [huber]

@[simp] theorem huber_neg (t : ℝ) : huber (-t) = huber t := by
  simp [huber]

@[simp] theorem huber_abs (t : ℝ) : huber |t| = huber t := by
  simp [huber, sq_abs]

theorem huber_nonneg (t : ℝ) : 0 ≤ huber t := by
  unfold huber
  split_ifs with h
  · positivity
  · have := abs_nonneg t
    push_neg at h
    linarith

theorem huber_le_sq (t : ℝ) : huber t ≤ t ^ 2 / 2 := by
  unfold huber
  split_ifs with h
  · rfl
  · have hs := sq_nonneg (|t| - 1)
    nlinarith [sq_abs t]

theorem huber_le_abs (t : ℝ) : huber t ≤ |t| := by
  unfold huber
  split_ifs with h
  · have hp := mul_nonneg (abs_nonneg t) (sub_nonneg.mpr h)
    nlinarith [sq_abs t]
  · linarith

theorem abs_sub_half_le_huber (t : ℝ) : |t| - 1 / 2 ≤ huber t := by
  unfold huber
  split_ifs with h
  · have := sq_nonneg (|t| - 1)
    nlinarith [sq_abs t]
  · rfl

theorem huber_mono_nonneg {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    huber s ≤ huber t := by
  have ht : 0 ≤ t := hs.trans hst
  unfold huber
  rw [abs_of_nonneg hs, abs_of_nonneg ht]
  split_ifs with h₁ h₂ h₂
  · nlinarith
  · have hx := mul_nonneg hs (sub_nonneg.mpr h₁)
    linarith
  · exact (h₁ (hst.trans h₂)).elim
  · linarith

theorem huber_mono_abs {s t : ℝ} (h : |s| ≤ |t|) : huber s ≤ huber t := by
  simpa only [huber_abs] using huber_mono_nonneg (abs_nonneg s) h

@[simp] theorem huber_eq_zero_iff (t : ℝ) : huber t = 0 ↔ t = 0 := by
  constructor
  · intro h
    unfold huber at h
    split_ifs at h with ht
    · apply sq_eq_zero_iff.mp
      linarith
    · have hh : 1 < |t| := lt_of_not_ge ht
      linarith
  · rintro rfl
    exact huber_zero

/-- A continuous expression for the two pieces of Huber loss. -/
theorem huber_eq_min_max (t : ℝ) :
    huber t = (min |t| 1) ^ 2 / 2 + max (|t| - 1) 0 := by
  by_cases ht : |t| ≤ 1
  · simp [huber, ht, sq_abs]
  · have ht' : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    simp [huber, ht, min_eq_right ht', max_eq_left (sub_nonneg.mpr ht')]
    ring

theorem continuous_huber : Continuous huber := by
  have h : Continuous (fun t : ℝ => (min |t| 1) ^ 2 / 2 + max (|t| - 1) 0) :=
    (((continuous_abs.min continuous_const).pow 2).div_const 2).add
      ((continuous_abs.sub continuous_const).max continuous_const)
  simpa only [← huber_eq_min_max] using h

/-- The exact lower-one and upper-two scaling bounds in equation (3.12). -/
theorem huber_scaling_nonneg {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) :
    a * huber t ≤ huber (a * t) ∧ huber (a * t) ≤ a ^ 2 * huber t := by
  have ha0 : 0 ≤ a := by linarith
  have hat : 0 ≤ a * t := mul_nonneg ha0 ht
  by_cases ht1 : t ≤ 1
  · have hform : huber t = t ^ 2 / 2 := by simp [huber, abs_of_nonneg ht, ht1]
    constructor
    · by_cases hat1 : a * t ≤ 1
      · have hform' : huber (a * t) = (a * t) ^ 2 / 2 := by
          simp [huber, abs_of_nonneg hat, hat1]
        rw [hform, hform']
        have haa : a ≤ a ^ 2 := by nlinarith
        have hh := mul_le_mul_of_nonneg_right haa (sq_nonneg t)
        nlinarith
      · have hform' : huber (a * t) = a * t - 1 / 2 := by
          simp [huber, abs_of_nonneg hat, hat1]
        rw [hform, hform']
        have hh : t ^ 2 ≤ t := by nlinarith
        have hmul := mul_le_mul_of_nonneg_left hh ha0
        have hlarge : 1 < a * t := lt_of_not_ge hat1
        linarith
    · calc
        huber (a * t) ≤ (a * t) ^ 2 / 2 := huber_le_sq _
        _ = a ^ 2 * huber t := by rw [hform]; ring
  · have htlarge : 1 < t := lt_of_not_ge ht1
    have hatlarge : 1 < a * t := lt_of_lt_of_le htlarge (le_mul_of_one_le_left ht ha)
    have hform : huber t = t - 1 / 2 := by simp [huber, abs_of_nonneg ht, ht1]
    have hform' : huber (a * t) = a * t - 1 / 2 := by
      simp [huber, abs_of_nonneg hat, not_le.mpr hatlarge]
    rw [hform, hform']
    constructor
    · nlinarith
    · have haux : 0 ≤ a * t - (a + 1) / 2 := by
        have hh := le_mul_of_one_le_right ha0 htlarge.le
        nlinarith
      have hh := mul_nonneg (sub_nonneg.mpr ha) haux
      nlinarith

theorem huber_scaling {a t : ℝ} (ha : 1 ≤ a) :
    a * huber t ≤ huber (a * t) ∧ huber (a * t) ≤ a ^ 2 * huber t := by
  have h := huber_scaling_nonneg ha (abs_nonneg t)
  have he : huber (a * |t|) = huber (a * t) := by
    rw [← huber_abs (a * t), abs_mul, abs_of_nonneg (show 0 ≤ a by linarith)]
  simpa only [huber_abs, he] using h

theorem psi_nonneg (t : ℝ) : 0 ≤ psi t := Real.sqrt_nonneg _

@[simp] theorem psi_zero : psi 0 = 0 := by simp [psi]

@[simp] theorem psi_neg (t : ℝ) : psi (-t) = psi t := by simp [psi]

@[simp] theorem psi_abs (t : ℝ) : psi |t| = psi t := by simp [psi]

theorem psi_sq (t : ℝ) : psi t ^ 2 = huber t := Real.sq_sqrt (huber_nonneg t)

theorem psi_mono_abs {s t : ℝ} (h : |s| ≤ |t|) : psi s ≤ psi t :=
  Real.sqrt_le_sqrt (huber_mono_abs h)

theorem psi_quadratic {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    psi t = t * Real.sqrt (1 / 2) := by
  have he : huber t = t ^ 2 / 2 := by simp [huber, abs_of_nonneg ht, ht']
  have hc := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hp := psi_sq t
  have hs := psi_nonneg t
  have ht0 := mul_nonneg ht (Real.sqrt_nonneg (1 / 2))
  have hsq : (t * Real.sqrt (1 / 2)) ^ 2 = t ^ 2 / 2 := by
    rw [mul_pow, hc]
    ring
  apply (sq_eq_sq₀ hs ht0).mp
  rw [hp, hsq, he]

theorem psi_one_le {t : ℝ} (ht : 1 ≤ t) :
    Real.sqrt (1 / 2) ≤ psi t := by
  have h := psi_mono_abs (s := 1) (t := t) (by
    rw [abs_one, abs_of_nonneg (by linarith : 0 ≤ t)]
    exact ht)
  simpa [psi_quadratic (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)] using h

/-- Nonnegative scalar subadditivity, proved from the two pieces of Huber's formula. -/
theorem psi_add_le_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    psi (s + t) ≤ psi s + psi t := by
  have hsqrt := psi_nonneg (s + t)
  have hss := psi_nonneg s
  have hts := psi_nonneg t
  have hsum := psi_sq (s + t)
  have hs2 := psi_sq s
  have ht2 := psi_sq t
  have hc := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hc0 := Real.sqrt_nonneg (1 / 2)
  by_cases hs1 : s ≤ 1
  · by_cases ht1 : t ≤ 1
    · have hsq := huber_le_sq (s + t)
      rw [psi_quadratic hs hs1, psi_quadratic ht ht1]
      apply (sq_le_sq₀ hsqrt (by positivity)).mp
      rw [psi_sq]
      calc
        huber (s + t) ≤ (s + t) ^ 2 / 2 := hsq
        _ = (s * Real.sqrt (1 / 2) + t * Real.sqrt (1 / 2)) ^ 2 := by
          rw [← add_mul, mul_pow, hc]
          ring
    · have ht1' : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
      have hp := psi_one_le ht1'
      have he : huber (s + t) = huber t + s := by
        have hh : 1 < s + t := by linarith
        have hh' : 1 < t := by linarith
        simp [huber, abs_of_nonneg ht, abs_of_nonneg (add_nonneg hs ht),
          not_le.mpr hh, not_le.mpr hh']
        ring
      have hpbound : (1 / 2 : ℝ) ≤ Real.sqrt (1 / 2) * psi t := by
        nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hp)]
      have hm : s ≤ 2 * psi s * psi t := by
        rw [psi_quadratic hs hs1]
        nlinarith [mul_nonneg hs (sub_nonneg.mpr hpbound)]
      apply (sq_le_sq₀ hsqrt (add_nonneg hss hts)).mp
      nlinarith [huber_nonneg s]
  · have hs1' : 1 ≤ s := le_of_lt (lt_of_not_ge hs1)
    by_cases ht1 : t ≤ 1
    · have hp := psi_one_le hs1'
      have he : huber (s + t) = huber s + t := by
        have hh : 1 < s + t := by linarith
        have hh' : 1 < s := by linarith
        simp [huber, abs_of_nonneg hs, abs_of_nonneg (add_nonneg hs ht),
          not_le.mpr hh, not_le.mpr hh']
        ring
      have hpbound : (1 / 2 : ℝ) ≤ Real.sqrt (1 / 2) * psi s := by
        nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hp)]
      have hm : t ≤ 2 * psi s * psi t := by
        rw [psi_quadratic ht ht1]
        nlinarith [mul_nonneg ht (sub_nonneg.mpr hpbound)]
      apply (sq_le_sq₀ hsqrt (add_nonneg hss hts)).mp
      nlinarith [huber_nonneg t]
    · have ht1' : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
      have hp := psi_one_le hs1'
      have hq := psi_one_le ht1'
      have hm : (1 / 2 : ℝ) ≤ psi s * psi t := by
        have hh := mul_le_mul hp hq hc0 hss
        nlinarith
      have he : huber (s + t) = huber s + huber t + 1 / 2 := by
        have hh : 1 < s + t := by linarith
        simp [huber, abs_of_nonneg hs, abs_of_nonneg ht,
          abs_of_nonneg (add_nonneg hs ht), hs1, ht1, not_le.mpr hh]
        ring
      apply (sq_le_sq₀ hsqrt (add_nonneg hss hts)).mp
      nlinarith

/-- Equation (3.1), the triangle inequality for the square root of Huber loss. -/
theorem huber_triangle (s t : ℝ) : psi (s + t) ≤ psi s + psi t := by
  calc
    psi (s + t) ≤ psi (|s| + |t|) := psi_mono_abs (by
      rw [abs_of_nonneg (add_nonneg (abs_nonneg s) (abs_nonneg t))]
      exact abs_add_le s t)
    _ ≤ psi |s| + psi |t| := psi_add_le_nonneg (abs_nonneg s) (abs_nonneg t)
    _ = psi s + psi t := by simp

/-- A convenient squared consequence of the Huber triangle inequality. -/
theorem huber_add_le (s t : ℝ) : huber (s + t) ≤ 2 * (huber s + huber t) := by
  have h := (sq_le_sq₀ (psi_nonneg (s + t))
    (add_nonneg (psi_nonneg s) (psi_nonneg t))).mpr (huber_triangle s t)
  rw [psi_sq] at h
  nlinarith [psi_sq s, psi_sq t, sq_nonneg (psi s - psi t)]

/-- Equation (3.2), the reverse triangle inequality. -/
theorem psi_sub_le (s t : ℝ) : |psi s - psi t| ≤ psi (s - t) := by
  apply abs_le.mpr
  constructor
  · have h := huber_triangle (s - t) (-s)
    have he : s - t + -s = -t := by ring
    rw [he, psi_neg, psi_neg] at h
    linarith
  · have h := huber_triangle (s - t) t
    rw [sub_add_cancel] at h
    linarith

/-- Equation (3.3), the increment inequality for Huber loss. -/
theorem huber_increment (s t : ℝ) :
    |huber s - huber t| ≤ psi (s - t) * (psi s + psi t) := by
  have hsum : 0 ≤ psi s + psi t := add_nonneg (psi_nonneg s) (psi_nonneg t)
  calc
    |huber s - huber t| = |psi s - psi t| * (psi s + psi t) := by
      rw [← psi_sq s, ← psi_sq t, ← abs_of_nonneg hsum, ← abs_mul]
      congr 1
      ring
    _ ≤ psi (s - t) * (psi s + psi t) :=
      mul_le_mul_of_nonneg_right (psi_sub_le s t) hsum

/-- Finite weighted Huber objectives are nonnegative for arbitrary nonnegative real weights. -/
theorem weightedHuber_nonneg {ι : Type*} [Fintype ι] (w y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ weightedHuber w y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (huber_nonneg (y i))

/-- Equation (3.4), including zero weights and empty finite index types. -/
theorem weightedHuber_triangle {ι : Type*} [Fintype ι] (w y z : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    Real.sqrt (weightedHuber w (fun i => y i + z i)) ≤
      Real.sqrt (weightedHuber w y) + Real.sqrt (weightedHuber w z) := by
  let C : ℝ := ∑ i, w i * psi (y i) * psi (z i)
  have hA := weightedHuber_nonneg w y hw
  have hB := weightedHuber_nonneg w z hw
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (hw i) (psi_nonneg (y i))) (psi_nonneg (z i))
  have hCS : C ^ 2 ≤ weightedHuber w y * weightedHuber w z := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun i _ => mul_nonneg (hw i) (huber_nonneg (y i)))
      (fun i _ => mul_nonneg (hw i) (huber_nonneg (z i)))
    intro i _
    simp only [mul_pow, psi_sq]
    ring
  have hprod : C ≤ Real.sqrt (weightedHuber w y) * Real.sqrt (weightedHuber w z) := by
    have he : (Real.sqrt (weightedHuber w y) * Real.sqrt (weightedHuber w z)) ^ 2 =
        weightedHuber w y * weightedHuber w z := by
      rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
    exact (sq_le_sq₀ hC (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
      (by rw [he]; exact hCS)
  have hpoint (i : ι) : huber (y i + z i) ≤
      huber (y i) + huber (z i) + 2 * psi (y i) * psi (z i) := by
    have h := (sq_le_sq₀ (psi_nonneg (y i + z i))
      (add_nonneg (psi_nonneg (y i)) (psi_nonneg (z i)))).mpr (huber_triangle (y i) (z i))
    rw [psi_sq] at h
    nlinarith [psi_sq (y i), psi_sq (z i)]
  have hsum : weightedHuber w (fun i => y i + z i) ≤
      weightedHuber w y + weightedHuber w z + 2 * C := by
    calc
      weightedHuber w (fun i => y i + z i) ≤
          ∑ i, w i * (huber (y i) + huber (z i) + 2 * psi (y i) * psi (z i)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hw i)
      _ = weightedHuber w y + weightedHuber w z + 2 * C := by
        simp only [weightedHuber, C, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]

@[simp] theorem weightedHuber_neg {ι : Type*} [Fintype ι] (w y : ι → ℝ) :
    weightedHuber w (fun i => -y i) = weightedHuber w y := by
  simp [weightedHuber]

/-- Reverse triangle inequality for the square root of a weighted Huber objective. -/
theorem weightedHuber_reverse_triangle {ι : Type*} [Fintype ι] (w y z : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    |Real.sqrt (weightedHuber w y) - Real.sqrt (weightedHuber w z)| ≤
      Real.sqrt (weightedHuber w (fun i => y i - z i)) := by
  apply abs_le.mpr
  constructor
  · have h := weightedHuber_triangle w (fun i => y i - z i) (fun i => -y i) hw
    have he : (fun i => y i - z i + -y i) = (fun i => -z i) := by
      funext i
      ring
    rw [he, weightedHuber_neg, weightedHuber_neg] at h
    linarith
  · have h := weightedHuber_triangle w (fun i => y i - z i) z hw
    simp only [sub_add_cancel] at h
    linarith

/-- Increment inequality for arbitrary finite weighted Huber objectives. -/
theorem weightedHuber_increment {ι : Type*} [Fintype ι] (w y z : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    |weightedHuber w y - weightedHuber w z| ≤
      Real.sqrt (weightedHuber w (fun i => y i - z i)) *
        (Real.sqrt (weightedHuber w y) + Real.sqrt (weightedHuber w z)) := by
  have hA := weightedHuber_nonneg w y hw
  have hB := weightedHuber_nonneg w z hw
  have hs : 0 ≤ Real.sqrt (weightedHuber w y) + Real.sqrt (weightedHuber w z) := by
    positivity
  calc
    |weightedHuber w y - weightedHuber w z| =
        |Real.sqrt (weightedHuber w y) - Real.sqrt (weightedHuber w z)| *
          (Real.sqrt (weightedHuber w y) + Real.sqrt (weightedHuber w z)) := by
      conv_lhs => rw [← Real.sq_sqrt hA, ← Real.sq_sqrt hB]
      rw [← abs_of_nonneg hs, ← abs_mul]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (weightedHuber_reverse_triangle w y z hw) hs

end Paper29

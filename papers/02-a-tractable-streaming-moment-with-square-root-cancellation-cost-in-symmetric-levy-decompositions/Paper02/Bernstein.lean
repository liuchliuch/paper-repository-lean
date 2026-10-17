import Paper02.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Appendix B algebraic inequalities
-/

noncomputable section

namespace Paper02.Bernstein

open Real

/-- Upper half of (B.5): `(1-e^{-y})/y ≤ 1` for `y > 0`. -/
lemma eq_B5_upper (y : ℝ) (hy : 0 < y) : (1 - exp (-y)) / y ≤ 1 := by
  have h : 1 - exp (-y) ≤ y := by
    have hexp := add_one_le_exp (-y)
    nlinarith
  rw [div_le_iff₀ hy]
  nlinarith [h]

/-- Proposition B.2 ratio identity. -/
lemma prop_B2_ratio (α k : ℝ) (hk : k ≠ 0) (hα : α > 0) :
    ((α⁻¹ * k ^ 2 - α⁻¹ * k ^ 2 / (1 + |k|) ^ α) / (k ^ 2 * log (1 + |k|)))
      = (1 - exp (-α * log (1 + |k|))) / (α * log (1 + |k|)) := by
  have hk2 : 0 < k ^ 2 := sq_pos_of_ne_zero hk
  have h1p : 1 < 1 + |k| := by nlinarith [abs_nonneg k, abs_pos.mpr hk]
  have hlog : 0 < log (1 + |k|) := Real.log_pos h1p
  have hpow : (1 + |k|) ^ α = exp (α * log (1 + |k|)) := by
    rw [rpow_def_of_pos (by nlinarith [abs_nonneg k] : 0 < 1 + |k|), mul_comm]
  have hG : α⁻¹ * k ^ 2 - α⁻¹ * k ^ 2 / (1 + |k|) ^ α
      = α⁻¹ * k ^ 2 * (1 - exp (-α * log (1 + |k|))) := by
    have hden : α⁻¹ * k ^ 2 / (1 + |k|) ^ α
        = α⁻¹ * k ^ 2 * exp (-(α * log (1 + |k|))) := by
      rw [hpow, Real.exp_neg, div_eq_mul_inv]
    calc α⁻¹ * k ^ 2 - α⁻¹ * k ^ 2 / (1 + |k|) ^ α
        = α⁻¹ * k ^ 2 - α⁻¹ * k ^ 2 * exp (-(α * log (1 + |k|))) := by rw [hden]
      _ = α⁻¹ * k ^ 2 * (1 - exp (-α * log (1 + |k|))) := by ring_nf
  rw [hG]
  rw [div_eq_div_iff (by nlinarith [mul_pos hk2 hlog] : k ^ 2 * log (1 + |k|) ≠ 0)
    (by nlinarith [mul_pos hα hlog] : α * log (1 + |k|) ≠ 0)]
  field_simp [hα.ne']

/-- Proposition B.2 envelope (B.4), for `|k| ≥ 1` (nonzero integers). -/
lemma prop_B2_envelope (α k : ℝ) (hk : 1 ≤ |k|) (hα : α > 0) :
    α⁻¹ * k ^ 2 + α⁻¹ * k ^ 2 / (1 + |k|) ^ α
      ≤ (2 / (α * log 2)) * (k ^ 2 * log (1 + |k|)) := by
  have hk2 : 0 < k ^ 2 := by
    have hkne : k ≠ 0 := by
      intro h
      subst h
      rw [abs_zero] at hk
      linarith
    exact sq_pos_of_ne_zero hkne
  have hlog : log 2 ≤ log (1 + |k|) := by
    have : (2:ℝ) ≤ 1 + |k| := by nlinarith
    exact log_le_log (by norm_num) this
  have hpow : 1 ≤ (1 + |k|) ^ α := by
    have hbase : 1 ≤ 1 + |k| := by nlinarith [abs_nonneg k]
    exact one_le_rpow hbase (le_of_lt hα)
  have hdiv : α⁻¹ * k ^ 2 / (1 + |k|) ^ α ≤ α⁻¹ * k ^ 2 := by
    have hnn : 0 ≤ α⁻¹ * k ^ 2 := by positivity
    exact div_le_self hnn hpow
  have h : α⁻¹ * k ^ 2 + α⁻¹ * k ^ 2 / (1 + |k|) ^ α
      ≤ 2 * α⁻¹ * k ^ 2 := by nlinarith
  have h2 : 0 < log 2 := Real.log_pos (by norm_num)
  have h3 : (2 / (α * log 2)) * (k ^ 2 * log (1 + |k|))
      = 2 * α⁻¹ * k ^ 2 * (log (1 + |k|) / log 2) := by
    field_simp [hα.ne']
  have h4 : 1 ≤ log (1 + |k|) / log 2 := by
    rw [le_div_iff₀ h2]
    nlinarith
  have hnn : 0 ≤ 2 * α⁻¹ * k ^ 2 := by positivity
  have h5 : 2 * α⁻¹ * k ^ 2 ≤ 2 * α⁻¹ * k ^ 2 * (log (1 + |k|) / log 2) := by
    nlinarith [mul_le_mul_of_nonneg_left h4 hnn]
  rw [h3]
  nlinarith

/-- Lower half of (B.5), obtained by integrating the tangent-line bound on `[-y,0]`. -/
lemma eq_B5_lower (y : ℝ) (hy : 0 < y) :
    1 - y / 2 ≤ (1 - exp (-y)) / y := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (a := -y) (b := 0) (by linarith)
    ((show Continuous (fun t : ℝ => 1 + t) from continuous_const.add continuous_id).intervalIntegrable _ _)
    (Real.continuous_exp.intervalIntegrable _ _) (fun t _ => by simpa [add_comm] using Real.add_one_le_exp t)
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const,
    integral_id, integral_exp] at h
  · rw [le_div_iff₀ hy]
    simp only [sub_neg_eq_add, zero_add, smul_eq_mul, Real.exp_zero, zero_pow,
      OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true] at h
    nlinarith
  · exact continuous_const.intervalIntegrable _ _
  · exact continuous_id.intervalIntegrable _ _

/-- The exponent selected in Proposition B.2. -/
def singleAlpha (n : ℕ) (ε : ℝ) : ℝ := 2 * ε / log (1 + n)

/-- The target single logarithmic moment. -/
def singleMoment (x : ℝ) : ℝ := x ^ 2 * log (1 + |x|)

/-- Positive member in the explicit single-logarithm split. -/
def singlePositive (α x : ℝ) : ℝ := α⁻¹ * x ^ 2

/-- Damped member in the explicit single-logarithm split. -/
def singleNegative (α x : ℝ) : ℝ := α⁻¹ * x ^ 2 / (1 + |x|) ^ α

lemma singleAlpha_pos {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) :
    0 < singleAlpha n ε := by
  unfold singleAlpha
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_pos (by linarith) (log_pos (by linarith))

lemma singleAlpha_lt_two {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : ε < 1 / 2) :
    singleAlpha n ε < 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 1 / 2 ≤ log (1 + n) := by
    have h := one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have h' := log_le_log (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≤ 1 + n by linarith)
    norm_num at h
    linarith
  unfold singleAlpha
  rw [div_lt_iff₀ (by linarith : 0 < log (1 + n))]
  linarith

/-- Both inequalities in (B.3), with the original choice of `α`; this also covers zero. -/
theorem prop_B2_error {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε)
    (x : ℝ) (hx : |x| ≤ n) :
    (1 - ε) * singleMoment x ≤
        singlePositive (singleAlpha n ε) x - singleNegative (singleAlpha n ε) x ∧
    singlePositive (singleAlpha n ε) x - singleNegative (singleAlpha n ε) x ≤
        singleMoment x := by
  by_cases hx0 : x = 0
  · subst x
    simp [singleMoment, singlePositive, singleNegative]
  have ha := singleAlpha_pos hn hε
  have hlog : 0 < log (1 + |x|) := log_pos (by linarith [abs_pos.mpr hx0])
  have hL : 0 < log (1 + (n : ℝ)) := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact log_pos (by linarith)
  have hlogle : log (1 + |x|) ≤ log (1 + (n : ℝ)) :=
    log_le_log (by linarith [abs_nonneg x]) (by linarith)
  have hy : 0 < singleAlpha n ε * log (1 + |x|) := mul_pos ha hlog
  have hyle : singleAlpha n ε * log (1 + |x|) ≤ 2 * ε := by
    calc
      _ ≤ singleAlpha n ε * log (1 + (n : ℝ)) := mul_le_mul_of_nonneg_left hlogle ha.le
      _ = 2 * ε := by unfold singleAlpha; field_simp
  have hlo := eq_B5_lower _ hy
  have hup := eq_B5_upper _ hy
  have hratio := prop_B2_ratio (singleAlpha n ε) x hx0 ha
  simp only [neg_mul] at hratio
  have hF : 0 < singleMoment x := mul_pos (sq_pos_of_ne_zero hx0) hlog
  change (singlePositive (singleAlpha n ε) x - singleNegative (singleAlpha n ε) x) /
    singleMoment x = _ at hratio
  have hlo' : (1 - ε) ≤
      (singlePositive (singleAlpha n ε) x - singleNegative (singleAlpha n ε) x) /
        singleMoment x := by rw [hratio]; linarith
  have hup' :
      (singlePositive (singleAlpha n ε) x - singleNegative (singleAlpha n ε) x) /
        singleMoment x ≤ 1 := by rw [hratio]; exact hup
  exact ⟨(le_div_iff₀ hF).mp hlo', by simpa using (div_le_iff₀ hF).mp hup'⟩

/-- Equation (B.4), including the vanishing value at zero. -/
theorem prop_B2_integer_envelope {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε)
    (k : ℤ) :
    singlePositive (singleAlpha n ε) k + singleNegative (singleAlpha n ε) k ≤
      (log (1 + n) / (ε * log 2)) * singleMoment k := by
  by_cases hk : k = 0
  · subst k
    simp [singlePositive, singleNegative, singleMoment]
  have hk' : (1 : ℝ) ≤ |(k : ℝ)| := by
    have hz : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
    exact_mod_cast hz
  have ha := singleAlpha_pos hn hε
  have h := prop_B2_envelope (singleAlpha n ε) k hk' ha
  have heq : 2 / (singleAlpha n ε * log 2) = log (1 + n) / (ε * log 2) := by
    unfold singleAlpha
    field_simp
  simpa only [singlePositive, singleNegative, singleMoment, heq] using h

/-- Proposition B.2's positive exponent is an actual Gaussian Lévy exponent. -/
theorem prop_B2_positive_mem {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) :
    IsLSym (singlePositive (singleAlpha n ε)) :=
  isLSym_gaussian (inv_nonneg.mpr (singleAlpha_pos hn hε).le)


/-- The power version of (B.5), including Bernoulli's inequality. -/
lemma eq_B5_power {m : ℕ} {ε y : ℝ} (hm : 1 ≤ m) (hε : 0 < ε)
    (hε' : ε < 1 / 2) (hy : 0 < y) (hmy : (m : ℝ) * y ≤ 2 * ε) :
    1 - ε ≤ ((1 - exp (-y)) / y) ^ m ∧
      ((1 - exp (-y)) / y) ^ m ≤ 1 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hylt : y < 1 := by nlinarith
  have hb : 0 ≤ 1 - y / 2 := by linarith
  have hlo := eq_B5_lower y hy
  have hup := eq_B5_upper y hy
  have hbern := one_add_mul_sub_le_pow (a := 1 - y / 2) (by linarith : -1 ≤ 1 - y / 2) m
  have hr : 0 ≤ (1 - exp (-y)) / y := hb.trans hlo
  constructor
  · have hp := pow_le_pow_left₀ hb hlo m
    nlinarith
  · exact pow_le_one₀ hr hup

/-- Parameters in the fixed-logarithmic-power construction (B.6). -/
def powerAlpha (p β : ℝ) (m n : ℕ) (ε : ℝ) : ℝ :=
  min (2 * ε / ((m : ℝ) * log (1 + (n : ℝ) ^ β))) (p / ((m : ℝ) * β))

/-- The exact original fixed-logarithmic-power target. -/
def powerMoment (p β : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  |x| ^ p * (log (1 + |x| ^ β)) ^ m

/-- The damped powers `H_j` from Proposition B.3. -/
def powerKernel (p β α : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  |x| ^ p * exp ((j : ℝ) * (-α * log (1 + |x| ^ β)))

/-- Positive finite-difference part from (B.6), with the even terms explicit. -/
def powerPositive (p β α : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  α⁻¹ ^ m * ∑ j ∈ Finset.range (m + 1),
    if Even j then (m.choose j : ℝ) * powerKernel p β α j x else 0

/-- Negative finite-difference part from (B.6), with the odd terms explicit. -/
def powerNegative (p β α : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  α⁻¹ ^ m * ∑ j ∈ Finset.range (m + 1),
    if Even j then 0 else (m.choose j : ℝ) * powerKernel p β α j x

/-- `powerKernel` agrees with the expression in the paper. -/
lemma powerKernel_eq (p β α : ℝ) (j : ℕ) (x : ℝ) :
    powerKernel p β α j x = |x| ^ p * (1 + |x| ^ β) ^ (-(j : ℝ) * α) := by
  have hb : 0 < 1 + |x| ^ β := by positivity
  unfold powerKernel
  rw [rpow_def_of_pos hb]
  congr 2
  ring

lemma powerAlpha_pos {p β ε : ℝ} {m n : ℕ} (hp : 0 < p) (hβ : 0 < β)
    (hm : 1 ≤ m) (hn : 2 ≤ n) (hε : 0 < ε) : 0 < powerAlpha p β m n ε := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hn' : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have hL : 0 < log (1 + (n : ℝ) ^ β) := log_pos (by linarith [rpow_pos_of_pos (show (0 : ℝ) < n by linarith) β])
  exact lt_min (div_pos (by positivity) (mul_pos hm' hL))
    (div_pos hp (mul_pos hm' hβ))

/-- The kernel parameters meet the original `bc ≤ a` condition for every term. -/
lemma powerAlpha_kernel_condition {p β ε : ℝ} {m n j : ℕ}
    (hp : 0 < p) (hβ : 0 < β) (hm : 1 ≤ m) (hn : 2 ≤ n) (hε : 0 < ε)
    (hj : j ≤ m) :
    (β / 2) * ((j : ℝ) * powerAlpha p β m n ε) ≤ p / 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
  have ha := powerAlpha_pos hp hβ hm hn hε
  have hα : powerAlpha p β m n ε ≤ p / ((m : ℝ) * β) := min_le_right _ _
  have hα' := (le_div_iff₀ (mul_pos hm' hβ)).mp hα
  have hjα : (j : ℝ) * powerAlpha p β m n ε ≤ m * powerAlpha p β m n ε :=
    mul_le_mul_of_nonneg_right hj' ha.le
  nlinarith

/-- Exact binomial identity for the two parts of (B.6). -/
lemma prop_B3_difference (p β α : ℝ) (m : ℕ) (x : ℝ) :
    powerPositive p β α m x - powerNegative p β α m x =
      |x| ^ p * α⁻¹ ^ m * (1 - exp (-α * log (1 + |x| ^ β))) ^ m := by
  let q := exp (-α * log (1 + |x| ^ β))
  have hk (j : ℕ) : powerKernel p β α j x = |x| ^ p * q ^ j := by
    simp only [powerKernel, q, Real.exp_nat_mul]
  have hb := add_pow (-q) (1 : ℝ) m
  simp only [one_pow, mul_one] at hb
  have hneg (j : ℕ) : (-q) ^ j = (-1 : ℝ) ^ j * q ^ j := by
    rw [← mul_pow, neg_one_mul]
  simp only [hneg] at hb
  have hbase : -q + 1 = 1 - q := by ring
  rw [hbase] at hb
  unfold powerPositive powerNegative
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  calc
    _ = α⁻¹ ^ m * ∑ j ∈ Finset.range (m + 1),
        |x| ^ p * ((-1 : ℝ) ^ j * q ^ j * (m.choose j : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [hk, neg_one_pow_eq_ite]
      split_ifs <;> ring
    _ = |x| ^ p * α⁻¹ ^ m * (1 - q) ^ m := by
      rw [← Finset.mul_sum, ← hb]
      ring

/-- The sum of the two finite-difference parts has no alternating signs. -/
lemma prop_B3_sum (p β α : ℝ) (m : ℕ) (x : ℝ) :
    powerPositive p β α m x + powerNegative p β α m x =
      α⁻¹ ^ m * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * powerKernel p β α j x := by
  unfold powerPositive powerNegative
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

/-- The unnormalised cancellation bound in Proposition B.3. -/
lemma prop_B3_sum_le {p β α : ℝ} (hα : 0 ≤ α) (m : ℕ) (x : ℝ) :
    powerPositive p β α m x + powerNegative p β α m x ≤
      (2 : ℝ) ^ m * α⁻¹ ^ m * |x| ^ p := by
  have hlog : 0 ≤ log (1 + |x| ^ β) := log_nonneg (by linarith [rpow_nonneg (abs_nonneg x) β])
  have hk (j : ℕ) : powerKernel p β α j x ≤ |x| ^ p := by
    unfold powerKernel
    have he : exp ((j : ℝ) * (-α * log (1 + |x| ^ β))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg j)
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) hlog)
    simpa using mul_le_mul_of_nonneg_left he (rpow_nonneg (abs_nonneg x) p)
  have hs : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)) = (2 : ℝ) ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  rw [prop_B3_sum]
  calc
    _ ≤ α⁻¹ ^ m * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * |x| ^ p := by
      gcongr with j hj
      exact hk j
    _ = (2 : ℝ) ^ m * α⁻¹ ^ m * |x| ^ p := by
      rw [← Finset.sum_mul, hs]
      ring

/-- Full two-sided relative approximation of Proposition B.3 for its explicit parts.
The Lévy membership of the damped kernels is a separate analytic assertion. -/
theorem prop_B3_error {p β ε : ℝ} {m n : ℕ} (hp : 0 < p) (hβ : 0 < β)
    (hm : 1 ≤ m) (hn : 2 ≤ n) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (x : ℝ) (hx : |x| ≤ n) :
    (1 - ε) * powerMoment p β m x ≤
        powerPositive p β (powerAlpha p β m n ε) m x -
          powerNegative p β (powerAlpha p β m n ε) m x ∧
    powerPositive p β (powerAlpha p β m n ε) m x -
        powerNegative p β (powerAlpha p β m n ε) m x ≤ powerMoment p β m x := by
  let α := powerAlpha p β m n ε
  have ha : 0 < α := powerAlpha_pos hp hβ hm hn hε
  by_cases hx0 : x = 0
  · subst x
    simp [powerMoment, prop_B3_difference, Real.zero_rpow hp.ne']
  have hr : 0 < |x| ^ p := rpow_pos_of_pos (abs_pos.mpr hx0) p
  have hL : 0 < log (1 + |x| ^ β) := log_pos (by linarith [rpow_pos_of_pos (abs_pos.mpr hx0) β])
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hN : 0 < log (1 + (n : ℝ) ^ β) := log_pos (by linarith [rpow_pos_of_pos hn' β])
  have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hlogle : log (1 + |x| ^ β) ≤ log (1 + (n : ℝ) ^ β) := by
    apply log_le_log (by positivity)
    exact add_le_add_left (rpow_le_rpow (abs_nonneg x) hx hβ.le) 1
  have haN : α * ((m : ℝ) * log (1 + (n : ℝ) ^ β)) ≤ 2 * ε := by
    have hα : α ≤ 2 * ε / ((m : ℝ) * log (1 + (n : ℝ) ^ β)) := min_le_left _ _
    exact (le_div_iff₀ (mul_pos hm' hN)).mp hα
  have hy : 0 < α * log (1 + |x| ^ β) := mul_pos ha hL
  have hmy : (m : ℝ) * (α * log (1 + |x| ^ β)) ≤ 2 * ε := by
    have := mul_le_mul_of_nonneg_left hlogle (mul_nonneg hm'.le ha.le)
    nlinarith
  have hbounds := eq_B5_power hm hε hε' hy hmy
  have heq : α⁻¹ ^ m * (1 - exp (-α * log (1 + |x| ^ β))) ^ m =
      (log (1 + |x| ^ β)) ^ m *
        ((1 - exp (-(α * log (1 + |x| ^ β)))) / (α * log (1 + |x| ^ β))) ^ m := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    field_simp
  have htarget : 0 ≤ |x| ^ p * (log (1 + |x| ^ β)) ^ m := by positivity
  rw [prop_B3_difference]
  change (1 - ε) * powerMoment p β m x ≤
      |x| ^ p * α⁻¹ ^ m * (1 - exp (-α * log (1 + |x| ^ β))) ^ m ∧
    |x| ^ p * α⁻¹ ^ m * (1 - exp (-α * log (1 + |x| ^ β))) ^ m ≤ powerMoment p β m x
  rw [mul_assoc, heq]
  constructor
  · have := mul_le_mul_of_nonneg_left hbounds.1 htarget
    simpa only [powerMoment, mul_assoc, mul_comm (1 - ε)] using this
  · have := mul_le_mul_of_nonneg_left hbounds.2 htarget
    simpa only [powerMoment, mul_one, mul_assoc] using this


/-- Explicit cancellation factor for Proposition B.3. -/
def powerCancellation (p β : ℝ) (m n : ℕ) (ε : ℝ) : ℝ :=
  (2 / log 2) ^ m * (powerAlpha p β m n ε)⁻¹ ^ m

/-- The cancellation envelope for every integer, including zero. -/
theorem prop_B3_integer_envelope {p β ε : ℝ} {m n : ℕ} (hp : 0 < p) (hβ : 0 < β)
    (hm : 1 ≤ m) (hn : 2 ≤ n) (hε : 0 < ε) (k : ℤ) :
    powerPositive p β (powerAlpha p β m n ε) m k +
        powerNegative p β (powerAlpha p β m n ε) m k ≤
      powerCancellation p β m n ε * powerMoment p β m k := by
  have ha := powerAlpha_pos hp hβ hm hn hε
  have h := prop_B3_sum_le (p := p) (β := β) ha.le m (k : ℝ)
  by_cases hk : k = 0
  · subst k
    simpa [powerMoment, Real.zero_rpow hp.ne'] using h
  have hk' : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hL : log 2 ≤ log (1 + |(k : ℝ)| ^ β) := by
    apply log_le_log (by norm_num)
    have := one_le_rpow hk' hβ.le
    linarith
  have h2 : 0 < log 2 := log_pos (by norm_num)
  have hpow := pow_le_pow_left₀ h2.le hL m
  have hcoeff : 0 ≤ (2 / log 2) ^ m * (powerAlpha p β m n ε)⁻¹ ^ m * |(k : ℝ)| ^ p := by
    positivity
  have hrew : (2 : ℝ) ^ m * (powerAlpha p β m n ε)⁻¹ ^ m * |(k : ℝ)| ^ p =
      ((2 / log 2) ^ m * (powerAlpha p β m n ε)⁻¹ ^ m * |(k : ℝ)| ^ p) * (log 2) ^ m := by
    rw [div_pow]
    field_simp
  unfold powerCancellation powerMoment
  calc
    _ ≤ (2 : ℝ) ^ m * (powerAlpha p β m n ε)⁻¹ ^ m * |(k : ℝ)| ^ p := h
    _ = _ := hrew
    _ ≤ ((2 / log 2) ^ m * (powerAlpha p β m n ε)⁻¹ ^ m * |(k : ℝ)| ^ p) *
        (log (1 + |(k : ℝ)| ^ β)) ^ m := mul_le_mul_of_nonneg_left hpow hcoeff
    _ = _ := by ring

/-- The relative-error and cancellation inequalities bundled in the actual split definition. -/
theorem prop_B3_admissibleSplit {p β ε : ℝ} {m n : ℕ} (hp : 0 < p) (hβ : 0 < β)
    (hm : 1 ≤ m) (hn : 2 ≤ n) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    AdmissibleSplit
      (RestrictInt (powerPositive p β (powerAlpha p β m n ε) m))
      (RestrictInt (powerNegative p β (powerAlpha p β m n ε) m))
      (fun k => powerMoment p β m k) n ε (powerCancellation p β m n ε) := by
  constructor
  · intro k hk
    have hk' : |(k : ℝ)| ≤ (n : ℝ) := by exact_mod_cast hk
    have h := prop_B3_error hp hβ hm hn hε hε' (k : ℝ) hk'
    change |powerPositive p β (powerAlpha p β m n ε) m k -
      powerNegative p β (powerAlpha p β m n ε) m k - powerMoment p β m k| ≤ _
    rw [abs_of_nonpos (by linarith [h.2])]
    nlinarith [h.1]
  · intro k _
    exact prop_B3_integer_envelope hp hβ hm hn hε k

/-- The analogous complete algebraic split statement for a single logarithm. -/
theorem prop_B2_admissibleSplit {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) :
    AdmissibleSplit
      (RestrictInt (singlePositive (singleAlpha n ε)))
      (RestrictInt (singleNegative (singleAlpha n ε)))
      (fun k => singleMoment k) n ε (log (1 + n) / (ε * log 2)) := by
  constructor
  · intro k hk
    have hk' : |(k : ℝ)| ≤ (n : ℝ) := by exact_mod_cast hk
    have h := prop_B2_error hn hε (k : ℝ) hk'
    change |singlePositive (singleAlpha n ε) k - singleNegative (singleAlpha n ε) k -
      singleMoment k| ≤ _
    rw [abs_of_nonpos (by linarith [h.2])]
    nlinarith [h.1]
  · intro k _
    exact prop_B2_integer_envelope hn hε k

/-- A uniform elementary bound on the logarithm occurring in `powerAlpha`. -/
lemma power_log_bound {β : ℝ} (hβ : β ≤ 2) {n : ℕ} (hn : 2 ≤ n) :
    log (1 + (n : ℝ) ^ β) ≤ 3 * log (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ β ≤ (n : ℝ) ^ (2 : ℝ) :=
    rpow_le_rpow_of_exponent_le (by linarith) hβ
  rw [rpow_two] at hpow
  have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hcube : 1 + (n : ℝ) ^ β ≤ (n : ℝ) ^ 3 := by nlinarith
  calc
    _ ≤ log ((n : ℝ) ^ 3) := log_le_log (by positivity) hcube
    _ = 3 * log (n : ℝ) := by rw [Real.log_pow]; norm_num

/-- An explicit inverse-parameter estimate, before absorbing the fixed additive term. -/
lemma powerAlpha_inv_le {p β ε : ℝ} {m n : ℕ} (hp : 0 < p) (hβ : 0 < β)
    (hβ' : β ≤ 2) (hm : 1 ≤ m) (hn : 2 ≤ n) (hε : 0 < ε) :
    (powerAlpha p β m n ε)⁻¹ ≤
      (3 * (m : ℝ) / 2) * (ε⁻¹ * log (n : ℝ)) + (m : ℝ) * β / p := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hL : 0 < log (1 + (n : ℝ) ^ β) :=
    log_pos (by linarith [rpow_pos_of_pos hn' β])
  have hlog := power_log_bound hβ' hn
  have hlogn : 0 < log (n : ℝ) := log_pos (by
    have hn'' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  unfold powerAlpha
  rcases le_total (2 * ε / ((m : ℝ) * log (1 + (n : ℝ) ^ β))) (p / ((m : ℝ) * β)) with h | h
  · rw [min_eq_left h, inv_div]
    have h1 : (m : ℝ) * log (1 + (n : ℝ) ^ β) / (2 * ε) ≤
        (3 * (m : ℝ) / 2) * (ε⁻¹ * log (n : ℝ)) := by
      have hx := mul_le_mul_of_nonneg_left hlog (div_nonneg hm'.le (show 0 ≤ 2 * ε by positivity))
      convert hx using 1 <;> field_simp
    have hconst : 0 ≤ (m : ℝ) * β / p := by positivity
    linarith
  · rw [min_eq_right h, inv_div]
    have hnn : 0 ≤ (3 * (m : ℝ) / 2) * (ε⁻¹ * log (n : ℝ)) := by positivity
    linarith

/-- A fixed constant depending only on `p,β,m` in the paper's big-O bound. -/
def powerCostConstant (p β : ℝ) (m : ℕ) : ℝ :=
  ((2 / log 2) * (3 * (m : ℝ) / 2 + (m : ℝ) * β / (p * log 2))) ^ m

/-- The stated `O_{p,β,m} ((ε⁻¹ log n)^m)` with a concrete uniform constant. -/
theorem prop_B3_cost_bound {p β ε : ℝ} {m n : ℕ} (hp : 0 < p) (hβ : 0 < β)
    (hβ' : β ≤ 2) (hm : 1 ≤ m) (hn : 2 ≤ n) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    powerCancellation p β m n ε ≤
      powerCostConstant p β m * (ε⁻¹ * log (n : ℝ)) ^ m := by
  have h2 : 0 < log 2 := log_pos (by norm_num)
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : log 2 ≤ log (n : ℝ) := log_le_log (by norm_num) hn'
  have he : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr (by linarith)
  have hX : log 2 ≤ ε⁻¹ * log (n : ℝ) := by
    have hx := mul_le_mul_of_nonneg_right he (h2.le.trans hlog)
    nlinarith
  have hc : 0 ≤ (m : ℝ) * β / (p * log 2) := by positivity
  have hadd : (m : ℝ) * β / p ≤
      ((m : ℝ) * β / (p * log 2)) * (ε⁻¹ * log (n : ℝ)) := by
    have hx := mul_le_mul_of_nonneg_left hX hc
    have heq : ((m : ℝ) * β / (p * log 2)) * log 2 = (m : ℝ) * β / p := by field_simp
    rwa [heq] at hx
  have hα := powerAlpha_inv_le hp hβ hβ' hm hn hε
  have hα' : (powerAlpha p β m n ε)⁻¹ ≤
      (3 * (m : ℝ) / 2 + (m : ℝ) * β / (p * log 2)) * (ε⁻¹ * log (n : ℝ)) := by
    nlinarith
  have ha : 0 ≤ (powerAlpha p β m n ε)⁻¹ := (inv_pos.mpr (powerAlpha_pos hp hβ hm hn hε)).le
  have hpw := pow_le_pow_left₀ ha hα' m
  unfold powerCancellation powerCostConstant
  have h := mul_le_mul_of_nonneg_left hpw (show 0 ≤ (2 / log 2) ^ m by positivity)
  simpa only [mul_pow, mul_assoc] using h

end Paper02.Bernstein

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-!
# Numerical identities of Paper 13

`15880 = 2^2 + 126^2`, `2048/1985 = 16384/15880 = 2^{14}/(2^2+126^2)`,
and the divergence/ratio estimates used in Theorem 1 and Corollary 2.
-/

namespace Paper13.Arith

/-- Local gadget ranks: `h = 7`, `d = 128`, `r = 2`. -/
def h : ℕ := 7
def d : ℕ := 128
def r : ℕ := 2

lemma h_eq : h = 7 := rfl
lemma d_eq : d = 128 := rfl
lemma r_eq : r = 2 := rfl

lemma d_pow : d = 2 ^ h := by
  norm_num [d, h]

lemma r_lt_d : r < d := by decide
lemma r_pos : 0 < r := by decide

/-- `A = r^2 + (d-r)^2 = 4 + 126^2 = 15880`. -/
def A : ℕ := r^2 + (d - r)^2

lemma A_eq : A = 15880 := by
  norm_num [A, r, d]

lemma A_eq' : 2^2 + 126^2 = 15880 := by norm_num

lemma d_sub_r : d - r = 126 := by decide

lemma d_sq : d^2 = 16384 := by decide

lemma d_pow_2k (k : ℕ) : d^(2*k) = 128^(2*k) := rfl

lemma A_pow (k : ℕ) : A^k = 15880^k := by rw [A_eq]

/-- `D = max r (d-r) = 126`. -/
def D : ℕ := max r (d - r)

lemma D_eq : D = 126 := by decide

lemma D_eq_d_sub_r : D = d - r := by decide

lemma A_eq_squares : A = r^2 + (d - r)^2 := rfl

/-- `d^2 / A = 16384 / 15880 = 2048 / 1985`. -/
lemma d_sq_div_A : (16384 : ℚ) / 15880 = 2048 / 1985 := by
  norm_num

lemma d_sq_div_A' : (d^2 : ℚ) / A = 2048 / 1985 := by
  norm_num [d, A, r]

lemma two_zero_four_eight : (2048 : ℚ) / 1985 = 16384 / 15880 := by
  norm_num

lemma A_lt_d_sq : A < d^2 := by
  rw [A_eq, d_sq]
  norm_num

lemma A_pos : 0 < A := by
  have hA : A = 15880 := A_eq
  rw [hA]
  norm_num

lemma fifteen_eighty_eighty : (15880 : ℕ) = 2^2 + 126^2 := by norm_num

/-- Over `ℤ`: `r^2 + (d-r)^2 = d^2 - 2 r (d-r)`. -/
lemma A_eq_d_sq_sub_int {r d : ℤ} :
    r^2 + (d - r)^2 = d^2 - 2 * r * (d - r) := by
  ring

/-- Over `ℕ` when `r ≤ d`: `r^2 + (d-r)^2 = d^2 - 2 r (d-r)`. -/
lemma A_eq_d_sq_sub (r d : ℕ) (hrd : r ≤ d) :
    r^2 + (d - r)^2 = d^2 - 2 * r * (d - r) := by
  have hsub : ((d - r : ℕ) : ℤ) = (d : ℤ) - r := Nat.cast_sub hrd
  have hcast : ((r^2 + (d - r)^2 : ℕ) : ℤ) = ((d^2 - 2 * r * (d - r) : ℕ) : ℤ) := by
    push_cast [hsub]
    have hle : 2 * r * (d - r) ≤ d^2 := by
      have hz : ((2 * r * (d - r) + r^2 + (d - r)^2 : ℕ) : ℤ) = (d : ℤ)^2 := by
        push_cast [hsub]
        ring
      have hz' : 2 * r * (d - r) + r^2 + (d - r)^2 = d^2 := by
        exact_mod_cast hz
      omega
    have h2 : ((d^2 - 2 * r * (d - r) : ℕ) : ℤ) = (d : ℤ)^2 - 2 * r * (d - r) := by
      push_cast [Nat.cast_sub hle, hsub]
      rfl
    rw [h2]
    exact A_eq_d_sq_sub_int
  exact_mod_cast hcast

/-- Ratio estimate of Theorem 1:
` (2048/1985)^k - 4/15880^k `. -/
def ratioBound (k : ℕ) : ℚ := (2048 / 1985)^k - 4 / 15880^k

lemma ratioBound_formula (k : ℕ) :
    ratioBound k = ((d^2 : ℚ) / A)^k - 4 / A^k := by
  unfold ratioBound
  have h1 : ((d^2 : ℚ) / A) = 2048 / 1985 := d_sq_div_A'
  have h2 : ((A : ℚ)) = 15880 := by rw [A_eq]; norm_num
  rw [h1, h2]

lemma ratioBound_eq (k : ℕ) :
    ratioBound k = (2048 / 1985 : ℚ)^k - 4 / 15880^k := rfl

/-- `ratioBound` diverges to `+∞`: for every rational bound `M`, eventually `M ≤ ratioBound`. -/
lemma ratioBound_tendsto_atTop :
    ∀ M : ℚ, ∃ k₀, ∀ k, k₀ ≤ k → M ≤ ratioBound k := by
  intro M
  have hbase : (2048 / 1985 : ℚ) = 1 + 63 / 1985 := by norm_num
  have hbern : ∀ k : ℕ, (1 + (63 / 1985 : ℚ))^k ≥ 1 + (k : ℚ) * (63 / 1985) :=
    fun k => one_add_mul_le_pow (by norm_num : (-2 : ℚ) ≤ 63 / 1985) k
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge ((M + 3) * 1985 / 63)
  refine ⟨k₀, fun k hk => ?_⟩
  have hlower : (2048 / 1985 : ℚ)^k ≥ 1 + (k : ℚ) * (63 / 1985) := by
    rw [hbase]
    exact_mod_cast hbern k
  have hneg : (4:ℚ) / 15880^k ≤ 4 :=
    div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
  have hgrow : (M + 3 : ℚ) ≤ (k : ℚ) * (63 / 1985) := by
    have hk0 : ((M + 3) * 1985 / 63 : ℚ) ≤ k₀ := by exact_mod_cast hk₀
    have hkk : (k₀ : ℚ) ≤ k := by exact_mod_cast hk
    have hcalc : ((M + 3) * 1985 / 63 : ℚ) ≤ k := le_trans hk0 hkk
    have h63 : (0:ℚ) < 63 := by norm_num
    have h1985 : (0:ℚ) < 1985 := by norm_num
    have hmul : (M + 3) * 1985 ≤ (k:ℚ) * 63 := by
      rwa [div_le_iff₀ h63] at hcalc
    have hrew : (k:ℚ) * (63 / 1985) = ((k:ℚ) * 63) / 1985 := by field_simp; try ring
    rw [hrew]
    rwa [le_div_iff₀ h1985]
  unfold ratioBound
  have hle : (1 + (k : ℚ) * (63 / 1985)) - 4 ≤ (2048 / 1985 : ℚ)^k - 4 / 15880^k := by
    have := hlower
    have := hneg
    linarith
  linarith

/-- Corollary 2 arithmetic identity:
`(128^k - 126^k)/2 = 2^{7k-1} * (1 - (63/64)^k)` over `ℚ`. -/
lemma cor2_main_ineq (k : ℕ) :
    ((128:ℚ)^k - 126^k) / 2 = 2^(7*k - 1) * (1 - (63/64 : ℚ)^k) := by
  rcases k with _ | k
  · norm_num
  · have h63 : (63:ℚ)/64 = (126:ℚ)/128 := by norm_num
    have hpow126 : (128:ℚ)^(k+1) * (126/128)^(k+1) = 126^(k+1) := by
      have h : (128:ℚ) * (126/128) = 126 := by field_simp
      rw [← mul_pow, h]
    have hsplit : ((128:ℚ)^(k+1) - 126^(k+1)) / 2
        = (128:ℚ)^(k+1) / 2 * (1 - (126/128)^(k+1)) := by
      have hmul : (128:ℚ)^(k+1) * (1 - (126/128)^(k+1)) = 128^(k+1) - 126^(k+1) := by
        rw [mul_sub, mul_one, hpow126]
      calc ((128:ℚ)^(k+1) - 126^(k+1)) / 2
          = ((128:ℚ)^(k+1) * (1 - (126/128)^(k+1))) / 2 := by rw [hmul]
        _ = (128:ℚ)^(k+1) / 2 * (1 - (126/128)^(k+1)) := by ring
    rw [hsplit, h63]
    have h2 : (128:ℚ)^(k+1) = 2^(7*(k+1)) := by
      have h128 : (128:ℚ) = 2^7 := by norm_num
      rw [h128, ← pow_mul]
    have hpow : (128:ℚ)^(k+1) / 2 = 2^(7*(k+1) - 1) := by
      rw [h2, show (7 * (k+1) : ℕ) = 7 * k + 7 from by ring]
      have hexp : (7 * k + 7 - 1 : ℕ) = 7 * k + 6 := by omega
      rw [hexp, pow_add, pow_add]
      field_simp
      try ring
    rw [hpow]

/-- Algebraic form of Corollary 2: `Δ/2^{7k-1} = 1 - (63/64)^k`. -/
lemma cor2_ratio_form (k : ℕ) :
    (((128:ℚ)^k - 126^k) / 2) / 2^(7*k - 1) = 1 - (63/64 : ℚ)^k := by
  rcases k with _ | k
  · norm_num
  · rw [cor2_main_ineq]
    have hpos : (2:ℚ)^(7*(k+1) - 1) ≠ 0 := by
      have : (7 * (k + 1) - 1 : ℕ) = 7 * k + 6 := by omega
      rw [this]
      positivity
    field_simp
    try ring

/-- Eventual `1 - ε` bound: `|(1-(63/64)^k) - 1| < ε` for all large `k`. -/
lemma cor2_ratio_limit :
    ∀ ε : ℚ, 0 < ε → ∃ k₀, ∀ k, k₀ ≤ k →
      |(1 - (63/64 : ℚ)^k : ℚ) - 1| < ε := by
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (63/64 : ℚ) < 1)
  refine ⟨k₀, fun k hk => ?_⟩
  have hmono : (63/64 : ℚ)^k ≤ (63/64)^k₀ :=
    pow_le_pow_of_le_one (by norm_num : (0:ℚ) ≤ 63/64) (by norm_num : (63/64:ℚ) ≤ 1)
      (by omega)
  have hpow : (63/64 : ℚ)^k < ε := lt_of_le_of_lt hmono hk₀
  have habs : |(1 - (63/64 : ℚ)^k : ℚ) - 1| = (63/64 : ℚ)^k := by
    rw [sub_sub_cancel_left, abs_neg]
    exact abs_of_nonneg (pow_nonneg (by norm_num) k)
  rw [habs]
  exact hpow

lemma one_minus_pow_le (k : ℕ) :
    (1 : ℚ) - (63/64)^k ≤ 1 ∧ 0 ≤ 1 - (63/64)^k := by
  constructor
  · have h : (0:ℚ) ≤ (63/64)^k := pow_nonneg (by norm_num) k
    linarith
  · have h : (63/64 : ℚ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith

/-- `∑_s C(k,s) r^{2s} (d-r)^{2(k-s)} = (r^2 + (d-r)^2)^k`, the binomial expansion of (25). -/
lemma binom_sum_A_pow {k r d : ℕ} :
    ∑ s ∈ Finset.range (k+1), (k.choose s : ℕ) * r^(2*s) * (d-r)^(2*(k-s))
      = (r^2 + (d-r)^2)^k := by
  have h := add_pow (r^2 : ℕ) ((d-r)^2) k
  rw [h]
  apply Finset.sum_congr rfl
  intro s hs
  have h1 : (r^2)^s = r^(2*s) := by
    rw [← pow_mul]
  have h2 : ((d-r)^2)^(k-s) = (d-r)^(2*(k-s)) := by
    rw [← pow_mul]
  rw [h1, h2]
  simp [mul_comm, mul_assoc]

lemma binom_A (k : ℕ) :
    (r^2 + (d - r)^2)^k = A^k := rfl

lemma A_div_half_form (k : ℕ) :
    (A : ℚ)^k / 2 = 15880^k / 2 := by
  rw [A_eq]
  rfl

lemma pow_two_eq (k : ℕ) : (2 : ℕ)^(7*k) = 128^k := by
  rw [pow_mul, show (2:ℕ)^7 = 128 from by norm_num]

/-- `dim g_nat = 2^{14k-1} - 2` written as `128^{2k}/2 - 2`. -/
lemma dim_nat_form (k : ℕ) :
    (2^(14*k - 1) : ℕ) - 2 = (128^(2*k) / 2) - 2 := by
  rcases k with _ | k
  · norm_num
  · have h : (128:ℕ)^(2*(k+1)) = 2^(14*(k+1)) := by
      have h2 : (128:ℕ) = 2^7 := by norm_num
      rw [h2, ← pow_mul]
      have hexp : (7 * (2 * (k+1)) : ℕ) = 14 * (k+1) := by ring
      rw [hexp]
    have h14 : (2^(14*(k+1)) : ℕ) / 2 = 2^(14*(k+1) - 1) := by
      have hadd : 14 * (k + 1) = 14 * k + 14 := by ring
      rw [hadd]
      have hexp : (14 * k + 14 - 1 : ℕ) = 14 * k + 13 := by omega
      rw [hexp]
      have hexp2 : (14 * k + 14 : ℕ) = 14 * k + 13 + 1 := by omega
      rw [hexp2, pow_succ]
      exact Nat.mul_div_cancel _ (by norm_num : (0:ℕ) < 2)
    rw [← h14, h]

/-- Dimension identity of Theorem 1:
`d^{2k}/2 - 2 = 2^{14k-1} - 2` for `d = 128`. -/
lemma dim_nat_form' (k : ℕ) :
    (128^(2*k) / 2) - 2 = (2^(14*k - 1) : ℕ) - 2 :=
  (dim_nat_form k).symm

/-- Paper inequality (25) specialized to the numeric ranks:
`∑_s C(k,s) 2^{2s} 126^{2(k-s)} = 15880^k`. -/
lemma binom_sum_paper (k : ℕ) :
    ∑ s ∈ Finset.range (k+1), (k.choose s : ℕ) * 2^(2*s) * 126^(2*(k-s))
      = 15880^k := by
  have h := binom_sum_A_pow (k := k) (r := 2) (d := 128)
  have hsub : (128 - 2 : ℕ) = 126 := by norm_num
  have hA : (2^2 + (128 - 2)^2 : ℕ) = 15880 := by norm_num
  rw [hsub, hA] at h
  exact h

/-- `m(G_k) ≤ D^k/2` arithmetic package: `D = 126`. -/
lemma m_bound_form (k : ℕ) :
    (D^k / 2 : ℕ) = 126^k / 2 := by
  rw [D_eq]

/-- Over `ℚ`, the gap identity of Corollary 2. -/
lemma delta_q_form (k : ℕ) :
    ((128^k - 126^k : ℚ) / 2) = 2^(7*k - 1) * (1 - (63/64 : ℚ)^k) :=
  cor2_main_ineq k

/-- `A < d^2` since `A = d^2 - 2 r (d-r)` and `0 < r < d`. -/
lemma A_lt_d_squared_nat (r d : ℕ) (hr : 0 < r) (hrd : r < d) :
    r^2 + (d-r)^2 < d^2 := by
  have hcast : ((r^2 + (d-r)^2 : ℕ) : ℤ) < (d^2 : ℕ) := by
    have hsub : ((d - r : ℕ) : ℤ) = (d : ℤ) - r := by omega
    have hr' : (0 : ℤ) < r := by exact_mod_cast hr
    have hrd' : (r : ℤ) < d := by exact_mod_cast hrd
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, hsub, Nat.cast_pow]
    nlinarith [sq_nonneg ((d : ℤ) - r - r)]
  exact_mod_cast hcast

lemma A_lt_d_squared_real {r d : ℝ} (hr : 0 < r) (hrd : r < d) :
    r^2 + (d - r)^2 < d^2 := by
  have hsub : 0 < d - r := by linarith
  have h : 0 < 2 * r * (d - r) := by positivity
  calc r^2 + (d - r)^2 = r^2 + (d^2 - 2 * d * r + r^2) := by ring
    _ = d^2 - 2 * r * (d - r) := by ring
    _ < d^2 := by linarith

/-- Special case of `A_lt_d_squared_real` with the paper numbers. -/
lemma A_lt_d_sq_real :
    ((2:ℝ)^2 + (128 - 2)^2) < 128^2 :=
  A_lt_d_squared_real (by norm_num) (by norm_num)

/-- Dimension bound form: `A^k / 2 - 1` is nonnegative. -/
lemma dim_bound_nonneg (k r d : ℕ) (hr : 0 < r) (_hrd : r < d) (_hk : 0 < k) :
    0 ≤ (r^2 + (d-r)^2)^k / 2 - 1 := by
  have hA : 0 < r^2 + (d-r)^2 := by positivity
  have hpow : 0 < (r^2 + (d-r)^2)^k := Nat.pow_pos hA
  omega

/-- Corollary 2 ratio form: `0 ≤ 1 - (63/64)^k ≤ 1`. -/
lemma cor2_ineq_real (k : ℕ) :
    (0:ℝ) ≤ 1 - (63/64)^k ∧ (1 - (63/64 : ℝ)^k) ≤ 1 := by
  constructor
  · have h : (63/64 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  · have h : (0:ℝ) ≤ (63/64)^k := pow_nonneg (by norm_num) k
    linarith

end Paper13.Arith

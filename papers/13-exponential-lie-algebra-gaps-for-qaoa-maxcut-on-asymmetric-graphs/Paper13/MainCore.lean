import Paper13.Basic
import Paper13.Arithmetic

noncomputable section
open scoped BigOperators
namespace Paper13


theorem arithmetic_ratio_lower_bound (k : ℕ) (hk : 7 ≤ k) :
    ((2^(14*k - 1) - 2 : ℕ) : ℚ) / (15880^k / 2 - 1)
      ≥ (2048 / 1985)^k - 4 / (15880 : ℚ)^k := by
  have hk1 : 1 ≤ k := by omega
  have hle2 : 2 ≤ 2^(14*k - 1) := by
    have hle : 2 ≤ 14*k - 1 := by
      have := Nat.mul_le_mul_left 14 hk
      omega
    have hexp : (2:ℕ)^(14*k-1) = 2^2 * 2^(14*k-1-2) := by
      have : 14*k-1 = 2 + (14*k-1-2) := by omega
      conv_lhs => rw [this, pow_add]
    rw [hexp]
    have hp : (1:ℕ) ≤ 2^(14*k-1-2) := one_le_pow₀ (by norm_num)
    nlinarith
  have hcast : ((2^(14*k - 1) - 2 : ℕ) : ℚ) = 2^(14*k - 1) - 2 := by
    rw [Nat.cast_sub hle2]
    push_cast
    rfl
  have h15880ge : (15880:ℚ) ≤ 15880^k := by
    have h : k = 1 + (k - 1) := by omega
    rw [h, pow_add, pow_one]
    have hp : (1:ℚ) ≤ 15880^(k-1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hApos : (0 : ℚ) < 15880^k / 2 - 1 := by
    have h2 : (15880:ℚ) / 2 = 7940 := by norm_num
    have h3 : (15880 : ℚ)^k / 2 ≥ 7940 := by
      have := div_le_div_of_nonneg_right h15880ge (by norm_num : (0:ℚ) ≤ 2)
      rwa [h2] at this
    linarith
  have hden_le : (15880^k / 2 - 1 : ℚ) ≤ 15880^k / 2 := by linarith
  have hnum_pos : (0 : ℚ) ≤ ((2^(14*k - 1) - 2 : ℕ) : ℚ) := by
    rw [hcast]
    have hexp : (2:ℚ)^(14*k-1) = 2^2 * 2^(14*k-1-2) := by
      have : 14*k-1 = 2 + (14*k-1-2) := by omega
      conv_lhs => rw [this, pow_add]
    have hp : (1:ℚ) ≤ 2^(14*k-1-2) := one_le_pow₀ (by norm_num)
    have : (2:ℚ)^(14*k-1) ≥ 2^2 := by
      rw [hexp]
      nlinarith
    norm_num at this
    linarith
  have hweaken : ((2^(14*k - 1) - 2 : ℕ) : ℚ) / (15880^k / 2 - 1)
      ≥ ((2^(14*k - 1) - 2 : ℕ) : ℚ) / (15880^k / 2) :=
    div_le_div_of_nonneg_left hnum_pos hApos hden_le
  have hkey : ((2^(14*k - 1) - 2 : ℕ) : ℚ) / (15880^k / 2)
      = (2048 / 1985)^k - 4 / (15880 : ℚ)^k := by
    rw [hcast]
    have h14 : (2 : ℚ)^14 = 16384 := by norm_num
    have h15880 : (16384 : ℚ) / 15880 = 2048 / 1985 := by norm_num
    have hpow : (2 : ℚ)^(14*k) = 16384^k := by
      rw [pow_mul, h14]
    have h2 : (2 : ℚ)^(14*k - 1) * 2 = 2^(14*k) := by
      have hle : 1 ≤ 14 * k := by
        have := Nat.mul_le_mul_left 14 hk
        omega
      have : 14 * k = (14*k - 1) + 1 := by omega
      conv_rhs => rw [this, pow_succ]
    have hnum : ((2 : ℚ)^(14*k - 1) - 2) * 2 = 2^(14*k) - 4 := by
      rw [sub_mul, h2]
      ring
    have hdiv : ((2 : ℚ)^(14*k - 1) - 2) / ((15880 : ℚ)^k / 2)
        = (2^(14*k) - 4) / 15880^k := by
      field_simp
      first
      | rw [mul_comm, hnum]
      | skip
    rw [hdiv, hpow]
    have hsplit : ((16384 : ℚ)^k - 4) / 15880^k
        = (16384^k / 15880^k) - 4 / 15880^k := by
      rw [← div_sub_div_same]
    rw [hsplit, ← div_pow, h15880]
  linarith

theorem geometric_lower_envelope_limit :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      |(1 - (63/64 : ℝ)^k) - 1| < ε := by
  intro ε hε
  have habs : ∀ k : ℕ, |(1 - (63/64 : ℝ)^k) - 1| = (63/64 : ℝ)^k := by
    intro k
    have hpow : (0 : ℝ) ≤ (63/64)^k := pow_nonneg (by norm_num) k
    have h : (1 - (63/64 : ℝ)^k) - 1 = -((63/64)^k) := by ring
    rw [h, abs_neg, abs_of_nonneg hpow]
  have htend : Filter.Tendsto (fun k : ℕ => (63/64 : ℝ)^k)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev0 : ∀ᶠ k in Filter.atTop, dist ((63/64 : ℝ)^k) 0 < ε :=
    Metric.tendsto_nhds.mp htend ε hε
  have hev : ∀ᶠ k in Filter.atTop, (63/64 : ℝ)^k < ε := by
    filter_upwards [hev0] with k hk
    have : dist ((63/64:ℝ)^k) 0 = (63/64)^k := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg (by norm_num) k)]
    linarith
  rw [Filter.eventually_atTop] at hev
  obtain ⟨k₀, hk₀⟩ := hev
  refine ⟨k₀, fun k hk => ?_⟩
  rw [habs]
  exact hk₀ k hk


theorem deficit_formula (k : ℕ) (hk : 7 ≤ k) :
    ((128:ℚ)^k - 126^k) / 2 = 2^(7*k - 1) * (1 - (63/64 : ℚ)^k) :=
  Arith.cor2_main_ineq k

end Paper13

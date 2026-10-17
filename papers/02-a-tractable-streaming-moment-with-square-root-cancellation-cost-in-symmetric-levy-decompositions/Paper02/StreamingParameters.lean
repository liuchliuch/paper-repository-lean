import Paper02.StreamingSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Concrete parameter choices and their inverse-accuracy/logarithmic bounds.
No probability guarantee or streaming conclusion is a field of these choices. -/
noncomputable section
namespace Paper02.StreamingParameters
open Paper02.StreamingSpace Paper02.WeightEval Real

def accuracyThreshold (ε : ℝ) : ℕ := ⌈65536 / ε ^ 2⌉₊
def medianHalf (δ : ℝ) : ℕ := ⌈4 * log (1 / δ)⌉₊

lemma accuracyThreshold_lower (ε : ℝ) :
    65536 / ε ^ 2 ≤ (accuracyThreshold ε : ℝ) := Nat.le_ceil _

lemma accuracyThreshold_ge_two {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2 ≤ accuracyThreshold ε := by
  have he : ε ^ 2 ≤ 1 := by nlinarith
  have hp : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hl : (65536 : ℝ) ≤ 65536 / ε ^ 2 := by
    rw [le_div_iff₀ hp]
    nlinarith
  have h := hl.trans (accuracyThreshold_lower ε)
  exact_mod_cast (by linarith : (2 : ℝ) ≤ accuracyThreshold ε)

lemma accuracyThreshold_upper {ε : ℝ} (hε : 0 < ε) :
    (accuracyThreshold ε : ℝ) < 65536 / ε ^ 2 + 1 :=
  Nat.ceil_lt_add_one (by positivity)

lemma accuracyThreshold_polynomial {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (accuracyThreshold ε : ℝ) ≤ 65537 * (ε⁻¹) ^ 2 := by
  have hi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hs : 1 ≤ (ε⁻¹) ^ 2 := by nlinarith
  have h := (accuracyThreshold_upper hε).le
  have heq : 65536 / ε ^ 2 = 65536 * (ε⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
  rw [heq] at h
  nlinarith

lemma median_repetitions_lower (δ : ℝ) :
    8 * log (1 / δ) ≤ ((2 * medianHalf δ + 1 : ℕ) : ℝ) := by
  have h := Nat.le_ceil (4 * log (1 / δ))
  change 4 * log (1 / δ) ≤ (medianHalf δ : ℝ) at h
  push_cast
  linarith

lemma log_inverse_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ log (1 / δ) := by
  apply log_nonneg
  rw [le_div_iff₀ hδ]
  simpa using hδ1

lemma median_repetitions_upper {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((2 * medianHalf δ + 1 : ℕ) : ℝ) < 8 * log (1 / δ) + 3 := by
  have h := Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    (log_inverse_nonneg hδ hδ1))
  change (medianHalf δ : ℝ) < 4 * log (1 / δ) + 1 at h
  push_cast
  linarith

/-- Binary-register bounds are also bounds in the natural logarithms appearing
in the paper's bit-space definition. -/
lemma registerBits_log_bound (n : ℕ) (hn : 1 ≤ n) :
    (registerBits (n + 1) : ℝ) ≤ 2 * log (2 * (n : ℝ)) + 1 := by
  have hpow : (2 : ℝ) ^ Nat.log 2 (n + 1) ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.pow_log_le_self 2 (show n + 1 ≠ 0 by omega)
  have hl := log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
  rw [log_pow] at hl
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : log ((n : ℝ) + 1) ≤ log (2 * (n : ℝ)) :=
    log_le_log (by positivity) (by linarith)
  have htwo := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  have he := Nat.cast_nonneg (α := ℝ) (Nat.log 2 (n + 1))
  unfold registerBits
  push_cast
  nlinarith

/-- Bertrand's prime gives the actual sampler's collision budget and the
logarithmic register bound, with the source's threshold constant 64. -/
theorem exists_parameters_prime (d U : ℕ) (hd : 1 ≤ d) (hU : 1 ≤ U) :
    ∃ q : ℕ, q.Prime ∧ d < q ∧ 2 * U < q ∧ q ≤ 2 * primeThreshold d U ∧
      ((levelCount d + 1 : ℕ) : ℝ) * ((d : ℝ) / q) < 1 / 64 ∧
      registerBits q ≤ 8 + 2 * registerBits (d + 1) + registerBits (U + 1) := by
  obtain ⟨q, hq, hlo, hup, hdq, hUq⟩ := exists_streaming_prime d U hd
  have hq0 : q ≠ 0 := by have := hq.two_le; omega
  refine ⟨q, hq, hdq, hUq, hup, ?_, prime_registerBits_bound d U q hq0 hup⟩
  have hbig : 64 * d * (levelCount d + 1) < q :=
    (Nat.le_max_right (2 * U) _).trans_lt hlo
  have hbigR : 64 * (d : ℝ) * ((levelCount d + 1 : ℕ) : ℝ) < q := by
    exact_mod_cast hbig
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq.pos
  rw [← mul_div_assoc, div_lt_iff₀ hqr]
  nlinarith

/-- The chosen prime's bit length is bounded by the natural logarithms of d,U. -/
theorem prime_bits_natural_log (d U q : ℕ) (hd : 1 ≤ d) (hU : 1 ≤ U)
    (hq0 : q ≠ 0) (hq : q ≤ 2 * primeThreshold d U) :
    (registerBits q : ℝ) ≤ 11 + 4 * log (2 * (d : ℝ)) + 2 * log (2 * (U : ℝ)) := by
  have h := prime_registerBits_bound d U q hq0 hq
  have hr : (registerBits q : ℝ) ≤
      8 + 2 * (registerBits (d + 1) : ℝ) + registerBits (U + 1) := by exact_mod_cast h
  nlinarith [registerBits_log_bound d hd, registerBits_log_bound U hU]

end Paper02.StreamingParameters

import Paper14.PrimitiveVoid
import Mathlib.Data.Nat.Cast.Order.Field

open MeasureTheory Filter Topology Set Finset
namespace Paper14
noncomputable section

lemma summable_SP_terms (P : ℕ) :
    Summable (fun ℓ : ℕ => if P < ℓ ∧ Nat.Prime ℓ then (ℓ : ℝ)⁻¹^2 else 0) := by
  apply Summable.of_nonneg_of_le (fun ℓ => by split_ifs <;> positivity) _ summable_invSq
  intro ℓ
  split_ifs
  · rw [inv_pow]
  · positivity

/-- The finite prime/divisor mean sum in the actual sieve remainder is
bounded by epsilon Q times the unsieved reciprocal-square prime tail. -/
theorem prime_mean_sum_le (P Q : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ ℓ ∈ Finset.range (Q+1), if P < ℓ ∧ Nat.Prime ℓ then
      ((Q/ℓ : ℕ) : ℝ)*(ε/(ℓ : ℝ)) else 0) ≤ ε*(Q : ℝ)*SP P := by
  have hfinite : (∑ ℓ ∈ Finset.range (Q+1), if P < ℓ ∧ Nat.Prime ℓ then
      ((Q/ℓ : ℕ) : ℝ)*(ε/(ℓ : ℝ)) else 0) ≤
      ε*(Q : ℝ)*∑ ℓ ∈ Finset.range (Q+1),
        if P < ℓ ∧ Nat.Prime ℓ then (ℓ : ℝ)⁻¹^2 else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ℓ hℓ
    by_cases hp : P < ℓ ∧ Nat.Prime ℓ
    · rw [if_pos hp,if_pos hp]
      calc _ ≤ ((Q : ℝ)/(ℓ : ℝ))*(ε/(ℓ : ℝ)) :=
            mul_le_mul_of_nonneg_right Nat.cast_div_le (div_nonneg hε (Nat.cast_nonneg _))
           _ = _ := by ring
    · simp [hp]
  apply hfinite.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hε (Nat.cast_nonneg _))
  exact (summable_SP_terms P).sum_le_tsum (Finset.range (Q+1)) (fun ℓ _ => by split_ifs <;> positivity)

end
end Paper14

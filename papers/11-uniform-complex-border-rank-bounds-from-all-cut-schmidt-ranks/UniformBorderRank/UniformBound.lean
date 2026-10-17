import UniformBorderRank.Comb

/-! The uniform numerical bound in Theorem 1.1 and Corollary 1.2. -/
namespace UniformBorderRank

/-- The bound of the paper, including its separate rank-one clause. -/
def Bhat (D : ℕ) : ℕ :=
  if D = 1 then 1 else D ^ (D ^ 2 + 2 * D - 3) * F (D ^ 2)

@[simp] theorem Bhat_zero : Bhat 0 = 1 := by norm_num [Bhat, F]
@[simp] theorem Bhat_one : Bhat 1 = 1 := by simp [Bhat]

theorem Bhat_of_two_le {D : ℕ} (hD : 2 ≤ D) :
    Bhat D = D ^ (D ^ 2 + 2 * D - 3) * F (D ^ 2) := by
  simp only [Bhat, if_neg (by omega : D ≠ 1)]

theorem Bhat_pos (D : ℕ) : 0 < Bhat D := by
  by_cases hD : D ≤ 1
  · interval_cases D <;> simp
  · have hD' : 2 ≤ D := by omega
    rw [Bhat_of_two_le hD']
    have hsq : 1 ≤ D ^ 2 := by nlinarith
    have hF : 1 ≤ F (D ^ 2) := by simpa using F_mono (x := 1) (y := D ^ 2) (by omega) hsq
    exact Nat.mul_pos (pow_pos (by omega) _) (by omega)

/-- The exponent in the paper increases with the allowed Schmidt rank. -/
theorem mainExponent_mono {D E : ℕ} (h : D ≤ E) :
    D ^ 2 + 2 * D - 3 ≤ E ^ 2 + 2 * E - 3 := by
  exact Nat.sub_le_sub_right (Nat.add_le_add (Nat.pow_le_pow_left h 2)
    (Nat.mul_le_mul_left 2 h)) 3

/-- The paper's bound is monotone, allowing replacement of the actual maximal
Schmidt rank by any larger all-cut rank bound. -/
theorem Bhat_mono : Monotone Bhat := by
  intro D E hDE
  by_cases hD : D ≤ 1
  · have heq : Bhat D = 1 := by interval_cases D <;> simp
    rw [heq]
    exact Bhat_pos E
  · have hD' : 2 ≤ D := by omega
    have hE' : 2 ≤ E := by omega
    rw [Bhat_of_two_le hD', Bhat_of_two_le hE']
    apply Nat.mul_le_mul
    · exact (Nat.pow_le_pow_left hDE _).trans
        (Nat.pow_le_pow_right (by omega) (mainExponent_mono hDE))
    · exact F_mono (by nlinarith) (Nat.pow_le_pow_left hDE 2)

end UniformBorderRank

import UniformBorderRank.UniformBound
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-! Explicit and asymptotic growth bounds for the numerical functions in
Section 5.2 of the paper. -/
noncomputable section
namespace UniformBorderRank
open Filter Asymptotics

/-- The elementary exponential estimate stated in Section 5.2. -/
theorem F_le_mul_four_pow {q : ℕ} (hq : 1 ≤ q) : F q ≤ q * 4 ^ (q - 1) := by
  by_cases hq1 : q = 1
  · subst q
    simp
  · have hq2 : 2 ≤ q := by omega
    rw [F_of_two_le hq2]
    have hp : 2 ^ (2 * q - 2) = 4 ^ (q - 1) := by
      rw [show 2 * q - 2 = 2 * (q - 1) by omega, pow_mul]
      rfl
    have h₁ := Nat.choose_le_two_pow (2 * q - 2) (q - 1)
    have h₂ := Nat.choose_le_two_pow (2 * q - 2) (q - 2)
    rw [hp] at h₁ h₂
    calc
      _ ≤ 4 ^ (q - 1) + (q - 1) * 4 ^ (q - 1) :=
        Nat.add_le_add h₁ (Nat.mul_le_mul_left _ h₂)
      _ = q * 4 ^ (q - 1) := by
        rw [← one_add_mul, Nat.add_sub_of_le hq]

/-- A concrete polynomial exponent dominates the full numerical bound. -/
theorem Bhat_le_pow {D : ℕ} (hD : 2 ≤ D) : Bhat D ≤ D ^ (5 * D ^ 2) := by
  have hD1 : 1 ≤ D := by omega
  have hq : 2 ≤ D ^ 2 := by nlinarith
  have hF : F (D ^ 2) ≤ D ^ (3 * D ^ 2) := by
    calc
      F (D ^ 2) ≤ D ^ 2 * 4 ^ (D ^ 2 - 1) := F_le_mul_four_pow (by omega)
      _ ≤ D ^ 2 * (D ^ 2) ^ (D ^ 2) := by
        apply Nat.mul_le_mul_left
        exact (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)).trans
          (Nat.pow_le_pow_left (by nlinarith : 4 ≤ D ^ 2) _)
      _ = D ^ (2 + 2 * D ^ 2) := by rw [← pow_mul, pow_add]
      _ ≤ D ^ (3 * D ^ 2) := Nat.pow_le_pow_right hD1 (by omega)
  have hexp : D ^ 2 + 2 * D - 3 ≤ 2 * D ^ 2 := by
    have h := Nat.sub_le (D ^ 2 + 2 * D) 3
    nlinarith
  rw [Bhat_of_two_le hD]
  calc
    _ ≤ D ^ (2 * D ^ 2) * D ^ (3 * D ^ 2) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right hD1 hexp) hF
    _ = D ^ (5 * D ^ 2) := by rw [← pow_add]; congr 1; omega

/-- An explicit exp(5 D² log D) upper bound, valid from D=2 onward. -/
theorem Bhat_le_exp {D : ℕ} (hD : 2 ≤ D) :
    (Bhat D : ℝ) ≤ Real.exp (5 * (D : ℝ) ^ 2 * Real.log D) := by
  have hpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have he : Real.exp (5 * (D : ℝ) ^ 2 * Real.log D) =
      (D : ℝ) ^ (5 * D ^ 2) := by
    rw [show (5 : ℝ) * (D : ℝ) ^ 2 * Real.log D =
      (5 * D ^ 2 : ℕ) * Real.log D by push_cast; ring,
      ← Real.log_pow, Real.exp_log (pow_pos hpos _)]
  rw [he]
  exact_mod_cast Bhat_le_pow hD

/-- Taking logarithms gives the explicit growth estimate used in the
asymptotic statement. -/
theorem log_Bhat_le {D : ℕ} (hD : 2 ≤ D) :
    Real.log (Bhat D : ℝ) ≤ 5 * (D : ℝ) ^ 2 * Real.log D := by
  have hp : (0 : ℝ) < Bhat D := by exact_mod_cast Bhat_pos D
  exact (Real.log_le_iff_le_exp hp).mpr (Bhat_le_exp hD)

/-- The precise formal meaning of Bhat(D)=exp(O(D² log D)). -/
theorem log_Bhat_isBigO :
    (fun D : ℕ => Real.log (Bhat D : ℝ)) =O[atTop]
      (fun D : ℕ => (D : ℝ) ^ 2 * Real.log D) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨5, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with D hD
  have hp : (1 : ℝ) ≤ Bhat D := by exact_mod_cast Bhat_pos D
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
  have hf : 0 ≤ Real.log (Bhat D : ℝ) := Real.log_nonneg hp
  have hg : 0 ≤ (D : ℝ) ^ 2 * Real.log D :=
    mul_nonneg (sq_nonneg _) (Real.log_nonneg hD1)
  simp only [Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg]
  simpa only [mul_assoc] using log_Bhat_le hD

end UniformBorderRank

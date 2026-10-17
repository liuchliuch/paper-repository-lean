import Paper28.CompactCurrentAlgebraInput
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! Native consequences of the ordinary current triangle inequality.
These estimates do not contain a transfer or a joint Jacobian premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {X : Type} {metricX : MetricSpace X}
  (I : CompactIntegralCurrentAlgebraInput.{0,0} X metricX)

theorem current_mass_finset_sum_le {V : Type*} {n : ℕ} (s : Finset V) (C : V → I.Current n) :
    I.mass (∑ v ∈ s, C v) ≤ ∑ v ∈ s, I.mass (C v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,I.mass_zero,le_refl]
  | @insert v s hv ih =>
    rw [Finset.sum_insert hv,Finset.sum_insert hv]
    exact (I.mass_add_le _ _).trans (add_le_add_left ih _)

theorem current_mass_nsmul_le {n : ℕ} (m : ℕ) (C : I.Current n) :
    I.mass (m • C) ≤ (m : ℝ)*I.mass C := by
  induction m with
  | zero => simp [I.mass_zero]
  | succ m ih =>
    rw [succ_nsmul]
    have h := (I.mass_add_le (m • C) C).trans (add_le_add_right ih _)
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using h

theorem current_mass_zsmul_le {n : ℕ} (m : ℤ) (C : I.Current n) :
    I.mass (m • C) ≤ |(m : ℝ)| * I.mass C := by
  cases m with
  | ofNat m => simpa using current_mass_nsmul_le I m C
  | negSucc m =>
    rw [Int.negSucc_coe,neg_smul,I.mass_neg,Int.cast_neg,Int.cast_natCast,abs_neg,
      abs_of_nonneg (Nat.cast_nonneg _),natCast_zsmul]
    exact current_mass_nsmul_le I (m+1) C

end Paper28

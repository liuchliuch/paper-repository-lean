import Paper20.YoungDifferential
import Paper20.YoungShapes
import Mathlib.Data.Matrix.Basic

namespace Paper20.YoungShapes
open Matrix Finset Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Actual single-box raising matrix between the complete finite levels. -/
def up (n : ℕ) : Matrix (Shape (n+1)) (Shape n) ℤ :=
  fun ν μ => if Covers μ.val ν.val then 1 else 0

def down (n : ℕ) : Matrix (Shape n) (Shape (n+1)) ℤ := (up n).transpose

def upperLevelEquiv {n : ℕ} (μ ν : Shape n) :
    {γ : Shape (n+1) // Covers μ.val γ.val ∧ Covers ν.val γ.val} ≃
      {γ : YoungDiagram // Covers μ.val γ ∧ Covers ν.val γ} where
  toFun γ := ⟨γ.val.val,γ.property⟩
  invFun γ := ⟨⟨γ.val,by simpa only [μ.property] using γ.property.1.2⟩,γ.property⟩
  left_inv γ := Subtype.ext (Subtype.ext rfl)
  right_inv γ := Subtype.ext rfl

def lowerLevelEquiv {n : ℕ} (μ ν : Shape (n+1)) :
    {κ : Shape n // Covers κ.val μ.val ∧ Covers κ.val ν.val} ≃
      {κ : YoungDiagram // Covers κ μ.val ∧ Covers κ ν.val} where
  toFun κ := ⟨κ.val.val,κ.property⟩
  invFun κ := ⟨⟨κ.val,by have := κ.property.1.2; have := μ.property; omega⟩,κ.property⟩
  left_inv κ := Subtype.ext (Subtype.ext rfl)
  right_inv κ := Subtype.ext rfl

lemma down_up_entry (n : ℕ) (μ ν : Shape n) :
    (down n*up n) μ ν=
      (Nat.card {γ : YoungDiagram // Covers μ.val γ ∧ Covers ν.val γ}:ℤ) := by
  rw [← Nat.card_congr (upperLevelEquiv μ ν),Nat.card_eq_fintype_card,
    Fintype.card_subtype,Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro γ hγ
  dsimp only [down,Matrix.transpose_apply,up]
  split_ifs <;> simp_all

lemma up_down_entry (n : ℕ) (μ ν : Shape (n+1)) :
    (up n*down n) μ ν=
      (Nat.card {κ : YoungDiagram // Covers κ μ.val ∧ Covers κ ν.val}:ℤ) := by
  rw [← Nat.card_congr (lowerLevelEquiv μ ν),Nat.card_eq_fintype_card,
    Fintype.card_subtype,Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro κ hκ
  dsimp only [down,Matrix.transpose_apply,up]
  split_ifs <;> simp_all

/-- The exact differential relation on the actual Young-lattice raising
and lowering matrices, derived from true common-cover cardinalities. -/
theorem down_up (n : ℕ) : down (n+1)*up (n+1)=up n*down n+1 := by
  apply Matrix.ext
  intro μ ν
  rw [Matrix.add_apply,down_up_entry,up_down_entry,Matrix.one_apply]
  have he := congrArg (fun a : ℕ => (a:ℤ))
    (young_differential_identity μ.val ν.val (by rw [μ.property,ν.property]))
  simp only [Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] at he
  have hi : μ.val=ν.val ↔ μ=ν := Subtype.ext_iff.symm
  simpa only [hi] using he

lemma down_up_zero : down 0*up 0=1 := by
  apply Matrix.ext
  intro μ ν
  have he : μ=ν := Subsingleton.elim ..
  subst ν
  rw [down_up_entry,Matrix.one_apply_eq]
  have hu := young_differential_identity μ.val μ.val rfl
  haveI : IsEmpty {κ : YoungDiagram // Covers κ μ.val ∧ Covers κ μ.val} := ⟨by
    intro κ
    have hc := κ.property.1.2
    rw [μ.property] at hc
    omega⟩
  simp only [Nat.card_of_isEmpty,if_pos rfl,Nat.zero_add] at hu
  exact_mod_cast hu

/-- The actual finite path vector from the unique empty diagram. -/
def vacuum : (n : ℕ) → Shape n → ℤ
  | 0 => fun _ => 1
  | n+1 => (up n).mulVec (vacuum n)

/-- Lowering the actual n+1-step path vector multiplies its predecessor
by n+1. This uses the proved differential identity, not a dimension-sum
or symmetric-group representation assumption. -/
theorem down_vacuum (n : ℕ) : (down n).mulVec (vacuum (n+1))=(n+1:ℤ) • vacuum n := by
  induction n with
  | zero =>
    change (down 0).mulVec ((up 0).mulVec (vacuum 0))=(1:ℤ) • vacuum 0
    rw [Matrix.mulVec_mulVec,down_up_zero,Matrix.one_mulVec,one_smul]
  | succ n ih =>
    change (down (n+1)).mulVec ((up (n+1)).mulVec (vacuum (n+1)))=_
    rw [Matrix.mulVec_mulVec,down_up,Matrix.add_mulVec,← Matrix.mulVec_mulVec,
      ih,Matrix.mulVec_smul,Matrix.one_mulVec]
    change (n+1:ℤ) • vacuum (n+1)+vacuum (n+1)=(n+1+1:ℤ) • vacuum (n+1)
    simp only [add_smul,one_smul]

end
end Paper20.YoungShapes

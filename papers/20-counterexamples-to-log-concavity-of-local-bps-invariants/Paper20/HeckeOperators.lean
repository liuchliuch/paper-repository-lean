import Paper20.BraidWalk

/-! Concrete standard-basis Hecke operators on permutations. The descent
test is the same one used by the actual admissible braid walks. -/
namespace Paper20.HeckeOperators
open Paper20.BraidWalk
noncomputable section
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

theorem adjacent_descent_flip {r : ℕ} (i : Fin (r-1)) (p : Equiv.Perm (Fin r)) :
    descent i (adjacentMove i p) ↔ ¬descent i p := by
  have hne : (p.symm (⟨i.val+1,by omega⟩:Fin r)).val ≠
      (p.symm (⟨i.val,by omega⟩:Fin r)).val := by
    intro he
    have hf : (⟨i.val+1,by omega⟩:Fin r) = (⟨i.val,by omega⟩:Fin r) :=
      p.symm.injective (Fin.ext he)
    have hv : i.val+1=i.val := congrArg Fin.val hf
    omega
  simp only [descent, adjacentMove, Equiv.Perm.mul_def, Equiv.symm_trans_apply]
  simp only [Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
  omega

section Generic
variable {S R : Type*} [CommRing R]

/-- The generator with a move of weight 1 and a descent-stay of weight z. -/
def operator (move : S → S) (desc : S → Prop) [DecidablePred desc]
    (z : R) (f : S → R) (s : S) : R :=
  f (move s)+(if desc s then z*f s else 0)

/-- The Hecke quadratic relation is derived from involution and the actual
descent flip, rather than imposed as an axiom on the walk model. -/
theorem operator_quadratic (move : S → S) (desc : S → Prop) [DecidablePred desc]
    (hinv : Function.Involutive move) (hflip : ∀ s, desc (move s) ↔ ¬desc s)
    (z : R) (f : S → R) (s : S) :
    operator move desc z (operator move desc z f) s =
      f s+z*operator move desc z f s := by
  by_cases h : desc s <;> simp [operator, hinv s, hflip s, h] <;> ring

def generatorMatrix (move : S → S) (desc : S → Prop) [DecidablePred desc]
    [DecidableEq S] (z : R) : Matrix S S R :=
  fun s t => (if t=move s then 1 else 0)+(if s=t ∧ desc s then z else 0)

/-- The standard-basis matrix is symmetric, including its descent weights. -/
theorem generatorMatrix_symmetric (move : S → S) (desc : S → Prop)
    [DecidablePred desc] [DecidableEq S] (hinv : Function.Involutive move) (z : R) :
    (generatorMatrix move desc z).transpose = generatorMatrix move desc z := by
  ext s t
  have hm : s=move t ↔ t=move s := by
    constructor
    · intro h; rw [h, hinv]
    · intro h; rw [h, hinv]
  by_cases hst : s=t
  · subst t; rfl
  · simp [generatorMatrix, Matrix.transpose_apply, hm, hst, Ne.symm hst]

end Generic

/-- The actual adjacent-permutation generators satisfy `T_i²=1+z T_i`. -/
theorem adjacent_quadratic {r : ℕ} {R : Type*} [CommRing R]
    (i : Fin (r-1)) (z : R) (f : Equiv.Perm (Fin r) → R) (p : Equiv.Perm (Fin r)) :
    operator (adjacentMove i) (descent i) z
      (operator (adjacentMove i) (descent i) z f) p =
      f p+z*operator (adjacentMove i) (descent i) z f p := by
  classical
  exact operator_quadratic _ _ (adjacentMove_involutive i) (adjacent_descent_flip i) z f p

end
end Paper20.HeckeOperators

import Paper20.HeckeInverseBasis

namespace Paper20.HeckeTraceAlgebra
open Polynomial Matrix Paper20.BraidWalk Paper20.HeckeOperators Paper20.HeckeMatrices
open Paper20.HeckeWalkExpansion Paper20.HalfTwistMatrix
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Right multiplication in the genuine permutation basis, obtained from
its proved inverse-permutation anti-involution. -/
theorem basisMatrix_mul_T (r : ℕ) (p : State r) (i : Fin (r-1)) :
    basisMatrix r p*T r i=basisMatrix r (rightMove i p)+
      (if rightDescent i p then (Polynomial.X:ℤ[X]) • basisMatrix r p else 0) := by
  have he := congrArg Matrix.transpose (T_mul_basisMatrix r i p.symm)
  simp only [Matrix.transpose_mul,Matrix.transpose_add,Matrix.transpose_smul,
    T_transpose,basisMatrix_transpose,Equiv.symm_symm,adjacentMove_symm] at he
  by_cases hd : rightDescent i p
  · have hd' : descent i p.symm := hd
    simpa only [hd,hd',↓reduceIte,Matrix.transpose_smul,basisMatrix_transpose,
      Equiv.symm_symm] using he
  · have hd' : ¬descent i p.symm := hd
    simpa only [hd,hd',↓reduceIte,Matrix.transpose_zero,add_zero] using he

lemma halfTwist_eq_longest_basis (r : ℕ) (hr : 1 ≤ r) :
    halfTwist r=basisMatrix r Fin.revPerm := by
  apply eq_of_identity_column r _ _ (halfTwist_mem r) (basisMatrix_mem r _)
  rw [halfTwist_delta r hr,basisMatrix_delta]

lemma longest_left_right (r : ℕ) (i : Fin (r-1)) :
    adjacentMove i Fin.revPerm=rightMove i.rev Fin.revPerm := by
  apply moves_eq_of_images
  apply Or.inr
  constructor <;> simp only [Fin.revPerm_apply,Fin.val_rev,Fin.val_mk] <;> omega

lemma longest_right_descent (r : ℕ) (i : Fin (r-1)) :
    rightDescent i Fin.revPerm := by
  rw [rightDescent_eq,Fin.revPerm_symm]
  exact reverse_descent i

/-- The actual longest-basis half twist conjugates adjacent generators by
reversal of their indices. This is derived from both basis rules, rather
than imposed as a braid-group relation. -/
theorem T_halfTwist (r : ℕ) (i : Fin (r-1)) :
    T r i*halfTwist r=halfTwist r*T r i.rev := by
  have hr : 1 ≤ r := by have := i.isLt; omega
  rw [halfTwist_eq_longest_basis r hr,T_mul_basisMatrix,basisMatrix_mul_T,
    if_pos (reverse_descent i),if_pos (longest_right_descent r i.rev),longest_left_right]

/-- The full twist commutes with every actual adjacent Hecke generator. -/
theorem fullTwist_commute_T (r : ℕ) (i : Fin (r-1)) : Commute (fullTwist r) (T r i) := by
  change fullTwist r*T r i=T r i*fullTwist r
  rw [fullTwist,pow_two]
  calc
    halfTwist r*halfTwist r*T r i = halfTwist r*(halfTwist r*T r i) := mul_assoc ..
    _ = halfTwist r*(T r i.rev*halfTwist r) := by
      rw [T_halfTwist r i.rev,Fin.rev_rev]
    _ = (halfTwist r*T r i.rev)*halfTwist r := (mul_assoc ..).symm
    _ = (T r i*halfTwist r)*halfTwist r := by rw [T_halfTwist]
    _ = T r i*(halfTwist r*halfTwist r) := mul_assoc ..

/-- Centrality holds on the entire genuine Hecke algebra, with no
character formula or centrality premise. -/
theorem fullTwist_central (r : ℕ) (A : Mat r) (hA : A ∈ algebra r) :
    Commute (fullTwist r) A := by
  induction hA using Algebra.adjoin_induction with
  | mem A hA => obtain ⟨i,rfl⟩ := hA; exact fullTwist_commute_T r i
  | algebraMap a => exact (Algebra.commutes a (fullTwist r)).symm
  | add A B hA hB ihA ihB => exact ihA.add_right ihB
  | mul A B hA hB ihA ihB => exact ihA.mul_right ihB

/-- The canonical full-twist element is central in the actual free
permutation-basis algebra. -/
theorem omega_central (r : ℕ) (A : algebra r) : Commute (omega r) A := by
  apply Subtype.ext
  exact (fullTwist_central r A.val A.property).eq

end
end Paper20.HeckeTraceAlgebra

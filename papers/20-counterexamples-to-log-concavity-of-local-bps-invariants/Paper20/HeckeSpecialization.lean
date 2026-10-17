import Paper20.HeckeFullTwistCenter

namespace Paper20.HeckeSpecialization
open Polynomial Matrix Paper20.HeckeTraceAlgebra Paper20.HeckeMatrices
open Paper20.HeckeOperators Paper20.BraidWalk Paper20.HeckeWalkExpansion
open Paper20.HalfTwistMatrix
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

section Regular
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The actual left regular permutation matrix over the integers. -/
def permutationMatrix (p : G) : Matrix G G ℤ := fun s t => if t=p⁻¹*s then 1 else 0

lemma permutationMatrix_mulVec (p : G) (f : G → ℤ) :
    (permutationMatrix p).mulVec f=fun s => f (p⁻¹*s) := by
  funext s
  simp [permutationMatrix,Matrix.mulVec,dotProduct,ite_mul]

@[simp] lemma permutationMatrix_one : permutationMatrix (1:G)=1 := by
  apply Matrix.ext
  intro s t
  simp [permutationMatrix,Matrix.one_apply,eq_comm]

lemma permutationMatrix_mul (p q : G) :
    permutationMatrix (p*q)=permutationMatrix p*permutationMatrix q := by
  apply matrix_eq_of_mulVec
  intro f
  rw [← Matrix.mulVec_mulVec,permutationMatrix_mulVec,permutationMatrix_mulVec,
    permutationMatrix_mulVec]
  funext s
  simp [_root_.mul_inv_rev,mul_assoc]

lemma permutationMatrix_delta (p : G) :
    (permutationMatrix p).mulVec (delta (1:G))=delta p := by
  rw [permutationMatrix_mulVec]
  funext s
  have he : p⁻¹*s=1 ↔ s=p := by simp only [inv_mul_eq_one,eq_comm]
  simp only [delta,he]
  split_ifs <;> rfl

end Regular

/-- Specializing the genuine Hecke parameter z to zero. -/
def specialize (r : ℕ) : Mat r →+* Matrix (State r) (State r) ℤ :=
  (Polynomial.evalRingHom (0:ℤ)).mapMatrix

lemma specialize_apply (r : ℕ) (A : Mat r) (s t : State r) :
    specialize r A s t=(A s t).coeff 0 := by simp [specialize,Polynomial.coeff_zero_eq_eval_zero]

lemma specialize_mulVec_delta (r : ℕ) (A : Mat r) (p : State r) :
    (specialize r A).mulVec (delta p)=fun s => (A.mulVec (delta p) s).coeff 0 := by
  funext s
  simp only [mulVec_delta,specialize_apply]

lemma specialize_T (r : ℕ) (i : Fin (r-1)) :
    specialize r (T r i)=permutationMatrix (adjacentMove i (1 : State r)) := by
  apply Matrix.ext
  intro s t
  simp only [specialize_apply,T,generatorMatrix,adjacentMove,mul_one,
    permutationMatrix,Equiv.swap_inv,Polynomial.coeff_add]
  split_ifs <;> simp

lemma specialize_word (r : ℕ) (w : List (Fin (r-1))) :
    specialize r (wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w)=
      permutationMatrix ((w.map (fun i => adjacentMove i (1 : State r))).prod) := by
  induction w with
  | nil => simp [wordMatrix]
  | cons i w ih =>
    rw [wordMatrix_cons,map_mul]
    change specialize r (T r i)*specialize r (wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w)=_
    rw [specialize_T,ih,List.map_cons,List.prod_cons,
      permutationMatrix_mul]

/-- Every actual Hecke basis matrix specializes to the corresponding
actual permutation matrix. No character or spectral formula is used. -/
theorem specialize_basis (r : ℕ) (p : State r) :
    specialize r (basisMatrix r p)=permutationMatrix p := by
  obtain ⟨w,hw⟩ := exists_basis_word r p
  have hM : wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w=basisMatrix r p := by
    apply eq_of_identity_column r _ _ (wordMatrix_mem r w) (basisMatrix_mem r p)
    rw [hw,basisMatrix_delta]
  have hc : (specialize r (wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w)).mulVec
      (delta (1 : State r))=delta p := by
    rw [specialize_mulVec_delta,hw]
    funext s
    by_cases hs : s=p <;> simp [delta,hs]
  rw [specialize_word,permutationMatrix_delta] at hc
  have he : ((w.map (fun i => adjacentMove i (1 : State r))).prod)=p := by
    have hs := congrFun hc p
    simp only [delta,ite_true] at hs
    split_ifs at hs with hp
    · exact hp.symm
    · norm_num at hs
  rw [← hM,specialize_word,he]

theorem specialize_halfTwist (r : ℕ) (hr : 1 ≤ r) :
    specialize r (halfTwist r)=permutationMatrix (Fin.revPerm : State r) := by
  rw [halfTwist_eq_longest_basis r hr,specialize_basis]

/-- The genuine full twist reduces to the identity in the ordinary
symmetric-group regular representation at z=0. -/
theorem specialize_fullTwist (r : ℕ) (hr : 1 ≤ r) : specialize r (fullTwist r)=1 := by
  rw [fullTwist,map_pow,specialize_halfTwist r hr,pow_two,← permutationMatrix_mul]
  have he : (Fin.revPerm : State r)*Fin.revPerm=1 := by
    apply Equiv.ext
    intro x
    simp only [Equiv.Perm.mul_apply,Fin.revPerm_apply,Fin.rev_rev,Equiv.Perm.one_apply]
  rw [he,permutationMatrix_one]

end
end Paper20.HeckeSpecialization

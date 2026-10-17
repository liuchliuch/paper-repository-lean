import Paper20.HeckeUnits

namespace Paper20.HeckeBar
open Polynomial Matrix Paper20.HeckeTraceAlgebra Paper20.HeckeMatrices
open Paper20.HeckeOperators Paper20.BraidWalk Paper20.HeckeWalkExpansion
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

def reversePositions {r : ℕ} (p : State r) : State r := p*Fin.revPerm

lemma longest_square (r : ℕ) : (Fin.revPerm : State r)*Fin.revPerm=1 := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply,Fin.revPerm_apply,Fin.rev_rev,Equiv.Perm.one_apply]

lemma reversePositions_involutive (r : ℕ) : Function.Involutive (@reversePositions r) := by
  intro p
  simp only [reversePositions,mul_assoc,longest_square,mul_one]

@[simp] lemma reversePositions_twice (r : ℕ) (p : State r) :
    reversePositions (reversePositions p)=p := reversePositions_involutive r p

lemma reversePositions_move (r : ℕ) (i : Fin (r-1)) (p : State r) :
    reversePositions (adjacentMove i p)=adjacentMove i (reversePositions p) := by
  simp only [reversePositions,adjacentMove,mul_assoc]

lemma reversePositions_descent (r : ℕ) (i : Fin (r-1)) (p : State r) :
    descent i (reversePositions p) ↔ ¬descent i p := by
  have he : (p*Fin.revPerm).symm=Fin.revPerm*p.symm := by
    change (p*Fin.revPerm)⁻¹=Fin.revPerm*p⁻¹
    rw [_root_.mul_inv_rev]
    rfl
  have hn : (p.symm (⟨i.val,by omega⟩:Fin r)).val ≠
      (p.symm (⟨i.val+1,by omega⟩:Fin r)).val := by
    intro hx
    have hfin := p.symm.injective (Fin.ext hx)
    have hv : i.val=i.val+1 := congrArg Fin.val hfin
    omega
  unfold descent reversePositions
  rw [he]
  simp only [Equiv.Perm.mul_apply,Fin.revPerm_apply,Fin.val_rev]
  have h0 := (p.symm (⟨i.val,by omega⟩:Fin r)).isLt
  have h1 := (p.symm (⟨i.val+1,by omega⟩:Fin r)).isLt
  omega

/-- The permutation matrix reversing all positions of every actual state. -/
def J (r : ℕ) : Mat r := fun s t => if t=reversePositions s then 1 else 0

lemma J_mulVec (r : ℕ) (f : State r → ℤ[X]) :
    (J r).mulVec f=fun p => f (reversePositions p) := by
  funext s
  simp [J,Matrix.mulVec,dotProduct,ite_mul]

lemma J_square (r : ℕ) : J r*J r=1 := by
  apply matrix_eq_of_mulVec
  intro f
  rw [← Matrix.mulVec_mulVec,J_mulVec,J_mulVec,Matrix.one_mulVec]
  funext s
  exact congrArg f (reversePositions_involutive r s)

/-- Parameter negation is an actual ring homomorphism on matrices. -/
def bar (r : ℕ) : Mat r →+* Mat r := (Polynomial.compRingHom (-X:ℤ[X])).mapMatrix

lemma bar_T (r : ℕ) (i : Fin (r-1)) :
    bar r (T r i)=generatorMatrix (adjacentMove i) (descent i) (-X:ℤ[X]) := by
  apply Matrix.ext
  intro s t
  change (T r i s t).comp (-X)=_
  simp only [T,generatorMatrix]
  split_ifs <;> simp

/-- Position reversal converts parameter negation into the genuine
inverse generator T_i-z, checked on the actual descent conditions. -/
theorem J_bar_T_J (r : ℕ) (i : Fin (r-1)) :
    J r*bar r (T r i)*J r=inverseGenerator r i := by
  apply matrix_eq_of_mulVec
  intro f
  funext p
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,J_mulVec,J_mulVec,bar_T,
    generator_mulVec]
  change operator (adjacentMove i) (descent i) (-X:ℤ[X])
    (fun p => f (reversePositions p)) (reversePositions p)=_
  rw [operator,← reversePositions_move,reversePositions_involutive,
    reversePositions_descent]
  rw [inverseGenerator,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    T,generator_mulVec]
  simp only [operator,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  by_cases hd : descent i p <;> simp [hd] <;> ring

end
end Paper20.HeckeBar

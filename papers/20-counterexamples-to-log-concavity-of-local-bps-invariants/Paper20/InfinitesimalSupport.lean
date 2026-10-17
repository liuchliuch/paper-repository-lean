import Paper20.OneStayTransposition

namespace Paper20.HeckeTraceAlgebra
open Polynomial Matrix Paper20.HeckeOperators Paper20.HeckeMatrices
open Paper20.HeckeWalkExpansion Paper20.BraidWalk Paper20.HalfTwistMatrix
open Paper20.OneStayTransposition Paper20.HeckeParameterPolynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma fullTwist_palindrome (r : ℕ) :
    fullTwist r=wordMatrix adjacentMove descent (Polynomial.X:ℤ[X])
      (deltaWord (r-1)++(deltaWord (r-1)).reverse) := by
  rw [wordMatrix_append,wordMatrix_reverse adjacentMove descent adjacentMove_involutive]
  change (halfTwist r)^2=halfTwist r*(halfTwist r).transpose
  rw [halfTwist_transpose,pow_two]

/-- First-order coefficients of the actual full twist are supported on
actual transpositions. A single omitted adjacent move in a palindrome is
proved to be a conjugate transposition, before admissibility is used. -/
theorem infinitesimal_support (r : ℕ) (p : State r) (hp : ¬p.IsSwap) :
    infinitesimalFullTwist r p 1=0 := by
  rw [infinitesimalFullTwist,fullTwist_palindrome]
  rw [← mulVec_delta (wordMatrix adjacentMove descent (Polynomial.X:ℤ[X])
      (deltaWord (r-1)++(deltaWord (r-1)).reverse)) (1:State r) p,
    wordMatrix_mulVec,wordAction_eq_sum,finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro w hw
  let word := deltaWord (r-1)++(deltaWord (r-1)).reverse
  have hfst : (word.zip (List.ofFn w)).map Prod.fst=word := by
    rw [List.map_fst_zip]
    simp [word]
  have hsnd : (word.zip (List.ofFn w)).map Prod.snd=List.ofFn w := by
    rw [List.map_snd_zip]
    simp [word]
  by_cases hn : Walks.nStays w=1
  · have hne : endpoint adjacentMove (word.zip (List.ofFn w)) p ≠ 1 := by
      intro he
      apply hp
      apply one_stay_endpoint (deltaWord (r-1)) _ hfst p he
      rw [hsnd,nStays_ofFn]
      exact hn
    dsimp only [word] at hne
    simp only [term,delta]
    split_ifs <;> simp_all only [mul_zero,mul_one,coeff_zero]
  · simp only [term,delta]
    split_ifs <;> simp [Polynomial.coeff_X_pow,Ne.symm hn]

lemma basisMatrix_swapAt (r : ℕ) (i : Fin (r-1)) : basisMatrix r (swapAt i)=T r i := by
  have hd : ¬descent i (1:State r) := by
    change ¬(i.val+1 < i.val)
    omega
  have he := T_mul_basisMatrix r i 1
  rw [basisMatrix_one,mul_one,if_neg hd,add_zero] at he
  exact he.symm

lemma swapAt_ne_one (r : ℕ) (i : Fin (r-1)) : swapAt i ≠ (1:State r) := by
  obtain ⟨a,b,hab,he⟩ := swapAt_isSwap i
  intro h
  rw [h] at he
  have hx := congrArg (fun p : State r => p a) he
  simp only [Equiv.Perm.one_apply,Equiv.swap_apply_left] at hx
  exact hab hx

lemma adjacent_longest_ne (r : ℕ) (i : Fin (r-1)) :
    adjacentMove i Fin.revPerm ≠ (Fin.revPerm:State r) := by
  intro he
  have hx : swapAt i*Fin.revPerm=1*Fin.revPerm := by simpa [swapAt,adjacentMove] using he
  exact swapAt_ne_one r i (mul_right_cancel hx)

/-- The full-twist coordinate at each actual simple transposition is
exactly z, from the genuine inverse dual basis and trace normalization. -/
theorem fullTwist_simple_coordinate (r : ℕ) (i : Fin (r-1)) :
    fullTwist r (swapAt i) 1=(Polynomial.X:ℤ[X]) := by
  have hr : 1 ≤ r := by have := i.isLt; omega
  have hT : T r i ∈ algebra r := Algebra.subset_adjoin (Set.mem_range_self i)
  have he : trace r (T r i*fullTwist r)=Polynomial.X := by
    rw [fullTwist,pow_two,← mul_assoc,halfTwist_eq_longest_basis r hr,
      T_mul_basisMatrix,if_pos (reverse_descent i),add_mul,trace_add]
    have hdual := trace_basis_inverse r (adjacentMove i Fin.revPerm) Fin.revPerm
    rw [Fin.revPerm_symm,if_neg (adjacent_longest_ne r i)] at hdual
    rw [hdual,zero_add,Matrix.smul_mul]
    change (Polynomial.X:ℤ[X])*trace r
      (basisMatrix r Fin.revPerm*basisMatrix r Fin.revPerm)=Polynomial.X
    have ht := canonicalTrace_omega_one r hr
    change trace r (fullTwist r)=1 at ht
    rw [← halfTwist_eq_longest_basis r hr,← pow_two,← fullTwist,ht,mul_one]
  have ht : (basisMatrix r (swapAt i)).transpose=basisMatrix r (swapAt i) := by
    rw [basisMatrix_swapAt,T_transpose]
  rw [← basisMatrix_swapAt r i] at he
  rw [← ht,trace_basisTranspose_mul] at he
  exact he

theorem infinitesimal_simple_coordinate (r : ℕ) (i : Fin (r-1)) :
    infinitesimalFullTwist r (swapAt i) 1=1 := by
  rw [infinitesimalFullTwist,fullTwist_simple_coordinate,coeff_X_one]

end
end Paper20.HeckeTraceAlgebra

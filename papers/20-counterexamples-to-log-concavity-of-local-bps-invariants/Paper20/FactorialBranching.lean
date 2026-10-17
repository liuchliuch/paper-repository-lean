import Paper20.HookDeterminant

namespace Paper20.HookDeterminant
open Polynomial Matrix Finset
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

section Determinant
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

lemma det_updateRow_weight (A : Matrix I I R) (i : I) (c : I → R) :
    (A.updateRow i (fun j => c j*A i j)).det=
      ∑ σ : Equiv.Perm I, (Equiv.Perm.sign σ:ℤ) •
        (c (σ.symm i)*∏ j, A (σ j) j) := by
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  have he : (∏ j, (A.updateRow i (fun j => c j*A i j)) (σ j) j)=
      ∏ j, (if σ j=i then c j else 1)*A (σ j) j := by
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hs : σ j=i <;> simp [Matrix.updateRow_apply,hs]
  rw [he,Finset.prod_mul_distrib]
  congr 1
  have hi (j : I) : σ j=i ↔ j=σ.symm i := by
    constructor
    · intro h; exact (σ.apply_eq_iff_eq_symm_apply).1 h
    · intro h; rw [h,σ.apply_symm_apply]
  simp only [hi,Finset.prod_ite_eq',mem_univ,ite_true]

/-- Exact determinant derivative under independent row and column
weights. This is an algebraic identity over any commutative ring. -/
theorem det_weighted_row_sum (A : Matrix I I R) (b d : I → R) :
    (∑ i, (A.updateRow i (fun j => (b i-d j)*A i j)).det)=
      ((∑ i, b i)-(∑ i, d i))*A.det := by
  simp_rw [det_updateRow_weight]
  rw [Finset.sum_comm,Matrix.det_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hsum : (∑ i, (b i-d (σ.symm i)))=(∑ i, b i)-(∑ i, d i) := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp σ.symm d]
  rw [← smul_sum,← Finset.sum_mul,hsum]
  simp only [Units.smul_def,zsmul_eq_mul]
  ring

end Determinant

def lowerFactorialRow {m : ℕ} (b d : Fin m → ℕ) (i j : Fin m) : ℚ :=
  if d j+1 ≤ b i then 1/((b i-d j-1).factorial:ℚ) else 0

lemma lowerFactorialRow_eq {m : ℕ} (b d : Fin m → ℕ) (i j : Fin m) :
    lowerFactorialRow b d i j=((b i:ℚ)-(d j:ℚ))*factorialMatrix b d i j := by
  unfold lowerFactorialRow factorialMatrix
  by_cases hd : d j+1 ≤ b i
  · rw [if_pos hd,if_pos (by omega : d j ≤ b i)]
    have hn : b i-d j=(b i-d j-1)+1 := by omega
    have hf := Nat.factorial_succ (b i-d j-1)
    rw [← hn] at hf
    have hdiff : (b i:ℚ)-(d j:ℚ)=((b i-d j:ℕ):ℚ) := (Nat.cast_sub (by omega)).symm
    rw [hdiff,hf]
    push_cast
    have hp : ((b i-d j-1).factorial:ℚ) ≠ 0 := by positivity
    have hn' : ((b i-d j:ℕ):ℚ) ≠ 0 := by exact_mod_cast (by omega : b i-d j ≠ 0)
    field_simp
  · rw [if_neg hd]
    by_cases he : d j ≤ b i
    · have hb : b i=d j := by omega
      rw [if_pos he,hb,sub_self,zero_mul]
    · rw [if_neg he,mul_zero]

/-- The exact branching recurrence for the factorial determinant of
actual beta data. Invalid lowerings vanish automatically through its
zero convention; no tableau dimension formula is assumed. -/
theorem factorial_det_branching {m n : ℕ} (b d : Fin m → ℕ)
    (hs : ∑ i, b i=n+∑ i, d i) :
    (∑ i, ((factorialMatrix b d).updateRow i (lowerFactorialRow b d i)).det)=
      (n:ℚ)*(factorialMatrix b d).det := by
  have he (i : Fin m) : lowerFactorialRow b d i=
      (fun j => ((b i:ℚ)-(d j:ℚ))*factorialMatrix b d i j) := by
    funext j
    exact lowerFactorialRow_eq b d i j
  simp_rw [he]
  rw [det_weighted_row_sum]
  have hq := congrArg (fun x : ℕ => (x:ℚ)) hs
  simp only [Nat.cast_sum,Nat.cast_add] at hq
  rw [hq]
  ring

end
end Paper20.HookDeterminant

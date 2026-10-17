import Paper20.HookVandermonde
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Nat.Choose.Multinomial

namespace Paper20.HookDeterminant
open Polynomial Matrix Finset
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Reciprocal factorial entries, with the actual zero convention for
negative factorial indices. -/
def factorialMatrix {m : ℕ} (b d : Fin m → ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  fun i j => if d j ≤ b i then 1/((b i-d j).factorial:ℚ) else 0

lemma sum_sub_permutation {m n : ℕ} (b d : Fin m → ℕ)
    (hs : ∑ i, b i=n+∑ i, d i) (σ : Equiv.Perm (Fin m))
    (hle : ∀ i, d i ≤ b (σ i)) : ∑ i, (b (σ i)-d i)=n := by
  have he : (∑ i, (b (σ i)-d i))+(∑ i, d i)=∑ i, b i := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i, b (σ i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Nat.sub_add_cancel (hle i)
      _ = ∑ i, b i := Equiv.sum_comp σ b
  omega

lemma factorial_term_integral {m n : ℕ} (b d : Fin m → ℕ)
    (hs : ∑ i, b i=n+∑ i, d i) (σ : Equiv.Perm (Fin m)) :
    ∃ z : ℤ, (z:ℚ)=(n.factorial:ℚ)*∏ i, factorialMatrix b d (σ i) i := by
  classical
  by_cases hle : ∀ i, d i ≤ b (σ i)
  · let a : Fin m → ℕ := fun i => b (σ i)-d i
    refine ⟨(Nat.multinomial univ a:ℤ),?_⟩
    have hsum : ∑ i, a i=n := sum_sub_permutation b d hs σ hle
    have he := congrArg (fun x : ℕ => (x:ℚ)) (Nat.multinomial_spec univ a)
    rw [hsum] at he
    simp only [Nat.cast_mul,Nat.cast_prod] at he
    simp only [Int.cast_natCast,factorialMatrix,hle,↓reduceIte]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const_one,one_div]
    have hn : (∏ i, (a i).factorial:ℚ) ≠ 0 := by positivity
    apply (eq_div_iff hn).2
    simpa only [mul_comm,a] using he
  · push_neg at hle
    obtain ⟨i,hi⟩ := hle
    refine ⟨0,?_⟩
    have hz : (∏ j, factorialMatrix b d (σ j) j)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [factorialMatrix,if_neg (by omega : ¬d i ≤ b (σ i))]
    rw [hz,mul_zero,Int.cast_zero]

/-- The factorial-scaled determinant is an actual integer for every
nonnegative shifted-factorial matrix with the correct total index.
This follows from finite multinomial coefficients term by term. -/
theorem factorial_det_integral {m n : ℕ} (b d : Fin m → ℕ)
    (hs : ∑ i, b i=n+∑ i, d i) :
    ∃ z : ℤ, (z:ℚ)=(n.factorial:ℚ)*(factorialMatrix b d).det := by
  classical
  choose z hz using factorial_term_integral b d hs
  refine ⟨∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ:ℤ)*z σ,?_⟩
  rw [Int.cast_sum,Matrix.det_apply',Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Int.cast_mul,hz]
  ring

/-- Clearing each row factorial produces the ordinary falling-factorial
matrix. This connects the integral determinant to the actual beta-number
Vandermonde without assuming hook divisibility. -/
theorem factorialMatrix_descFactorial {m : ℕ} (b d : Fin m → ℕ) :
    (fun i j => (b i).factorial * factorialMatrix b d i j : Matrix (Fin m) (Fin m) ℚ)=
      fun i j => ((b i).descFactorial (d j):ℚ) := by
  apply Matrix.ext
  intro i j
  by_cases hle : d j ≤ b i
  · rw [factorialMatrix,if_pos hle]
    have he := congrArg (fun a : ℕ => (a:ℚ)) (Nat.factorial_mul_descFactorial hle)
    simp only [Nat.cast_mul] at he
    have hn : ((b i-d j).factorial:ℚ) ≠ 0 := by positivity
    field_simp
    nlinarith [he]
  · rw [factorialMatrix,if_neg hle,mul_zero,Nat.descFactorial_eq_zero_iff_lt.mpr (by omega),
      Nat.cast_zero]

end
end Paper20.HookDeterminant

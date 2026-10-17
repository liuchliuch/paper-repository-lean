import Paper20.PaddedHookVandermonde

namespace Paper20.HookDeterminant
open Polynomial Matrix Finset Paper20.HookBeta
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def orientation (m : ℕ) : ℤ := ∏ i : Fin m, (-1:ℤ)^((Ioi i).card)

lemma orientation_sq (m : ℕ) : orientation m*orientation m=1 := by
  rw [orientation,← Finset.prod_mul_distrib]
  have he (i : Fin m) : (-1:ℤ)^((Ioi i).card)*(-1:ℤ)^((Ioi i).card)=1 := by
    rw [← pow_add,← two_mul,pow_mul]
    simp
  simp_rw [he]
  exact Finset.prod_const_one

lemma pairProduct_ne_zero {m : ℕ} (b : Fin m → ℕ)
    (hb : ∀ i j, i<j → b j<b i) : pairProduct b ≠ 0 := by
  unfold pairProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  by_cases hij : i<j
  · rw [if_pos hij]
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt (hb i j hij))
  · rw [if_neg hij]
    exact one_ne_zero

lemma determinant_orientation {m : ℕ} (b : Fin m → ℕ)
    (hb : ∀ i j, i<j → b j<b i) :
    (Matrix.vandermonde (fun i => (b i:ℤ))).det=orientation m*(pairProduct b:ℤ) := by
  rw [Matrix.det_vandermonde,orientation,pairProduct_Ioi,Nat.cast_prod,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Nat.cast_prod,← Finset.prod_const,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Nat.cast_sub (hb i j (mem_Ioi.mp hj)).le]
  ring

lemma factorialMatrix_vandermonde {m : ℕ} (b : Fin m → ℕ) :
    ((∏ i, (b i).factorial:ℕ):ℚ)*(factorialMatrix b (fun j => j.val)).det=
      (((Matrix.vandermonde (fun i => (b i:ℤ))).det:ℤ):ℚ) := by
  have he := Matrix.det_mul_column (fun i => ((b i).factorial:ℚ))
    (factorialMatrix b (fun j => j.val))
  rw [factorialMatrix_descFactorial] at he
  have hv := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun i => (b i:ℚ)) (fun j : Fin m => descPochhammer ℚ j.val)
    (fun j => descPochhammer_natDegree ℚ j.val)
    (fun j => monic_descPochhammer ℚ j.val)
  simp only [descPochhammer_eval_eq_descFactorial] at hv
  rw [← hv] at he
  have hc : (((Matrix.vandermonde (fun i => (b i:ℤ))).det:ℤ):ℚ)=
      (Matrix.vandermonde (fun i => (b i:ℚ))).det := by
    rw [Int.cast_det]
    congr 1
    apply Matrix.ext
    intro i j
    simp [Matrix.vandermonde,Matrix.map_apply]
  simpa only [Nat.cast_prod] using he.symm.trans hc.symm

lemma dimension_det_of_product {m n H f : ℕ} (b : Fin m → ℕ)
    (hb : ∀ i j, i<j → b j<b i)
    (hprod : H*pairProduct b=∏ i, (b i).factorial) (hdim : f*H=n.factorial) :
    (f:ℚ)=(orientation m:ℚ)*(n.factorial:ℚ)*(factorialMatrix b (fun j => j.val)).det := by
  have hH : H ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hdim
    exact Nat.factorial_ne_zero n hdim.symm
  have hD := pairProduct_ne_zero b hb
  have hc := factorialMatrix_vandermonde b
  have hd := congrArg (fun a : ℕ => (a:ℚ)) hdim
  simp only [Nat.cast_mul] at hd
  have hs := congrArg (fun a : ℤ => (a:ℚ)) (orientation_sq m)
  simp only [Int.cast_mul,Int.cast_one] at hs
  have hp : (H:ℚ)*(pairProduct b:ℚ)*(factorialMatrix b (fun j => j.val)).det=
      (orientation m:ℚ)*(pairProduct b:ℚ) := by
    rw [← Nat.cast_mul,hprod,hc,determinant_orientation b hb,Int.cast_mul,Int.cast_natCast]
  apply mul_left_cancel₀ (by exact_mod_cast hH : (H:ℚ) ≠ 0)
  apply mul_left_cancel₀ (by exact_mod_cast hD : (pairProduct b:ℚ) ≠ 0)
  linear_combination (norm := ring_nf)
    (pairProduct b:ℚ)*hd-(orientation m:ℚ)*(n.factorial:ℚ)*hp-
      (pairProduct b:ℚ)*(n.factorial:ℚ)*hs

lemma paddedBeta_strict (μ : YoungDiagram) (m : ℕ) (i j : Fin m) (hij : i<j) :
    paddedBeta μ m j < paddedBeta μ m i := by
  have hr := μ.rowLen_anti i.val j.val hij.le
  have hi := i.isLt
  have hj := j.isLt
  dsimp only [paddedBeta]
  omega

/-- The same actual natural hook quotient has a precise factorial
determinant formula at every fixed padded row bound. The orientation is
constant across a one-box branching calculation. -/
theorem padded_dim_det {n : ℕ} (p : Part n) (m : ℕ) (hm : p.diagram.colLen 0 ≤ m) :
    (dimOf n p.parts:ℚ)=(orientation m:ℚ)*(n.factorial:ℚ)*
      (factorialMatrix (paddedBeta p.diagram m) (fun j => j.val)).det := by
  apply dimension_det_of_product (H:=(hooksOf p.parts).prod) (paddedBeta p.diagram m)
    (paddedBeta_strict p.diagram m)
  · rw [actual_hook_product]
    exact padded_hook_factor p.diagram m hm
  · exact actual_dim_mul_hooks p

end
end Paper20.HookDeterminant

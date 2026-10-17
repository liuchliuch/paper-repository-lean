import Paper20.HookDeterminant

namespace Paper20.HookDeterminant
open Polynomial Matrix Finset Paper20.HookBeta
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev rows (μ : YoungDiagram) := Fin (μ.colLen 0)
def betaVector (μ : YoungDiagram) (i : rows μ) : ℕ := beta μ i.val

def betaDelta (μ : YoungDiagram) : ℕ :=
  ∏ i : rows μ, ∏ j ∈ Ioi i, (betaVector μ i-betaVector μ j)

def betaDet (μ : YoungDiagram) : ℤ :=
  (Matrix.vandermonde (fun i : rows μ => (betaVector μ i:ℤ))).det

lemma betaVector_sum (μ : YoungDiagram) :
    (∑ i : rows μ, betaVector μ i)=μ.cells.card+∑ i : rows μ, i.val := by
  have hb (i : rows μ) : betaVector μ i=μ.rowLen i.val+i.rev.val := by
    have hp := row_positive μ i.val i.isLt
    simp only [betaVector,beta,Fin.val_rev]
    omega
  simp_rw [hb]
  rw [Finset.sum_add_distrib]
  have hr : (∑ i : rows μ, μ.rowLen i.val)=μ.cells.card := by
    rw [Fin.sum_univ_eq_sum_range]
    have he := Paper20.rowLens_sum μ
    have hs : ∀ k, ((List.range k).map μ.rowLen).sum=∑ i ∈ range k, μ.rowLen i := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => simp [List.range_succ,Finset.sum_range_succ,ih]
    simpa only [YoungDiagram.rowLens,hs] using he
  rw [hr]
  congr 1
  exact Equiv.sum_comp Fin.revPerm (fun i : rows μ => i.val)

lemma betaDelta_row_form (μ : YoungDiagram) :
    betaDelta μ=∏ i ∈ range (μ.colLen 0),
      ∏ l ∈ Ico (i+1) (μ.colLen 0), (beta μ i-beta μ l) := by
  unfold betaDelta
  have he (i : rows μ) :
      (∏ j ∈ Ioi i, (betaVector μ i-betaVector μ j))=
        ∏ l ∈ Ico (i.val+1) (μ.colLen 0), (beta μ i.val-beta μ l) := by
    apply Finset.prod_bij (fun j _ => j.val)
    · intro j hj
      have hlt : i<j := mem_Ioi.mp hj
      exact mem_Ico.mpr ⟨Nat.succ_le_of_lt hlt,j.isLt⟩
    · intro j hj k hk he
      exact Fin.ext he
    · intro l hl
      obtain ⟨hil,hlm⟩ := mem_Ico.mp hl
      exact ⟨⟨l,hlm⟩,mem_Ioi.mpr (by change i.val<l; omega),rfl⟩
    · intro j hj
      rfl
  simp_rw [he]
  exact Fin.prod_univ_eq_prod_range (fun i : ℕ =>
    ∏ l ∈ Ico (i+1) (μ.colLen 0), (beta μ i-beta μ l)) (μ.colLen 0)

lemma betaDet_natAbs (μ : YoungDiagram) : (betaDet μ).natAbs=betaDelta μ := by
  rw [betaDet,Matrix.det_vandermonde]
  change Int.natAbsHom _=_
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  change Int.natAbs ((betaVector μ j:ℤ)-(betaVector μ i:ℤ))=_
  apply Int.natAbs_natCast_sub_natCast_of_le
  change beta μ j.val ≤ beta μ i.val
  have hlt : i<j := mem_Ioi.mp hj
  exact (beta_strict μ i.val j.val hlt j.isLt).le

lemma hook_beta_factor (μ : YoungDiagram) :
    (∏ c ∈ μ.cells, diagramHook μ c)*betaDelta μ=
      ∏ i : rows μ, (betaVector μ i).factorial := by
  rw [betaDelta_row_form]
  rw [diagram_hook_vandermonde]
  exact (Fin.prod_univ_eq_prod_range _ _).symm

lemma betaDelta_ne_zero (μ : YoungDiagram) : betaDelta μ ≠ 0 := by
  have he := hook_beta_factor μ
  have hp : 0 < ∏ i : rows μ, (betaVector μ i).factorial := by positivity
  intro hz
  rw [hz,mul_zero] at he
  omega

lemma factorialMatrix_det_clear (μ : YoungDiagram) :
    ((∏ i : rows μ, (betaVector μ i).factorial:ℕ):ℚ)*
        (factorialMatrix (betaVector μ) (fun i : rows μ => i.val)).det=
      (betaDet μ:ℚ) := by
  have he := Matrix.det_mul_column
    (fun i : rows μ => ((betaVector μ i).factorial:ℚ))
    (factorialMatrix (betaVector μ) (fun i : rows μ => i.val))
  rw [factorialMatrix_descFactorial] at he
  have hv := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun i : rows μ => (betaVector μ i:ℚ))
    (fun j : rows μ => descPochhammer ℚ j.val)
    (fun j => descPochhammer_natDegree ℚ j.val)
    (fun j => monic_descPochhammer ℚ j.val)
  simp only [descPochhammer_eval_eq_descFactorial] at hv
  rw [← hv] at he
  have hc : (betaDet μ:ℚ)=
      (Matrix.vandermonde (fun i : rows μ => (betaVector μ i:ℚ))).det := by
    rw [betaDet,Int.cast_det]
    congr 1
    apply Matrix.ext
    intro i j
    simp [Matrix.vandermonde,Matrix.map_apply]

  simpa only [Nat.cast_prod] using he.symm.trans hc.symm

/-- Every genuine Young-diagram hook product divides the size factorial.
The proof uses the exact beta Vandermonde factorization and an actual
integer multinomial determinant; no dimension identity is assumed. -/
theorem diagram_hook_dvd_factorial (μ : YoungDiagram) :
    (∏ c ∈ μ.cells, diagramHook μ c) ∣ μ.cells.card.factorial := by
  obtain ⟨z,hz⟩ := factorial_det_integral (betaVector μ)
    (fun i : rows μ => i.val) (betaVector_sum μ)
  let H := ∏ c ∈ μ.cells, diagramHook μ c
  have hf : (H*betaDelta μ:ℕ)=(∏ i : rows μ, (betaVector μ i).factorial) := hook_beta_factor μ
  have he : ((H*betaDelta μ:ℕ):ℤ)*z=(μ.cells.card.factorial:ℤ)*betaDet μ := by
    apply Int.cast_injective (α:=ℚ)
    rw [Int.cast_mul,Int.cast_natCast,Int.cast_mul,Int.cast_natCast,hz,
      Nat.cast_mul]
    have hc := factorialMatrix_det_clear μ
    rw [← Nat.cast_mul,hf]
    linear_combination (norm := ring_nf) (μ.cells.card.factorial:ℚ)*hc
  have ha := congrArg Int.natAbs he
  simp only [Int.natAbs_mul,Int.natAbs_natCast,betaDet_natAbs] at ha
  have hcancel : H*z.natAbs=μ.cells.card.factorial := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (betaDelta_ne_zero μ))
    nlinarith [ha]
  exact ⟨z.natAbs,hcancel.symm⟩

/-- The executable hook-length quotient is an exact natural dimension
for every actual partition, with its divisibility now proved generically. -/
theorem actual_hook_dvd_factorial {n : ℕ} (p : Part n) : (hooksOf p.parts).prod ∣ n.factorial := by
  rw [actual_hook_product]
  simpa only [p.diagram_card] using diagram_hook_dvd_factorial p.diagram

theorem actual_dim_mul_hooks {n : ℕ} (p : Part n) :
    dimOf n p.parts*(hooksOf p.parts).prod=n.factorial :=
  Nat.div_mul_cancel (actual_hook_dvd_factorial p)

end
end Paper20.HookDeterminant

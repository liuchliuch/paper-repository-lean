import Paper20.HookDimensionDet

namespace Paper20.HookDeterminant
open Polynomial Matrix Finset Paper20.HookBeta
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def pairProduct {m : ℕ} (b : Fin m → ℕ) : ℕ :=
  ∏ i, ∏ j, if i<j then b i-b j else 1

lemma pairProduct_Ioi {m : ℕ} (b : Fin m → ℕ) :
    pairProduct b=∏ i, ∏ j ∈ Ioi i, (b i-b j) := by
  apply Finset.prod_congr rfl
  intro i hi
  have he : Ioi i=univ.filter (fun j : Fin m => i<j) := by ext j; simp
  rw [he,Finset.prod_filter]

lemma pairProduct_grow {m : ℕ} (b : Fin m → ℕ) :
    pairProduct (Fin.snoc (α:=fun _ : Fin (m+1) => ℕ) (fun i => b i+1) 0)=pairProduct b*∏ i, (b i+1) := by
  unfold pairProduct
  rw [Fin.prod_univ_castSucc]
  have hl : (∏ j : Fin (m+1),
      if Fin.last m<j then (Fin.snoc (α:=fun _ : Fin (m+1) => ℕ) (fun i => b i+1) 0) (Fin.last m)-
        (Fin.snoc (α:=fun _ : Fin (m+1) => ℕ) (fun i => b i+1) 0) j else 1)=1 := by
    apply Finset.prod_eq_one
    intro j hj
    rw [if_neg (by exact not_lt_of_ge (Fin.le_last j))]
  rw [hl,mul_one]
  simp_rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,Fin.castSucc_lt_last,↓reduceIte,
    Fin.castSucc_lt_castSucc_iff,Nat.add_sub_add_right,Nat.sub_zero]
  rw [Finset.prod_mul_distrib]

lemma factorialProduct_grow {m : ℕ} (b : Fin m → ℕ) :
    (∏ i : Fin (m+1), ((Fin.snoc (α:=fun _ : Fin (m+1) => ℕ) (fun i => b i+1) 0) i).factorial)=
      (∏ i, (b i).factorial)*(∏ i, (b i+1)) := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,Nat.factorial_zero,mul_one,Nat.factorial_succ]
  rw [Finset.prod_mul_distrib,mul_comm]

/-- Beta numbers with any fixed row bound, including zero padded rows. -/
def paddedBeta (μ : YoungDiagram) (m : ℕ) (i : Fin m) : ℕ :=
  μ.rowLen i.val+m-1-i.val

lemma rowLen_zero_of_height_le (μ : YoungDiagram) (m : ℕ) (hm : μ.colLen 0 ≤ m) : μ.rowLen m=0 := by
  by_contra hz
  have hp : 0 < μ.rowLen m := Nat.pos_of_ne_zero hz
  have hc := YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hp)
  omega

lemma paddedBeta_grow (μ : YoungDiagram) (m : ℕ) (hm : μ.colLen 0 ≤ m) :
    paddedBeta μ (m+1)=Fin.snoc (α:=fun _ : Fin (m+1) => ℕ) (fun i => paddedBeta μ m i+1) 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    dsimp only [paddedBeta,Fin.val_last]
    rw [rowLen_zero_of_height_le μ m hm]
    omega
  · rw [Fin.snoc_castSucc]
    have hj := j.isLt
    simp only [paddedBeta,Fin.coe_castSucc]
    omega

/-- The genuine hook-product Vandermonde remains exact for every fixed
row bound. Zero padding is proved algebraically by adjoining beta=0 and
raising every existing beta by one. -/
theorem padded_hook_factor (μ : YoungDiagram) (m : ℕ) (hm : μ.colLen 0 ≤ m) :
    (∏ c ∈ μ.cells, diagramHook μ c)*pairProduct (paddedBeta μ m)=
      ∏ i : Fin m, (paddedBeta μ m i).factorial := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hm
  induction t with
  | zero =>
    simpa only [Nat.add_zero,pairProduct_Ioi,paddedBeta,betaVector,beta,betaDelta] using
      hook_beta_factor μ
  | succ t ih =>
    have he : μ.colLen 0+(t+1)=μ.colLen 0+t+1 := by omega
    rw [he,paddedBeta_grow μ _ (by omega),pairProduct_grow,factorialProduct_grow]
    rw [← mul_assoc,ih (by omega)]

end
end Paper20.HookDeterminant

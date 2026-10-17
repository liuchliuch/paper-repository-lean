import Paper20.PowerSeriesBPS

/-! Correctness of the actual array operations used in Appendix A.
These results connect executable finite differences and elimination updates
to coefficient arithmetic; they do not replace the executable definitions. -/
namespace Paper20.ArraySemantics
open Finset BigOperators Paper20.Semantics

lemma getD_setBang (a : Array ℤ) (i j : ℕ) (v : ℤ) (hj : j < a.size) :
    (a.set! i v).getD j 0 = if i = j then v else a.getD j 0 := by
  by_cases he : i = j
  · subst i
    simp [Array.set!, Array.getD_eq_getD_getElem?, hj]
  · simp [Array.set!, Array.getD_eq_getD_getElem?, he]

/-- Any fold of fixed writes is a tabulation on the indices that are written. -/
lemma fixed_writes (xs : List ℕ) (a : Array ℤ) (v : ℕ → ℤ) (j : ℕ)
    (hj : j < a.size) :
    (xs.foldl (fun a i => a.set! i (v i)) a).getD j 0 =
      if j ∈ xs then v j else a.getD j 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons i xs ih =>
    rw [List.foldl_cons, ih]
    · rw [getD_setBang a i j (v i) hj]
      by_cases hi : i = j
      · subst i; simp
      · by_cases hmem : j ∈ xs <;> simp [hmem, hi, Ne.symm hi]
    · simpa [size_setBang] using hj

/-- Additive writes have precisely their expected coefficientwise effect.
No distinctness assumption is needed: repeated writes add repeatedly. -/
lemma additive_writes (xs : List ℕ) (a : Array ℤ)
    (index : ℕ → ℕ) (inc : ℕ → ℤ) (j : ℕ) (hj : j < a.size) :
    (xs.foldl (fun a i => a.set! (index i) (a.getD (index i) 0 + inc i)) a).getD j 0 =
      a.getD j 0 + ((xs.map (fun i => if index i = j then inc i else 0)).sum) := by
  induction xs generalizing a with
  | nil => simp
  | cons i xs ih =>
    rw [List.foldl_cons, ih]
    · rw [getD_setBang a (index i) j _ hj]
      by_cases he : index i = j
      · rw [if_pos he, he]
        simp only [List.map_cons, List.sum_cons, if_pos he]
        ring
      · rw [if_neg he]
        simp [he]
    · simpa [size_setBang] using hj

/-- One actual finite difference is multiplication by `(1-q)` on every
coefficient present in the array. -/
theorem diffOnce_getD (a : Array ℤ) (j : ℕ) (hj : j < a.size) :
    (diffOnce a).getD j 0 =
      if j = 0 then a.getD 0 0 else a.getD j 0 - a.getD (j-1) 0 := by
  unfold diffOnce
  simp only [Array.getElem!_eq_getD, show (default : ℤ) = 0 by rfl]
  have hf : ∀ (xs : List ℕ) (b : Array ℤ),
      xs.foldl (fun acc i => acc.set! (i+1) (a.getD (i+1) 0 - a.getD i 0)) b =
      (xs.map (fun i => i+1)).foldl
        (fun acc i => acc.set! i (a.getD i 0 - a.getD (i-1) 0)) b := by
    intro xs b
    rw [List.foldl_map]
    simp
  rw [hf, fixed_writes _ _ _ _ hj]
  by_cases hj0 : j = 0
  · subst j; simp
  · have hmem : j ∈ (List.range (a.size-1)).map (fun i => i+1) := by
      apply List.mem_map.mpr
      exact ⟨j-1, List.mem_range.mpr (by omega), by omega⟩
    rw [if_pos hmem, if_neg hj0]

lemma mulOneMinusQPow_succ (a : Array ℤ) (r : ℕ) :
    mulOneMinusQPow a (r+1) = diffOnce (mulOneMinusQPow a r) := by
  simp [mulOneMinusQPow, List.range_succ, List.foldl_append]

lemma residual_zero (H : ℕ → ℤ) (j : ℕ) : hilbertResidual 0 H j = H j := by
  have hc := coeff_hilbert_residual 0 j H
  simpa only [pow_zero, one_mul, hilbertSeries, PowerSeries.coeff_mk] using hc.symm

lemma residual_succ (r j : ℕ) (H : ℕ → ℤ) :
    hilbertResidual (r+1) H (j+1) = hilbertResidual r H (j+1) - hilbertResidual r H j := by
  rw [← coeff_hilbert_residual]
  have he : ((1-PowerSeries.X)^(r+1) * hilbertSeries H : PowerSeries ℤ) =
      (1-PowerSeries.X)^r * hilbertSeries H -
        ((1-PowerSeries.X)^r * hilbertSeries H)*PowerSeries.X := by ring
  rw [he, map_sub, PowerSeries.coeff_succ_mul_X,
    coeff_hilbert_residual, coeff_hilbert_residual]

/-- The actual finite-difference array computes the defining BPS residual
on its entire retained coefficient range, for every input and exponent. -/
theorem mulOneMinusQPow_correct (a : Array ℤ) (r j : ℕ) (hj : j < a.size) :
    (mulOneMinusQPow a r).getD j 0 =
      hilbertResidual r (fun i => a.getD i 0) j := by
  induction r generalizing j with
  | zero => simp [mulOneMinusQPow, residual_zero]
  | succ r ih =>
    rw [mulOneMinusQPow_succ, diffOnce_getD _ j (by rwa [size_mulOneMinusQPow])]
    cases j with
    | zero =>
      rw [if_pos rfl, ih 0 hj]
      simp [hilbertResidual]
    | succ j =>
      rw [if_neg (by omega), show j+1-1 = j by omega,
        ih (j+1) hj, ih j (by omega), residual_succ]

lemma getD_nat_int_map (a : Array ℕ) (j : ℕ) :
    (a.map (fun n : ℕ => (n:ℤ))).getD j 0 = (a.getD j 0 : ℤ) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases he : a[j]? <;> simp [he]

/-- The paper's actual `fArray` is the coefficient residual of its Hilbert
partition computation. This is an implementation theorem, not an assumed
identification with a certificate. -/
theorem fArray_correct (r k ℓ : ℕ) (hℓ : ℓ ≤ deg r k) :
    (fArray r k).getD ℓ 0 =
      hilbertResidual r (fun i => ((hilbertArray r k).getD i 0 : ℤ)) ℓ := by
  unfold fArray
  rw [mulOneMinusQPow_correct _ r ℓ (by rw [Array.size_map, size_hilbertArray]; exact Nat.lt_succ_of_le hℓ)]
  congr 1
  funext i
  exact getD_nat_int_map _ i

end Paper20.ArraySemantics

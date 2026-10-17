import Paper20.ArraySemantics

/-! Correctness of the actual triangular array elimination in Appendix A.
The invariant tracks the residual and every stored coefficient against the
canonical inverse of the original BPS coefficient equations. -/
namespace Paper20.Elimination
open Finset BigOperators Paper20.Semantics Paper20.ArraySemantics

set_option maxHeartbeats 4000000

lemma signedChoose_eq (h j : ℕ) :
    signedChoose h j = (-1 : ℤ)^j * (Nat.choose (2*h) j : ℤ) := by
  rw [signedChoose, neg_one_pow_eq_ite]
  simp only [Nat.even_iff]
  ring

/-- The actual inner subtraction loop, retaining the lower half of (24). -/
def subtractRow (d ell : ℕ) (H : Array ℤ) (nh : ℤ) : Array ℤ :=
  (List.range (d-ell+1)).foldl (fun H j =>
    H.set! (ell+j) (H.getD (ell+j) 0 - nh*signedChoose (d-ell) j)) H

lemma subtractRow_size (d ell : ℕ) (H : Array ℤ) (nh : ℤ) :
    (subtractRow d ell H nh).size = H.size :=
  size_foldl_cons (fun _ _ => size_setBang ..)

lemma sum_map_range (f : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- Exact coefficient effect of one subtraction row. -/
theorem subtractRow_getD (d ell : ℕ) (H : Array ℤ) (nh : ℤ)
    (i : ℕ) (hi : i < H.size) (hid : i ≤ d) :
    (subtractRow d ell H nh).getD i 0 = H.getD i 0 -
      if ell ≤ i then nh*signedChoose (d-ell) (i-ell) else 0 := by
  unfold subtractRow
  simp only [sub_eq_add_neg]
  rw [additive_writes _ H (fun j => ell+j) (fun j => -(nh*signedChoose (d-ell) j)) i hi,
    sum_map_range]
  by_cases hel : ell ≤ i
  · rw [if_pos hel]
    have hmem : i-ell ∈ range (d-ell+1) := mem_range.mpr (by omega)
    rw [Finset.sum_eq_single (i-ell)]
    · rw [if_pos (by omega)]
    · intro j hj hne
      rw [if_neg (by omega)]
    · exact fun hn => False.elim (hn hmem)
  · rw [if_neg hel]
    have hs : (∑ j ∈ range (d-ell+1),
        if ell+j = i then -(nh*signedChoose (d-ell) j) else 0) = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [if_neg (by omega)]
    rw [hs]
    ring

/-- One exact outer step of the executable elimination. -/
def step (d : ℕ) (s : Array ℤ × Array ℤ) (ell : ℕ) : Array ℤ × Array ℤ :=
  (subtractRow d ell s.1 (s.1.getD ell 0),
    s.2.set! (d-ell) (s.1.getD ell 0))

/-- The executable state after the first `t` elimination steps. -/
def stateAt (F : Array ℤ) (t : ℕ) : Array ℤ × Array ℤ :=
  (List.range t).foldl (step (F.size-1)) (F, Array.replicate F.size 0)

lemma stateAt_zero (F : Array ℤ) : stateAt F 0 = (F, Array.replicate F.size 0) := rfl

lemma stateAt_succ (F : Array ℤ) (t : ℕ) :
    stateAt F (t+1) = step (F.size-1) (stateAt F t) t := by
  simp [stateAt, List.range_succ, List.foldl_append]

/-- These are the actual functions in `Hilbert.bpsPass`, not a new algorithm. -/
theorem bpsPass_eq_stateAt (F : Array ℤ) : bpsPass F = stateAt F F.size := by
  unfold bpsPass stateAt
  dsimp only
  apply congrArg (fun f => (List.range F.size).foldl f (F, Array.replicate F.size 0))
  funext s ell
  rcases s with ⟨H,n⟩
  have hm : min (2*(F.size-1-ell)) (F.size-1-ell) = F.size-1-ell := by omega
  simp only [hm, step, subtractRow, Array.getElem!_eq_getD,
    show (default : ℤ) = 0 by rfl]

lemma stateAt_sizes (F : Array ℤ) (t : ℕ) :
    (stateAt F t).1.size = F.size ∧ (stateAt F t).2.size = F.size := by
  induction t with
  | zero => simp [stateAt_zero]
  | succ t ih =>
    rw [stateAt_succ]
    simpa only [step, subtractRow_size, size_setBang] using ih

/-- The scalar recurrence used by the canonical inverse, with the same
signed binomials as the executable subtraction rows. -/
lemma inverse_step (d : ℕ) (F : ℕ → ℤ) (ell : ℕ) :
    inverse d F ell = F ell -
      ∑ j ∈ range ell, inverse d F j * signedChoose (d-j) (ell-j) := by
  rw [inverse]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j hj
  rw [signedChoose_eq]
  ring

/-- Inductive invariant of the elimination state. The residual contains
exactly the unremoved terms, and the output contains exactly the previously
extracted coefficients. -/
def Invariant (F : Array ℤ) (t : ℕ) : Prop :=
  (∀ i, i < F.size → (stateAt F t).1.getD i 0 = F.getD i 0 -
    ∑ j ∈ range t, if j ≤ i then
      inverse (F.size-1) (fun ℓ => F.getD ℓ 0) j * signedChoose (F.size-1-j) (i-j) else 0) ∧
  (∀ h, h < F.size → (stateAt F t).2.getD h 0 =
    if F.size-1-h < t then inverse (F.size-1) (fun ℓ => F.getD ℓ 0) (F.size-1-h) else 0)

/-- The complete invariant is derived by induction over the actual array loop. -/
theorem stateAt_invariant (F : Array ℤ) (t : ℕ) (ht : t ≤ F.size) : Invariant F t := by
  induction t with
  | zero =>
    constructor
    · intro i hi; simp [stateAt_zero]
    · intro h hh; simp [stateAt_zero, Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hh]
  | succ t ih =>
    have htm : t < F.size := by omega
    have htd : t ≤ F.size-1 := by omega
    obtain ⟨hres,hout⟩ := ih (by omega)
    have hval : (stateAt F t).1.getD t 0 =
        inverse (F.size-1) (fun ℓ => F.getD ℓ 0) t := by
      rw [hres t htm, inverse_step]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [if_pos (show j ≤ t by have := mem_range.mp hj; omega)]
    constructor
    · intro i hi
      rw [stateAt_succ]
      dsimp only [step]
      rw [subtractRow_getD _ _ _ _ i (by rw [(stateAt_sizes F t).1]; exact hi) (by omega),
        hres i hi, hval, Finset.sum_range_succ]
      split_ifs <;> ring
    · intro h hh
      rw [stateAt_succ]
      dsimp only [step]
      rw [getD_setBang _ _ h _ (by rw [(stateAt_sizes F t).2]; exact hh)]
      by_cases he : F.size-1-t = h
      · rw [if_pos he, hval]
        have hs : F.size-1-h = t := by omega
        rw [hs, if_pos (by omega)]
      · rw [if_neg he, hout h hh]
        by_cases hp : F.size-1-h < t
        · rw [if_pos hp, if_pos (by omega)]
        · rw [if_neg hp, if_neg (by omega)]

/-- Every retained coefficient produced by the actual executable elimination
is exactly the canonical inverse of the triangular BPS equations. -/
theorem bpsFromF_getD (F : Array ℤ) (h : ℕ) (hh : h < F.size) :
    (bpsFromF F).getD h 0 =
      inverse (F.size-1) (fun ℓ => F.getD ℓ 0) (F.size-1-h) := by
  unfold bpsFromF
  rw [bpsPass_eq_stateAt]
  have he := (stateAt_invariant F F.size le_rfl).2 h hh
  rw [if_pos (by omega)] at he
  exact he

theorem bpsFromF_eq_extracted (F : Array ℤ) (h : ℕ) (hh : h < F.size) :
    (bpsFromF F).getD h 0 =
      extracted (F.size-1) (fun ℓ => F.getD ℓ 0) h := by
  rw [bpsFromF_getD F h hh, extracted, if_pos (by omega)]

/-- The implementation satisfies the original recurrence with no certificate
premise and no assumed identification with the inverse. -/
theorem bpsFromF_recurrence (F : Array ℤ) (hF : 0 < F.size) :
    recurrence25 (F.size-1) (fun ℓ => F.getD ℓ 0) (fun h => (bpsFromF F).getD h 0) := by
  intro h hh
  dsimp only
  rw [bpsFromF_eq_extracted F h (by omega)]
  rw [extracted_recurrence _ _ h hh]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  rw [bpsFromF_eq_extracted F j (by omega)]

/-- Removing the final natural-part wrapper exposes the actual integer
array coefficient, on every retained index. -/
theorem bpsCoeff_eq_toNat (r k h : ℕ) (hh : h ≤ deg r k) :
    bpsCoeff r k h = ((bpsFromF (fArray r k)).getD h 0).toNat := by
  unfold bpsCoeff bpsCoeffs
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  rw [dif_pos (show h < deg r k+1 by omega)]
  rfl

/-- Recurrence (25) for the exact integer output of the Hilbert/BPS program. -/
theorem bpsFromHilbert_recurrence (r k : ℕ) :
    recurrence25 (deg r k) (fun ℓ => (fArray r k).getD ℓ 0)
      (fun h => (bpsFromF (fArray r k)).getD h 0) := by
  have hr := bpsFromF_recurrence (fArray r k) (by rw [size_fArray]; omega)
  simpa only [size_fArray, Nat.add_sub_cancel] using hr

/-- The original defining BPS expansion determines the exact integer output
of the implemented program whenever its Hilbert input agrees through `d`.
In particular no equality of BPS coefficients is an input to this theorem. -/
theorem original_expansion_to_program (r k : ℕ) {H n : ℕ → ℤ}
    (hn : localBPSExpansion r (deg r k) H n)
    (hH : ∀ ℓ, ℓ ≤ deg r k → H ℓ = ((hilbertArray r k).getD ℓ 0 : ℤ)) :
    ∀ h, h ≤ deg r k → n h = (bpsFromF (fArray r k)).getD h 0 := by
  apply recurrence25_unique (F := fun ℓ => (fArray r k).getD ℓ 0)
    (n := n) (m := fun h => (bpsFromF (fArray r k)).getD h 0)
    ?_ (bpsFromHilbert_recurrence r k)
  intro h hh
  have hf : (fArray r k).getD (deg r k-h) 0 = hilbertResidual r H (deg r k-h) := by
    rw [fArray_correct r k _ (by omega)]
    unfold hilbertResidual
    apply sum_congr rfl
    intro i hi
    rw [hH (deg r k-h-i) (by omega)]
  have he := localBPSExpansion_recurrence hn h hh
  rwa [← hf] at he

/-- The natural-valued public implementation is the natural part of the
original integer coefficients; no silent positivity premise is needed. -/
theorem bpsCoeff_from_original_expansion (r k : ℕ) {H n : ℕ → ℤ}
    (hn : localBPSExpansion r (deg r k) H n)
    (hH : ∀ ℓ, ℓ ≤ deg r k → H ℓ = ((hilbertArray r k).getD ℓ 0 : ℤ))
    (h : ℕ) (hh : h ≤ deg r k) : bpsCoeff r k h = (n h).toNat := by
  rw [bpsCoeff_eq_toNat r k h hh, ← original_expansion_to_program r k hn hH h hh]

end Paper20.Elimination

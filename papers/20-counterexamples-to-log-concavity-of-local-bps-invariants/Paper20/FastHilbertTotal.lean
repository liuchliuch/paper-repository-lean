import Paper20.FastHilbertProof

namespace Paper20.FastHilbert
open Finset BigOperators
set_option maxHeartbeats 4000000

lemma series_length (hooks : List ℕ) (len : ℕ) : (series hooks len).length = len := by
  have hf (xs : List ℕ) : (hooks.foldl geom xs).length = xs.length := by
    induction hooks generalizing xs with
    | nil => rfl
    | cons a hooks ih => simp only [List.foldl_cons, ih, geom_length]
  unfold series
  rw [hf]
  simp only [List.length_take, List.length_cons, List.length_replicate]
  omega

lemma summand_length (r k d : ℕ) (parts : List ℕ) :
    (summand r k d parts).length = d+1 := by
  unfold summand
  dsimp only
  split_ifs with h
  · simp
  · simp only [List.length_append, List.length_replicate, List.length_map, series_length]
    omega

lemma addPart_length (r k d : ℕ) (H : List ℕ) (parts : List ℕ) (hH : H.length = d+1) :
    (addPart r k d H parts).length = d+1 := by
  unfold addPart
  dsimp only
  split_ifs with h
  · exact hH
  · simp only [List.length_zipWith, hH, List.length_append, List.length_replicate,
      List.length_map, series_length]
    omega

lemma additive_writes_nat (xs : List ℕ) (a : Array ℕ)
    (index inc : ℕ → ℕ) (j : ℕ) (hj : j < a.size) :
    (xs.foldl (fun a i => a.set! (index i) (a.getD (index i) 0 + inc i)) a).getD j 0 =
      a.getD j 0 + ((xs.map (fun i => if index i = j then inc i else 0)).sum) := by
  induction xs generalizing a with
  | nil => simp
  | cons i xs ih =>
    rw [List.foldl_cons, ih]
    · rw [getD_setNat a (index i) j _ hj]
      by_cases he : index i = j
      · rw [if_pos he, he]
        simp only [List.map_cons, List.sum_cons, if_pos he]
        omega
      · rw [if_neg he]
        simp [he]
    · simpa [size_setBang] using hj

lemma sum_map_range_nat (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

lemma getD_map_mul (t : List ℕ) (f i : ℕ) :
    (t.map (fun n => f*n)).getD i 0 = f*t.getD i 0 := by
  simp only [List.getD_eq_getD_getElem?, List.getElem?_map]
  cases he : t[i]? <;> simp

lemma getD_replicate_zero (len i : ℕ) : (List.replicate len 0).getD i 0 = 0 := by
  simp only [List.getD_eq_getD_getElem?, List.getElem?_replicate]
  split_ifs <;> rfl

/-- One partition contribution is identical in both implementations, with
no positivity or value-of-the-BPS-coefficient assumption. -/
theorem addSummand_toList (H : Array ℕ) (parts : List ℕ) (r k d : ℕ)
    (hH : H.size = d+1) :
    (addSummand H parts r k d).toList = addPart r k d H.toList parts := by
  unfold addSummand addPart
  dsimp only
  by_cases hn : shiftE parts k d < 0
  · rw [if_pos hn, if_pos (Or.inl hn)]
  · rw [if_neg hn]
    by_cases hd : d < (shiftE parts k d).toNat
    · rw [if_pos hd, if_pos (Or.inr hd)]
    · rw [if_neg hd, if_neg (by omega)]
      let E := (shiftE parts k d).toNat
      let t := geomSeries (hooksOf parts) (d-E+1)
      let f := dimOf r parts
      have hE : E ≤ d := by dsimp [E]; omega
      have ht : t.size = d-E+1 := size_geomSeries _ _
      have hvlen : (List.replicate E 0 ++ (series (hooksOf parts) (d-E+1)).map
          (fun n => f*n)).length = d+1 := by
        simp only [List.length_append, List.length_replicate, List.length_map, series_length]
        omega
      apply list_eq_of_getD
      · rw [Array.length_toList]
        have hsize : ((List.range t.size).foldl (fun H j =>
            H.set! (E+j) (H[E+j]! + f*t[j]!)) H).size = H.size :=
          size_foldl_cons (fun _ _ => size_setBang ..)
        change _ = (List.zipWith Nat.add H.toList
          (List.replicate E 0 ++ (series (hooksOf parts) (d-E+1)).map (fun n => f*n))).length
        rw [hsize, List.length_zipWith, Array.length_toList, hH, hvlen, min_self]
      · intro i hi
        have hsize : ((List.range t.size).foldl (fun H j =>
            H.set! (E+j) (H[E+j]! + f*t[j]!)) H).size = H.size :=
          size_foldl_cons (fun _ _ => size_setBang ..)
        have hiH : i < H.size := by
          change i < (Array.toList ((List.range t.size).foldl (fun H j =>
            H.set! (E+j) (H[E+j]! + f*t[j]!)) H)).length at hi
          simpa only [Array.length_toList, hsize] using hi
        change (Array.toList ((List.range t.size).foldl (fun H j =>
            H.set! (E+j) (H[E+j]! + f*t[j]!)) H)).getD i 0 = _
        rw [getD_toList]
        simp only [Array.getElem!_eq_getD, show (default : ℕ) = 0 by rfl]
        rw [additive_writes_nat _ H (fun j => E+j) (fun j => f*t.getD j 0) i hiH,
          sum_map_range_nat]
        rw [getD_zipAdd _ _ i (by simpa using hiH) (by rw [hvlen]; omega),
          getD_toList, getD_append_if, List.length_replicate]
        by_cases hei : i < E
        · rw [if_pos hei, getD_replicate_zero]
          have hs : (∑ j ∈ range t.size, if E+j = i then f*t.getD j 0 else 0) = 0 := by
            apply sum_eq_zero
            intro j hj
            rw [if_neg (by omega)]
          rw [hs]
        · rw [if_neg hei, getD_map_mul, ← series_correct]
          change H.getD i 0 + _ = H.getD i 0 + f*t.toList.getD (i-E) 0
          rw [getD_toList]
          congr 1
          rw [Finset.sum_eq_single (i-E)]
          · rw [if_pos (by omega)]
          · intro j hj hne; rw [if_neg (by omega)]
          · intro hnot
            exact False.elim (hnot (mem_range.mpr (by rw [ht]; omega)))

/-- The complete actual Hilbert partition computation has the fast list
implementation as a proved equivalent, not as a new model. -/
theorem total_correct (r k : ℕ) : (hilbertArray r k).toList = total r k := by
  have hf (pss : List (List ℕ)) (H : Array ℕ) (hH : H.size = deg r k+1) :
      (pss.foldl (fun H ps => addSummand H ps r k (deg r k)) H).toList =
      pss.foldl (addPart r k (deg r k)) H.toList := by
    induction pss generalizing H with
    | nil => rfl
    | cons ps pss ih =>
      rw [List.foldl_cons, List.foldl_cons, ih _ (by rwa [size_addSummand]),
        addSummand_toList H ps r k (deg r k) hH]
  unfold hilbertArray total
  rw [hf _ _ (by simp)]
  simp

end Paper20.FastHilbert

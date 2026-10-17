import Paper20.HilbertJobs
import Paper20.FastHilbertTotal

namespace Paper20.HilbertJobs
open Finset BigOperators Paper20.FastHilbert
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

/-- Exact recursion-tree decomposition of the partition list. -/
theorem parts_children (j : Job) (hf : 0 < j.fuel) (hn : j.rem ≠ 0) :
    (children j).flatMap parts = parts j := by
  rcases j with ⟨pre,cap,n,fuel⟩
  cases fuel with
  | zero => simp at hf
  | succ fuel =>
    simp only [children, hn, ↓reduceIte, List.flatMap_map, parts,
      partitionsCappedAux, hn, ↓reduceIte, List.map_flatMap]
    apply List.flatMap_congr
    intro a ha
    simp [List.map_map, List.append_assoc]

lemma addPart_getD (H : List ℕ) (ps : List ℕ) (i : ℕ)
    (hH : H.length = 904) (hi : i < 904) :
    (FastHilbert.addPart 43 1 903 H ps).getD i 0 = H.getD i 0 +
      (FastHilbert.summand 43 1 903 ps).getD i 0 := by
  unfold FastHilbert.addPart FastHilbert.summand
  dsimp only
  split_ifs with h
  · rw [getD_replicate_zero, Nat.add_zero]
  · apply getD_zipAdd
    · omega
    · simp only [List.length_append, List.length_replicate, List.length_map, series_length]
      omega

lemma fold_addPart_length (pss : List (List ℕ)) (H : List ℕ) (hH : H.length = 904) :
    (pss.foldl (FastHilbert.addPart 43 1 903) H).length = 904 := by
  induction pss generalizing H with
  | nil => exact hH
  | cons ps pss ih =>
    rw [List.foldl_cons]
    exact ih _ (addPart_length _ _ _ _ _ hH)

lemma fold_addPart_getD (pss : List (List ℕ)) (H : List ℕ)
    (hH : H.length = 904) (i : ℕ) (hi : i < 904) :
    (pss.foldl (FastHilbert.addPart 43 1 903) H).getD i 0 = H.getD i 0 +
      (pss.map (fun ps => (FastHilbert.summand 43 1 903 ps).getD i 0)).sum := by
  induction pss generalizing H with
  | nil => simp
  | cons ps pss ih =>
    rw [List.foldl_cons, ih _ (addPart_length _ _ _ _ _ hH), addPart_getD _ _ _ hH hi]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem value_length (j : Job) : (value j).length = 904 :=
  fold_addPart_length _ _ (by simp)

theorem value_getD (j : Job) (i : ℕ) (hi : i < 904) :
    (value j).getD i 0 =
      ((parts j).map (fun ps => (FastHilbert.summand 43 1 903 ps).getD i 0)).sum := by
  rw [value, fold_addPart_getD _ _ (by simp) i hi, getD_replicate_zero, Nat.zero_add]

lemma fold_zip_length (vs : List (List ℕ)) (H : List ℕ) (hH : H.length = 904)
    (hvs : ∀ v ∈ vs, v.length = 904) :
    (vs.foldl (List.zipWith Nat.add) H).length = 904 := by
  induction vs generalizing H with
  | nil => exact hH
  | cons v vs ih =>
    rw [List.foldl_cons]
    apply ih
    · simp [List.length_zipWith, hH, hvs v (by simp)]
    · intro w hw; exact hvs w (by simp [hw])

lemma fold_zip_getD (vs : List (List ℕ)) (H : List ℕ) (hH : H.length = 904)
    (hvs : ∀ v ∈ vs, v.length = 904) (i : ℕ) (hi : i < 904) :
    (vs.foldl (List.zipWith Nat.add) H).getD i 0 =
      H.getD i 0 + (vs.map (fun v => v.getD i 0)).sum := by
  induction vs generalizing H with
  | nil => simp
  | cons v vs ih =>
    have hv := hvs v (by simp)
    have hs : (List.zipWith Nat.add H v).length = 904 := by simp [hH,hv]
    rw [List.foldl_cons, ih _ hs (fun w hw => hvs w (by simp [hw])),
      getD_zipAdd _ _ i (by omega) (by omega)]
    simp only [List.map_cons, List.sum_cons]
    omega

lemma sum_flatMap_nat {α : Type*} (xs : List α) (f : α → List ℕ) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, List.sum_append]

/-- Replacing a subtree by the sum of all its children preserves every
coefficient. Thus every generated internal-node proof certifies completeness,
not just the numeric correctness of a selected subset of partitions. -/
theorem value_children (j : Job) (hf : 0 < j.fuel) (hn : j.rem ≠ 0) :
    value j = combine ((children j).map value) := by
  apply list_eq_of_getD
  · rw [value_length]
    symm
    exact fold_zip_length _ _ (by simp) (by
      intro v hv
      obtain ⟨ch,hch,rfl⟩ := List.mem_map.mp hv
      exact value_length ch)
  · intro i hi
    have hi' : i < 904 := by rwa [value_length] at hi
    rw [value_getD _ _ hi']
    unfold combine
    rw [fold_zip_getD _ _ (by simp) (by
      intro v hv
      obtain ⟨ch,hch,rfl⟩ := List.mem_map.mp hv
      exact value_length ch) i hi', getD_replicate_zero, Nat.zero_add]
    rw [← parts_children j hf hn, List.map_flatMap]
    rw [sum_flatMap_nat]
    simp only [List.map_map, Function.comp_apply]
    congr 1
    apply List.map_congr_left
    intro ch hch
    exact (value_getD ch i hi').symm

lemma parts_root : parts root = partitionsOf 43 := by
  change (partitionsCappedAux 44 43 43).map (fun tail => ([] : List ℕ)++tail) = partitionsOf 43
  rw [show (fun tail : List ℕ => ([] : List ℕ)++tail) = id from rfl, List.map_id]
  rfl

/-- The root job is the complete original 43-fold-point Hilbert computation. -/
theorem root_value : (hilbertArray 43 1).toList = value root := by
  rw [FastHilbert.total_correct]
  have hd : deg 43 1 = 903 := by decide
  unfold FastHilbert.total value
  rw [parts_root, hd]

end Paper20.HilbertJobs

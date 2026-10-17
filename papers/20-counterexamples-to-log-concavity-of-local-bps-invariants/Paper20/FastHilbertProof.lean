import Paper20.FastHilbert
import Paper20.ArraySemantics

namespace Paper20.FastHilbert
open Paper20.ArraySemantics
set_option maxHeartbeats 4000000

lemma getD_append_if (xs ys : List ℕ) (i : ℕ) :
    (xs++ys).getD i 0 = if i < xs.length then xs.getD i 0 else ys.getD (i-xs.length) 0 := by
  simp only [List.getD_eq_getD_getElem?, List.getElem?_append]
  split_ifs <;> rfl

lemma getD_take_lt (xs : List ℕ) (a i : ℕ) (hi : i < a) :
    (xs.take a).getD i 0 = xs.getD i 0 := by
  simp [List.getD_eq_getD_getElem?, List.getElem?_take, hi]

lemma getD_drop_eq (xs : List ℕ) (a i : ℕ) :
    (xs.drop a).getD i 0 = xs.getD (a+i) 0 := by
  simp [List.getD_eq_getD_getElem?, List.getElem?_drop, Nat.add_comm]

lemma getD_zipAdd (xs ys : List ℕ) (i : ℕ) (hx : i < xs.length) (hy : i < ys.length) :
    (List.zipWith Nat.add xs ys).getD i 0 = xs.getD i 0 + ys.getD i 0 := by
  induction xs generalizing ys i with
  | nil => simp at hx
  | cons x xs ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i =>
        simpa using ih ys i (by simpa using hx) (by simpa using hy)

@[simp] lemma geomBlocks_nil (a fuel : ℕ) (prev : List ℕ) :
    geomBlocks a fuel [] prev = [] := by cases fuel <;> rfl

/-- The block algorithm satisfies exactly the geometric-series recurrence. -/
theorem geomBlocks_spec (a : ℕ) (ha : 0 < a) (fuel : ℕ) (old prev : List ℕ)
    (hf : old.length ≤ fuel) (hp : prev.length = a) :
    (geomBlocks a fuel old prev).length = old.length ∧
    ∀ j, j < old.length → (geomBlocks a fuel old prev).getD j 0 = old.getD j 0 +
      if j < a then prev.getD j 0 else (geomBlocks a fuel old prev).getD (j-a) 0 := by
  induction fuel generalizing old prev with
  | zero =>
    have he : old = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst old
    simp [geomBlocks]
  | succ fuel ih =>
    by_cases hn : old = []
    · subst old; simp
    have hne : old.isEmpty = false := by cases old <;> simp_all
    let cur := List.zipWith Nat.add (old.take a) prev
    have hc : cur.length = min a old.length := by
      simp only [cur, List.length_zipWith, List.length_take, hp]
      omega
    have he : geomBlocks a (fuel+1) old prev =
        cur ++ geomBlocks a fuel (old.drop a) cur := by
      simp only [geomBlocks, hne, Bool.false_eq_true, ↓reduceIte]
      rfl
    by_cases hs : old.length ≤ a
    · have hd : old.drop a = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_drop]
        omega
      rw [he, hd, geomBlocks_nil, List.append_nil]
      constructor
      · rw [hc, min_eq_right hs]
      · intro j hj
        have hjA : j < a := by omega
        rw [if_pos hjA]
        dsimp only [cur]
        rw [getD_zipAdd _ _ j (by simp; omega) (by omega), getD_take_lt _ _ _ hjA]
    · have hb : a < old.length := by omega
      have hcA : cur.length = a := by rw [hc, min_eq_left (by omega)]
      have ht := ih (old.drop a) cur (by simp; omega) hcA
      constructor
      · rw [he, List.length_append, hcA, ht.1, List.length_drop]
        omega
      · intro j hj
        rw [he, getD_append_if, hcA]
        by_cases hjA : j < a
        · rw [if_pos hjA, if_pos hjA]
          dsimp only [cur]
          rw [getD_zipAdd _ _ j (by simp; omega) (by omega), getD_take_lt _ _ _ hjA]
        · rw [if_neg hjA, if_neg hjA]
          rw [ht.2 (j-a) (by simp; omega), getD_drop_eq,
            show a+(j-a) = j by omega]
          congr 1
          rw [getD_append_if, hcA]

/-- The fast update preserves the complete truncation length. -/
theorem geom_length (t : List ℕ) (a : ℕ) : (geom t a).length = t.length := by
  unfold geom
  split_ifs with ha
  · simp [size_geomStep]
  · exact (geomBlocks_spec a (by omega) t.length t (List.replicate a 0) le_rfl (by simp)).1

/-- A positive-hook update implements division by `(1-q^a)` through the
whole retained coefficient range. -/
theorem geom_recurrence (t : List ℕ) (a : ℕ) (ha : 0 < a) (j : ℕ) (hj : j < t.length) :
    (geom t a).getD j 0 = t.getD j 0 +
      if a ≤ j then (geom t a).getD (j-a) 0 else 0 := by
  have hs := (geomBlocks_spec a ha t.length t (List.replicate a 0) le_rfl (by simp)).2 j hj
  unfold geom
  rw [if_neg (by omega)]
  by_cases hja : j < a
  · rw [if_neg (by omega)]
    rw [if_pos hja] at hs
    simpa [List.getD_eq_getD_getElem?, List.getElem?_replicate, hja] using hs
  · rw [if_pos (by omega)]
    rw [if_neg hja] at hs
    exact hs

lemma getD_setNat (xs : Array ℕ) (i j v : ℕ) (hj : j < xs.size) :
    (xs.set! i v).getD j 0 = if i = j then v else xs.getD j 0 := by
  by_cases he : i = j
  · subst i; simp [Array.set!, Array.getD_eq_getD_getElem?, hj]
  · simp [Array.set!, Array.getD_eq_getD_getElem?, he]

lemma getD_toList (xs : Array ℕ) (i : ℕ) : xs.toList.getD i 0 = xs.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getD_getElem?]

lemma list_eq_of_getD {xs ys : List ℕ} (hlen : xs.length = ys.length)
    (hget : ∀ i, i < xs.length → xs.getD i 0 = ys.getD i 0) : xs = ys := by
  apply List.ext_getElem hlen
  intro i hi hi'
  have he := hget i hi
  simpa only [List.getD_eq_getD_getElem?, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi', Option.getD_some] using he

/-- The block update and the original in-place array loop are identical.
The proof follows the actual loop and uses the geometric recurrence. -/
theorem geomStep_toList (xs : Array ℕ) (a : ℕ) :
    (geomStep xs a).toList = geom xs.toList a := by
  by_cases ha0 : a = 0
  · subst a
    simp [geom]
  have ha : 0 < a := by omega
  let out := geom xs.toList a
  have hout : out.length = xs.size := by simp [out, geom_length]
  have hrec (i : ℕ) (hi : i < xs.size) :
      out.getD i 0 = xs.getD i 0 + if a ≤ i then out.getD (i-a) 0 else 0 := by
    simpa only [getD_toList] using geom_recurrence xs.toList a ha i (by simpa using hi)
  let st (n : ℕ) := (List.range n).foldl
    (fun acc j => acc.set! (a+j) (acc[a+j]! + acc[j]!)) xs
  have hsize (n : ℕ) : (st n).size = xs.size :=
    size_foldl_cons (fun _ _ => size_setBang ..)
  have hstep (n : ℕ) : st (n+1) =
      (st n).set! (a+n) ((st n).getD (a+n) 0 + (st n).getD n 0) := by
    simp [st, List.range_succ, List.foldl_append, Array.getElem!_eq_getD]
  have hinv (n : ℕ) (hn : n ≤ xs.size-a) : ∀ i, i < xs.size →
      (st n).getD i 0 = if a ≤ i ∧ i < a+n then out.getD i 0 else xs.getD i 0 := by
    induction n with
    | zero => intro i hi; simp [st]
    | succ n ih =>
      have hn' : n ≤ xs.size-a := by omega
      have hidx : a+n < xs.size := by omega
      have hni : n < xs.size := by omega
      have hread : (st n).getD (a+n) 0 = xs.getD (a+n) 0 := by
        rw [ih hn' (a+n) hidx, if_neg (by omega)]
      have hprev : (st n).getD n 0 = out.getD n 0 := by
        rw [ih hn' n hni]
        by_cases han : a ≤ n
        · rw [if_pos (by omega)]
        · rw [if_neg (by omega), hrec n hni, if_neg han, Nat.add_zero]
      have hvalue : (st n).getD (a+n) 0 + (st n).getD n 0 = out.getD (a+n) 0 := by
        rw [hread, hprev, hrec (a+n) hidx, if_pos (by omega), Nat.add_sub_cancel_left]
      intro i hi
      rw [hstep, getD_setNat _ _ i _ (by rwa [hsize]), hvalue]
      by_cases hei : a+n = i
      · rw [if_pos hei]
        subst i
        rw [if_pos (by omega)]
      · rw [if_neg hei, ih hn' i hi]
        by_cases hold : a ≤ i ∧ i < a+n
        · rw [if_pos hold, if_pos (by omega)]
        · rw [if_neg hold, if_neg (by omega)]
  apply list_eq_of_getD
  · rw [Array.length_toList, size_geomStep, geom_length, Array.length_toList]
  · intro i hi
    have hi' : i < xs.size := by simpa only [Array.length_toList, size_geomStep] using hi
    rw [getD_toList]
    change (st (xs.size-a)).getD i 0 = out.getD i 0
    rw [hinv _ le_rfl i hi']
    by_cases hai : a ≤ i
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega), hrec i hi', if_neg hai, Nat.add_zero]

/-- Every hook product in the original computational Hilbert formula is
computed by exactly the same retained coefficient list in the fast version. -/
theorem series_correct (hooks : List ℕ) (len : ℕ) :
    (geomSeries hooks len).toList = series hooks len := by
  have hfold (hooks : List ℕ) (xs : Array ℕ) :
      (hooks.foldl geomStep xs).toList = hooks.foldl geom xs.toList := by
    induction hooks generalizing xs with
    | nil => rfl
    | cons a hooks ih =>
      simp only [List.foldl_cons, ih, geomStep_toList]
  unfold geomSeries series
  rw [hfold]
  congr 1
  cases len with
  | zero => simp [Array.set!]
  | succ n =>
    simp [Array.set!, Array.toList_setIfInBounds, List.replicate_succ]

end Paper20.FastHilbert

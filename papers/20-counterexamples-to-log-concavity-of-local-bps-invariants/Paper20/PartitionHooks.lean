import Paper20.PolynomialLink

namespace Paper20
set_option maxHeartbeats 1000000

/-- A box in a weakly decreasing row list has a positive hook length.
In particular the subtraction in the executable natural formula does not
truncate a genuine hook to zero. -/
theorem hook_positive (ps : List ℕ) (hs : ps.Pairwise (· ≥ ·))
    (i a j : ℕ) (hi : ps[i]? = some a) (hj : j < a) :
    1 ≤ a-j+(ps.filter (· > j)).length-i-1 := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst a
      simp only [List.filter_cons, decide_eq_true_eq, hj, ↓reduceIte,
        List.length_cons]
      omega
    | succ i =>
      have hi' : bs[i]? = some a := by simpa using hi
      have ha : a ∈ bs := List.mem_of_getElem? hi'
      have hjb : j < b := lt_of_lt_of_le hj (hhead a ha)
      have ht := ih htail i hi'
      simp only [List.filter_cons, decide_eq_true_eq, hjb, ↓reduceIte,
        List.length_cons]
      omega

theorem hooksOf_positive (ps : List ℕ) (hs : ps.Pairwise (· ≥ ·)) :
    ∀ a ∈ hooksOf ps, 1 ≤ a := by
  intro h hh
  unfold hooksOf at hh
  obtain ⟨⟨a,i⟩, hai, hmem⟩ := List.mem_flatMap.mp hh
  dsimp only at hmem
  obtain ⟨j, hjrange, rfl⟩ := List.mem_map.mp hmem
  exact hook_positive ps hs i a j (List.mk_mem_zipIdx_iff_getElem?.mp hai)
    (List.mem_range.mp hjrange)

/-- The R-series denominators for every actual enumerated partition are
nonzero by hook positivity, with no additional hook assumption. -/
theorem hooksOf_positive_of_mem_partitionsOf {r : ℕ} {ps : List ℕ}
    (hp : ps ∈ partitionsOf r) : ∀ a ∈ hooksOf ps, 1 ≤ a :=
  hooksOf_positive ps ((mem_partitionsOf r ps).mp hp).2.1

end Paper20

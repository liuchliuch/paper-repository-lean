import Paper20.PartitionHooks

namespace Paper20
set_option maxHeartbeats 1000000

lemma positive_mem_length_le_sum (xs : List ℕ) (hp : ∀ x ∈ xs, 1 ≤ x)
    (a : ℕ) (ha : a ∈ xs) : a+xs.length ≤ xs.sum+1 := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    have hb : 1 ≤ b := hp b (by simp)
    have hp' : ∀ x ∈ xs, 1 ≤ x := fun x hx => hp x (by simp [hx])
    have hlen : xs.length ≤ xs.sum := by
      have aux : ∀ ys : List ℕ, (∀ y ∈ ys, 1 ≤ y) → ys.length ≤ ys.sum := by
        intro ys hy
        induction ys with
        | nil => rfl
        | cons y ys ih =>
          have hy1 := hy y (by simp)
          have hys := ih (fun z hz => hy z (by simp [hz]))
          simp only [List.length_cons, List.sum_cons]
          omega
      exact aux xs hp'
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [List.length_cons, List.sum_cons]
      omega
    · have ht := ih hp' ha
      simp only [List.length_cons, List.sum_cons]
      omega

lemma sum_filter_le_nat (xs : List ℕ) (p : ℕ → Bool) : (xs.filter p).sum ≤ xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp only [List.filter_cons, hp, Bool.false_eq_true,
      ↓reduceIte, List.sum_cons] <;> omega

/-- Every actual hook is bounded by the size, from its box formula. -/
theorem hook_le_sum (ps : List ℕ) (i a j : ℕ) (hi : ps[i]?=some a) (hj : j < a) :
    a-j+(ps.filter (· > j)).length-i-1 ≤ ps.sum := by
  have hamem : a ∈ ps := List.mem_of_getElem? hi
  have ha : a ∈ ps.filter (· > j) := by simp [hamem,hj]
  have hp : ∀ b ∈ ps.filter (· > j), 1 ≤ b := by
    intro b hb
    have hjb := (List.mem_filter.mp hb).2
    simp only [decide_eq_true_eq] at hjb
    omega
  have hlen := positive_mem_length_le_sum _ hp a ha
  have hs := sum_filter_le_nat ps (fun b => b>j)
  omega

theorem hooksOf_le_sum (ps : List ℕ) : ∀ a ∈ hooksOf ps, a ≤ ps.sum := by
  intro h hh
  unfold hooksOf at hh
  obtain ⟨⟨a,i⟩, hai, hmem⟩ := List.mem_flatMap.mp hh
  dsimp only at hmem
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hmem
  exact hook_le_sum ps i a j (List.mk_mem_zipIdx_iff_getElem?.mp hai) (List.mem_range.mp hj)

theorem hooksOf_le_of_mem_partitionsOf {r : ℕ} {ps : List ℕ}
    (hp : ps ∈ partitionsOf r) : ∀ a ∈ hooksOf ps, a ≤ r := by
  have hs := ((mem_partitionsOf r ps).mp hp).1
  simpa only [hs] using hooksOf_le_sum ps

end Paper20

import Paper02.RudinShapiro

/-! Exact endpoint coefficients and the parity-dependent transition count (2.6). -/

noncomputable section

namespace Paper02.RS

lemma coeffsP_ne_nil (m : ℕ) : coeffsP m ≠ [] := by
  intro h
  have := congr_arg List.length h
  rw [coeffsP_length] at this
  simp at this

lemma coeffsQ_ne_nil (m : ℕ) : coeffsQ m ≠ [] := by
  intro h
  have := congr_arg List.length h
  rw [coeffsQ_length] at this
  simp at this

lemma coeffsQ_last (m : ℕ) : (coeffsQ m).getLastD 0 = (-1 : ℝ) ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [coeffsQ_succ, List.getLastD_append_of_ne_nil]
    · have hm : ((coeffsQ m).map (fun x => -x)).getLastD 0 =
          -(coeffsQ m).getLastD 0 := by
        simpa using (List.getLastD_map (f := fun x : ℝ => -x)
          (l := coeffsQ m) (a := 0))
      rw [hm, ih, pow_succ]
      ring
    · simpa using coeffsQ_ne_nil m

lemma coeffsP_last_succ (m : ℕ) :
    (coeffsP (m + 1)).getLastD 0 = (-1 : ℝ) ^ m := by
  rw [coeffsP_succ, List.getLastD_append_of_ne_nil _ _ _ (coeffsQ_ne_nil m),
    coeffsQ_last]

lemma joinTrans_PQ_succ (m : ℕ) :
    joinTrans (coeffsP (m + 1)) (coeffsQ (m + 1)) = if Odd m then 1 else 0 := by
  simp only [joinTrans, coeffsP_ne_nil, coeffsQ_ne_nil, false_or, ↓reduceIte,
    coeffsP_last_succ, coeffsQ_head, mul_one]
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow]
    simp [show ¬Odd m from Nat.not_odd_iff_even.mpr he]
  · rw [ho.neg_one_pow]
    simp [ho]

lemma T_succ_succ (m : ℕ) :
    T (m + 2) = 2 ^ (m + 1) - 1 + if Odd m then 1 else 0 := by
  change transitions (coeffsP ((m + 1) + 1)) = _
  rw [coeffsP_succ, transitions_append]
  change T (m + 1) + U (m + 1) + _ = _
  rw [T_add_U, joinTrans_PQ_succ]

/-- Lemma 2.4, equation (2.6), including both parity cases. -/
theorem T_closed (m : ℕ) (hm : 2 ≤ m) :
    T m = if Odd m then 2 ^ m / 2 else 2 ^ m / 2 - 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 2 := ⟨m - 2, by omega⟩
  rw [T_succ_succ]
  have hpow : 2 ^ (a + 2) / 2 = 2 ^ (a + 1) := by
    rw [show a + 2 = (a + 1) + 1 by omega, pow_succ]
    omega
  have hpar : Odd (a + 2) ↔ Odd a := by
    simp [Nat.odd_iff]
  simp only [hpow, hpar]
  split_ifs with ho
  · have hp := Nat.one_le_two_pow (n := a + 1)
    omega
  · omega

theorem T_closed_odd (m : ℕ) (hm : 2 ≤ m) (ho : Odd m) : T m = 2 ^ m / 2 := by
  rw [T_closed m hm, if_pos ho]

theorem T_closed_even (m : ℕ) (hm : 2 ≤ m) (he : Even m) :
    T m = 2 ^ m / 2 - 1 := by
  rw [T_closed m hm, if_neg (Nat.not_odd_iff_even.mpr he)]

end Paper02.RS

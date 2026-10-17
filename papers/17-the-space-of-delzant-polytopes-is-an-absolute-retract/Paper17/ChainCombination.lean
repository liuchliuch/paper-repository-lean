import Paper17.ChainGeometry

/-! The full finite-chain Minkowski interpolation theorem (Lemma 2.1). -/
noncomputable section
open scoped BigOperators Pointwise
namespace Paper17
namespace DelzantPolytope

/-- Finite positive sums in a refinement chain have the fan of their largest index. -/
theorem exists_positive_chain_sum {n m : ℕ} (P : Fin m → DelzantPolytope n)
    (hchain : ∀ i j : Fin m, i ≤ j → le (P i) (P j))
    (w : Fin m → ℝ) (s : Finset (Fin m)) : s.Nonempty →
    (∀ i ∈ s, 0 < w i) →
    ∃ (j : Fin m) (R : DelzantPolytope n), j ∈ s ∧
      (∀ i ∈ s, i ≤ j) ∧ R.carrier = ∑ i ∈ s, w i • (P i).carrier ∧
      Fan.Equivalent (NormalFan R.val) (NormalFan (P j).val) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro hs; simpa using hs
  | @insert i s hi ih =>
    intro hs hw
    have hwi : 0 < w i := hw i (Finset.mem_insert_self _ _)
    by_cases hs' : s.Nonempty
    · obtain ⟨j, Q, hj, hmax, hQcar, hQfan⟩ := ih hs'
        (fun a ha => hw a (Finset.mem_insert_of_mem ha))
      rcases le_total i j with hij | hji
      · have hPQ : le (P i) Q := Fan.refines_trans hQfan.1 (hchain i j hij)
        obtain ⟨hfan, hdel⟩ := lemma_2_1_pair hPQ hwi (by norm_num : (0:ℝ) < 1)
        let R : DelzantPolytope n := ⟨((P i).val.smul (w i)).add (Q.val.smul 1), hdel⟩
        refine ⟨j, R, Finset.mem_insert_of_mem hj, ?_, ?_, ?_⟩
        · intro a ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact hij
          · exact hmax a ha
        · change (((P i).val.smul (w i)).add (Q.val.smul 1)).carrier = _
          rw [carrier_add_eq, carrier_smul_eq, carrier_smul_eq, one_smul,
            Finset.sum_insert hi]
          exact congrArg (fun K => w i • (P i).carrier + K) hQcar
        · exact ⟨Fan.refines_trans hfan.1 hQfan.1, Fan.refines_trans hQfan.2 hfan.2⟩
      · have hQP : le Q (P i) := Fan.refines_trans (hchain j i hji) hQfan.2
        obtain ⟨hfan, hdel⟩ := lemma_2_1_pair hQP (by norm_num : (0:ℝ) < 1) hwi
        let R : DelzantPolytope n := ⟨(Q.val.smul 1).add ((P i).val.smul (w i)), hdel⟩
        refine ⟨i, R, Finset.mem_insert_self _ _, ?_, ?_, hfan⟩
        · intro a ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact le_rfl
          · exact (hmax a ha).trans hji
        · change ((Q.val.smul 1).add ((P i).val.smul (w i))).carrier = _
          rw [carrier_add_eq, carrier_smul_eq, carrier_smul_eq, one_smul,
            Finset.sum_insert hi]
          rw [show Q.val.carrier = ∑ a ∈ s, w a • (P a).carrier from hQcar]
          exact add_comm _ _
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst hs0
      have hdim : ((P i).val.smul (w i)).IsFullDim := by
        change (interior (((P i).val.smul (w i)).carrier)).Nonempty
        rw [carrier_smul_eq]
        exact (PosBody.smul (w i) hwi.ne' ((P i).val.toPosBody (P i).property.1)).interior_nonempty
      have hdel : IsDelzant ((P i).val.smul (w i)) :=
        ⟨hdim, by rw [normalFan_smul_eq _ hwi]; exact (P i).property.2⟩
      refine ⟨i, ⟨(P i).val.smul (w i), hdel⟩, by simp, ?_, ?_, ?_⟩
      · intro a ha
        have hai : a = i := by simpa using ha
        exact hai.le
      · simp only [Finset.sum_insert, Finset.notMem_empty, not_false_eq_true,
          Finset.sum_empty, add_zero]
        exact carrier_smul_eq _ _
      · rw [normalFan_smul_eq _ hwi]
        exact ⟨Fan.refines_refl _, Fan.refines_refl _⟩

/-- **Lemma 2.1**, including the actual Minkowski carrier and finest normal fan. -/
theorem lemma_2_1 {n k : ℕ} (P : Fin (k + 1) → DelzantPolytope n)
    (hchain : ∀ i j : Fin (k + 1), i.val ≤ j.val → le (P i) (P j))
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ∃ (j : Fin (k + 1)) (R : DelzantPolytope n),
      0 < w j ∧ (∀ i, 0 < w i → i.val ≤ j.val) ∧
      R.carrier = ∑ i, w i • (P i).carrier ∧
      Fan.Equivalent (NormalFan R.val) (NormalFan (P j).val) := by
  classical
  let s : Finset (Fin (k + 1)) := Finset.univ.filter fun i => 0 < w i
  have hs : s.Nonempty := by
    by_contra hn
    have hz : ∀ i, w i = 0 := by
      intro i
      have hnot : ¬ 0 < w i := fun hi => hn ⟨i, by simp [s, hi]⟩
      exact le_antisymm (le_of_not_gt hnot) (hw i)
    simp [hz] at hsum
  obtain ⟨j, R, hj, hmax, hcar, hfan⟩ := exists_positive_chain_sum P
    (fun i j hij => hchain i j hij) w s hs (fun i hi => (Finset.mem_filter.mp hi).2)
  refine ⟨j, R, (Finset.mem_filter.mp hj).2, ?_, ?_, hfan⟩
  · intro i hi
    exact hmax i (by simp [s, hi])
  · rw [hcar]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hwi : w i = 0 :=
      le_antisymm (le_of_not_gt (by simpa [s] using hi)) (hw i)
    rw [hwi]
    exact Set.zero_smul_set (P i).val.nonempty

end DelzantPolytope
end Paper17

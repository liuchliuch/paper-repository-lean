import Paper06.MatchingEvents
import Paper06.ProductEvents
import Paper06.WitnessFull

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-- The increasing representatives exhaust all two-element subsets. -/
theorem ascendingPairs_card (k : ℕ) : (ascendingPairs k).card = k.choose 2 := by
  classical
  have he : (ascendingPairs k).card = ((Finset.univ : Finset (Fin k)).powersetCard 2).card := by
    apply Finset.card_bij (fun p _ => ({p.1, p.2} : Finset (Fin k)))
    · intro p hp
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
        Finset.card_pair (Finset.mem_filter.mp hp).2.ne⟩
    · intro p hp r hr he
      have hp' := (Finset.mem_filter.mp hp).2
      have hr' := (Finset.mem_filter.mp hr).2
      have h1 : p.1 = r.1 ∨ p.1 = r.2 := by
        have hm : p.1 ∈ ({r.1, r.2} : Finset (Fin k)) := by rw [← he]; simp
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
      have h2 : p.2 = r.1 ∨ p.2 = r.2 := by
        have hm : p.2 ∈ ({r.1, r.2} : Finset (Fin k)) := by rw [← he]; simp
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact (hp'.ne (h1.trans h2.symm)).elim
      · exact Prod.ext h1 h2
      · exfalso
        rw [h1, h2] at hp'
        exact (lt_asymm hp' hr').elim
      · exact (hp'.ne (h1.trans h2.symm)).elim
    · intro s hs
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hs).2
      rcases lt_or_gt_of_ne hab with hab | hba
      · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, rfl⟩
      · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba⟩, Finset.pair_comm _ _⟩
  simpa using he

namespace Matching

variable {κ : Type*} [Fintype κ]

/-- Uniform endpoint permutations as an actual finite probability law. -/
noncomputable def permutationLaw : FinProb (Equiv.Perm κ) where
  w _ := (Fintype.card (Equiv.Perm κ) : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_eq_one := by simp [Fintype.card_ne_zero]

/-- The count of internal matching edges among any injectively selected sites. -/
noncomputable def internalEdges {k : ℕ} (f : κ → κ) (selection : Fin k → κ)
    (σ : Equiv.Perm κ) : ℕ :=
  ∑ p ∈ ascendingPairs k,
    if conjugatePartner f σ (selection p.1) = selection p.2 then 1 else 0

theorem internalEdges_cast {k : ℕ} (f : κ → κ) (selection : Fin k → κ)
    (σ : Equiv.Perm κ) :
    (internalEdges f selection σ : ℝ) = ∑ p ∈ ascendingPairs k,
      if conjugatePartner f σ (selection p.1) = selection p.2 then 1 else 0 := by
  simp [internalEdges]

/-- The exact first moment follows from the actual specified-edge probability. -/
theorem internalEdges_mean {k : ℕ} (f : κ → κ) (hnf : ∀ i, f i ≠ i)
    (selection : Fin k → κ) (hselection : Function.Injective selection) :
    (∑ σ : Equiv.Perm κ, permutationLaw.w σ * (internalEdges f selection σ : ℝ)) =
      (k.choose 2 : ℝ) / ((Fintype.card κ : ℝ) - 1) := by
  simp_rw [internalEdges_cast, Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (p : Fin k × Fin k) (hp : p ∈ ascendingPairs k) :
      (∑ σ : Equiv.Perm κ, permutationLaw.w σ *
        (if conjugatePartner f σ (selection p.1) = selection p.2 then (1 : ℝ) else 0)) =
      ((Fintype.card κ : ℝ) - 1)⁻¹ := by
    rw [show (∑ σ : Equiv.Perm κ, permutationLaw.w σ *
        (if conjugatePartner f σ (selection p.1) = selection p.2 then (1 : ℝ) else 0)) =
      permutationProb (fun σ => conjugatePartner f σ (selection p.1) = selection p.2) by
        unfold permutationLaw permutationProb
        dsimp only
        rw [Finset.mul_sum]]
    exact partner_probability f hnf _ _
      (fun h => (Finset.mem_filter.mp hp).2.ne (hselection h))
  rw [Finset.sum_congr rfl he]
  simp [ascendingPairs_card, div_eq_mul_inv]

/-- Distinct ascending edges of an involution cannot share an endpoint. -/
theorem internalEdges_disjoint {k : ℕ} (f : κ → κ) (hf : Function.Involutive f)
    (selection : Fin k → κ) (hselection : Function.Injective selection)
    (σ : Equiv.Perm κ) (p r : Fin k × Fin k)
    (hp : p ∈ ascendingPairs k) (hr : r ∈ ascendingPairs k) (hpr : p ≠ r)
    (h₁ : conjugatePartner f σ (selection p.1) = selection p.2)
    (h₂ : conjugatePartner f σ (selection r.1) = selection r.2) :
    selection p.1 ≠ selection r.1 ∧ selection p.1 ≠ selection r.2 ∧
      selection p.2 ≠ selection r.1 ∧ selection p.2 ≠ selection r.2 := by
  have hp' := (Finset.mem_filter.mp hp).2
  have hr' := (Finset.mem_filter.mp hr).2
  have hinv := conjugatePartner_involutive f hf σ
  have h₁' : conjugatePartner f σ (selection p.2) = selection p.1 := by
    rw [← h₁, hinv]
  have h₂' : conjugatePartner f σ (selection r.2) = selection r.1 := by
    rw [← h₂, hinv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h' : selection p.2 = selection r.2 := by rw [← h₁, ← h₂, h]
    exact hpr (Prod.ext (hselection h) (hselection h'))
  · intro h
    have h' : selection p.2 = selection r.1 := by rw [← h₁, ← h₂', h]
    have hx := hselection h
    have hy := hselection h'
    rw [hx, hy] at hp'
    exact lt_asymm hp' hr'
  · intro h
    have h' : selection p.1 = selection r.2 := by rw [← h₁', ← h₂, h]
    have hx := hselection h
    have hy := hselection h'
    rw [hy, hx] at hp'
    exact lt_asymm hp' hr'
  · intro h
    have h' := hinv.injective (h₁.trans (h₂.trans h.symm).symm)
    exact hpr (Prod.ext (hselection h') (hselection h))

/-- Every two distinct candidate edges have joint probability at most the
specified disjoint-edge probability; overlapping edges contribute zero. -/
theorem internalEdges_pair_probability_le {k : ℕ} (hcard : 4 ≤ Fintype.card κ) (f : κ → κ)
    (hf : Function.Involutive f) (hnf : ∀ i, f i ≠ i)
    (selection : Fin k → κ) (hselection : Function.Injective selection)
    (p r : Fin k × Fin k) (hp : p ∈ ascendingPairs k) (hr : r ∈ ascendingPairs k)
    (hpr : p ≠ r) :
    permutationProb (fun σ => conjugatePartner f σ (selection p.1) = selection p.2 ∧
      conjugatePartner f σ (selection r.1) = selection r.2) ≤
      (((Fintype.card κ : ℝ) - 1) * ((Fintype.card κ : ℝ) - 3))⁻¹ := by
  by_cases hd : selection p.1 ≠ selection r.1 ∧ selection p.1 ≠ selection r.2 ∧
      selection p.2 ≠ selection r.1 ∧ selection p.2 ≠ selection r.2
  · rw [two_edge_probability f hf hnf _ _ _ _
      (fun h => (Finset.mem_filter.mp hp).2.ne (hselection h)) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
      (fun h => (Finset.mem_filter.mp hr).2.ne (hselection h))]
  · have hn : ∀ σ : Equiv.Perm κ,
        ¬ (conjugatePartner f σ (selection p.1) = selection p.2 ∧
          conjugatePartner f σ (selection r.1) = selection r.2) := by
      intro σ h
      exact hd (internalEdges_disjoint f hf selection hselection σ p r hp hr hpr h.1 h.2)
    simp only [permutationProb, hn, if_false, Finset.sum_const_zero, mul_zero]
    have hc : (4 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hcard
    have hn1 : (0 : ℝ) < Fintype.card κ - 1 := by linarith
    have hn3 : (0 : ℝ) < Fintype.card κ - 3 := by linarith
    positivity

/-- The factorial square of a count is the sum over distinct ordered pairs. -/
theorem indicator_factorial {A : Type*} [DecidableEq A] (s : Finset A) (P : A → Prop) :
    (∑ a ∈ s, if P a then (1 : ℝ) else 0) *
      ((∑ a ∈ s, if P a then (1 : ℝ) else 0) - 1) =
      ∑ p ∈ s.offDiag, if P p.1 ∧ P p.2 then (1 : ℝ) else 0 := by
  classical
  have hs : (∑ a ∈ s, if P a then (1 : ℝ) else 0) = ((s.filter P).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hp : (∑ p ∈ s.offDiag, if P p.1 ∧ P p.2 then (1 : ℝ) else 0) =
      ((s.filter P).offDiag.card : ℝ) := by
    have he : s.offDiag.filter (fun p => P p.1 ∧ P p.2) = (s.filter P).offDiag := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_offDiag]
      tauto
    rw [← he]
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hs, hp, Finset.offDiag_card]
  have hn : (s.filter P).card ≤ (s.filter P).card * (s.filter P).card := by nlinarith
  rw [Nat.cast_sub hn, Nat.cast_mul]
  ring

/-- Exact expansion of the internal-edge factorial count into joint events. -/
theorem internalEdges_factorial {k : ℕ} (f : κ → κ) (selection : Fin k → κ)
    (σ : Equiv.Perm κ) :
    (internalEdges f selection σ : ℝ) * ((internalEdges f selection σ : ℝ) - 1) =
      ∑ p ∈ (ascendingPairs k).offDiag,
        if conjugatePartner f σ (selection p.1.1) = selection p.1.2 ∧
          conjugatePartner f σ (selection p.2.1) = selection p.2.2 then (1 : ℝ) else 0 := by
  rw [internalEdges_cast]
  exact indicator_factorial (ascendingPairs k) (fun p =>
    conjugatePartner f σ (selection p.1) = selection p.2)

/-- The actual second factorial moment is bounded using all distinct
candidate pairs. Overlapping pairs have probability zero. -/
theorem internalEdges_second_le {k : ℕ} (hcard : 4 ≤ Fintype.card κ)
    (f : κ → κ) (hf : Function.Involutive f) (hnf : ∀ i, f i ≠ i)
    (selection : Fin k → κ) (hselection : Function.Injective selection) :
    (∑ σ : Equiv.Perm κ, permutationLaw.w σ *
      ((internalEdges f selection σ : ℝ) * ((internalEdges f selection σ : ℝ) - 1))) ≤
      (k.choose 2 : ℝ) * ((k.choose 2 : ℝ) - 1) /
        (((Fintype.card κ : ℝ) - 1) * ((Fintype.card κ : ℝ) - 3)) := by
  simp_rw [internalEdges_factorial, Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (p : (Fin k × Fin k) × (Fin k × Fin k)) :
      (∑ σ : Equiv.Perm κ, permutationLaw.w σ *
        (if conjugatePartner f σ (selection p.1.1) = selection p.1.2 ∧
          conjugatePartner f σ (selection p.2.1) = selection p.2.2 then (1 : ℝ) else 0)) =
      permutationProb (fun σ => conjugatePartner f σ (selection p.1.1) = selection p.1.2 ∧
        conjugatePartner f σ (selection p.2.1) = selection p.2.2) := by
    unfold permutationLaw permutationProb
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs <;> rfl
  simp_rw [he]
  calc
    _ ≤ ∑ p ∈ (ascendingPairs k).offDiag,
        (((Fintype.card κ : ℝ) - 1) * ((Fintype.card κ : ℝ) - 3))⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp₁, hp₂, hne⟩ := Finset.mem_offDiag.mp hp
      exact internalEdges_pair_probability_le hcard f hf hnf selection hselection p.1 p.2 hp₁ hp₂ hne
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.offDiag_card]
      have hm : (ascendingPairs k).card ≤ (ascendingPairs k).card * (ascendingPairs k).card := by nlinarith
      rw [Nat.cast_sub hm, Nat.cast_mul, ascendingPairs_card]
      ring

/-- A coarse factorial-moment bound already yields the exact matching-event
constant under the paper's original `k² ≤ n` hypothesis. -/
theorem internalEdges_positive_probability {k : ℕ} (hn : 6 ≤ Fintype.card κ)
    (hk2 : 2 ≤ k) (hk : k * k ≤ Fintype.card κ)
    (f : κ → κ) (hf : Function.Involutive f) (hnf : ∀ i, f i ≠ i)
    (selection : Fin k → κ) (hselection : Function.Injective selection) :
    3 * ((k : ℝ) * (k - 1) / 2) / (4 * ((Fintype.card κ : ℝ) - 1)) ≤
      permutationProb (fun σ => 0 < internalEdges f selection σ) := by
  let m : ℝ := (k.choose 2 : ℝ)
  let n : ℝ := Fintype.card κ
  have hn6 : (6 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn1 : 0 < n - 1 := by linarith
  have hn3 : 0 < n - 3 := by linarith
  have hkR : (k : ℝ) * k ≤ n := by dsimp [n]; exact_mod_cast hk
  have hk2R : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hm : m = (k : ℝ) * (k - 1) / 2 := Nat.cast_choose_two ℝ k
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hsmall : 2 * (m - 1) ≤ n - 3 := by rw [hm]; nlinarith
  have hmean := internalEdges_mean f hnf selection hselection
  have hsecond := internalEdges_second_le (by omega : 4 ≤ Fintype.card κ) f hf hnf selection hselection
  have hb := FinProb.positive_event_ge_factorial_moments
    (permutationLaw (κ := κ)) (internalEdges f selection)
  rw [hmean] at hb
  have hprob : (FinProb.map permutationLaw (fun σ => decide (0 < internalEdges f selection σ))).w true =
      permutationProb (fun σ => 0 < internalEdges f selection σ) := by
    rw [FinProb.map_w]
    simp only [decide_eq_true_eq]
    unfold permutationLaw permutationProb
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs <;> simp
  rw [hprob] at hb
  change m / (n - 1) - _ / 2 ≤ _ at hb
  change _ ≤ m * (m - 1) / ((n - 1) * (n - 3)) at hsecond
  have herror : m * (m - 1) / ((n - 1) * (n - 3)) / 2 ≤ m / (4 * (n - 1)) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (div_le_iff₀ (mul_pos hn1 hn3)).2
    have he : m / (4 * (n - 1)) * 2 * ((n - 1) * (n - 3)) = m * (n - 3) / 2 := by
      field_simp
      ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hsmall hm0]
  have hhalf := div_le_div_of_nonneg_right hsecond (by norm_num : (0 : ℝ) ≤ 2)
  have hcharge : 3 * m / (4 * (n - 1)) = m / (n - 1) - m / (4 * (n - 1)) := by
    field_simp
    ring
  rw [← hm]
  change 3 * m / (4 * (n - 1)) ≤ _
  rw [hcharge]
  linarith

end Matching
end Paper06

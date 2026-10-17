import Paper06.MatchingFull

open Real Set BigOperators
open scoped Classical

namespace Paper06.Matching

attribute [local instance] sitesDecidableEq

/-- The canonical partner involution on labelled endpoints. -/
def flipEndpoint (m : ℕ) : Equiv.Perm (Sites m) where
  toFun i := (i.1, !i.2)
  invFun i := (i.1, !i.2)
  left_inv i := by cases i with | mk j b => cases b <;> rfl
  right_inv i := by cases i with | mk j b => cases b <;> rfl

theorem flipEndpoint_involutive (m : ℕ) : Function.Involutive (flipEndpoint m) := by
  intro i
  cases i with | mk j b => cases b <;> rfl

theorem flipEndpoint_ne (m : ℕ) (i : Sites m) : flipEndpoint m i ≠ i := by
  cases i with | mk j b => cases b <;> simp [flipEndpoint]

/-- The partner of a site after uniformly relabelling all canonical
endpoints by `σ`. -/
def partner (m : ℕ) (σ : Equiv.Perm (Sites m)) (i : Sites m) : Sites m :=
  σ (flipEndpoint m (σ.symm i))

theorem partner_involutive (m : ℕ) (σ : Equiv.Perm (Sites m)) :
    Function.Involutive (partner m σ) := by
  intro i
  simp [partner, flipEndpoint_involutive m (σ.symm i)]

theorem partner_ne (m : ℕ) (σ : Equiv.Perm (Sites m)) (i : Sites m) :
    partner m σ i ≠ i := by
  intro h
  apply flipEndpoint_ne m (σ.symm i)
  exact σ.injective (by simpa [partner] using h)

theorem partner_relabel (m : ℕ) (σ τ : Equiv.Perm (Sites m)) (i : Sites m) :
    partner m (σ.trans τ) i = τ (partner m σ (τ.symm i)) := rfl

/- The following counting argument works for every fixed-point-free
involution, independently of its coordinate representation. -/
section Counting

variable {κ : Type*} [Fintype κ]

def conjugatePartner (f : κ → κ) (σ : Equiv.Perm κ) (i : κ) : κ :=
  σ (f (σ.symm i))

/-- Probability under a uniformly sampled endpoint permutation. -/
noncomputable def permutationProb (p : Equiv.Perm κ → Prop) : ℝ :=
  (Fintype.card (Equiv.Perm κ) : ℝ)⁻¹ * ∑ σ, if p σ then (1 : ℝ) else 0

theorem permutationProb_nonneg (p : Equiv.Perm κ → Prop) :
    0 ≤ permutationProb p := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem permutationProb_true : permutationProb (fun _ : Equiv.Perm κ => True) = 1 := by
  unfold permutationProb
  simp only [if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast
    (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm κ))))

theorem permutationProb_relabel (τ : Equiv.Perm κ) (p : Equiv.Perm κ → Prop) :
    permutationProb (fun σ => p (σ.trans τ)) = permutationProb p := by
  unfold permutationProb
  congr 1
  let e : Equiv.Perm κ ≃ Equiv.Perm κ :=
    { toFun := fun σ => σ.trans τ
      invFun := fun σ => σ.trans τ.symm
      left_inv := by
        intro σ
        apply Equiv.ext
        intro i
        exact τ.symm_apply_apply (σ i)
      right_inv := by
        intro σ
        apply Equiv.ext
        intro i
        exact τ.apply_symm_apply (σ i) }
  exact e.sum_comp (fun σ => if p σ then (1 : ℝ) else 0)

theorem partner_probability_same (f : κ → κ) (i j k : κ)
    (hij : i ≠ j) (hik : i ≠ k) :
    permutationProb (fun σ => conjugatePartner f σ i = j) =
      permutationProb (fun σ => conjugatePartner f σ i = k) := by
  let τ : Equiv.Perm κ := Equiv.swap j k
  have hτi : τ i = i := Equiv.swap_apply_of_ne_of_ne hij hik
  have hevent : ∀ σ : Equiv.Perm κ,
      (conjugatePartner f (σ.trans τ) i = k) ↔ (conjugatePartner f σ i = j) := by
    intro σ
    change τ (σ (f (σ.symm (τ.symm i)))) = k ↔ _
    have hs : τ.symm i = i := by simpa [τ] using hτi
    rw [hs]
    have hjk : τ j = k := Equiv.swap_apply_left j k
    rw [← hjk, τ.injective.eq_iff]
    rfl
  have h := permutationProb_relabel τ (fun σ => conjugatePartner f σ i = k)
  simpa only [hevent] using h

theorem sum_partner_probability (f : κ → κ) (i : κ) :
    (∑ j : κ, permutationProb (fun σ => conjugatePartner f σ i = j)) = 1 := by
  classical
  unfold permutationProb
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hs : ∀ σ : Equiv.Perm κ,
      (∑ j : κ, @ite ℝ (conjugatePartner f σ i = j)
        (Classical.propDecidable _) 1 0) = 1 := by
    intro σ
    rw [Finset.sum_eq_single (conjugatePartner f σ i)]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  have he : (∑ σ : Equiv.Perm κ, ∑ j : κ,
      @ite ℝ (conjugatePartner f σ i = j) (Classical.propDecidable _) 1 0) =
      ∑ _σ : Equiv.Perm κ, (1 : ℝ) :=
    Finset.sum_congr rfl (fun σ _ => hs σ)
  change (Fintype.card (Equiv.Perm κ) : ℝ)⁻¹ *
    (∑ σ : Equiv.Perm κ, ∑ j : κ, @ite ℝ (conjugatePartner f σ i = j)
      (Classical.propDecidable _) 1 0) = 1
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast
    (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm κ))))

/-- A specified edge occurs with probability `1/(n-1)` in the
uniformly relabelled perfect matching. -/
theorem partner_probability (f : κ → κ) (hf : ∀ i, f i ≠ i)
    (i j : κ) (hij : i ≠ j) :
    permutationProb (fun σ => conjugatePartner f σ i = j) =
      ((Fintype.card κ : ℝ) - 1)⁻¹ := by
  have hdiag : permutationProb (fun σ => conjugatePartner f σ i = i) = 0 := by
    unfold permutationProb
    have hs : ∀ σ : Equiv.Perm κ, conjugatePartner f σ i ≠ i := by
      intro σ h
      apply hf (σ.symm i)
      exact σ.injective (by simpa [conjugatePartner] using h)
    simp [hs]
  have hs := sum_partner_probability f i
  have hrepl : (∑ k : κ, permutationProb (fun σ => conjugatePartner f σ i = k)) =
      (∑ k : κ, if k = i then (0 : ℝ) else
        permutationProb (fun σ => conjugatePartner f σ i = j)) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hki : k = i
    · subst k; simp [hdiag]
    · rw [if_neg hki]
      exact partner_probability_same f i k j (Ne.symm hki) hij
  rw [hrepl] at hs
  have hsum : (∑ k : κ, if k = i then (0 : ℝ) else
      permutationProb (fun σ => conjugatePartner f σ i = j)) =
      ((Fintype.card κ : ℝ) - 1) *
        permutationProb (fun σ => conjugatePartner f σ i = j) := by
    have ht : ∀ k : κ, (if k = i then (0 : ℝ) else
        permutationProb (fun σ => conjugatePartner f σ i = j)) =
        permutationProb (fun σ => conjugatePartner f σ i = j) -
          if k = i then permutationProb (fun σ => conjugatePartner f σ i = j) else 0 := by
      intro k
      by_cases hk : k = i <;> simp [hk]
    simp_rw [ht]
    simp [Finset.sum_sub_distrib, sub_mul]
  rw [hsum] at hs
  exact eq_inv_of_mul_eq_one_right hs

theorem conjugatePartner_involutive (f : κ → κ) (hf : Function.Involutive f)
    (σ : Equiv.Perm κ) : Function.Involutive (conjugatePartner f σ) := by
  intro i
  simp [conjugatePartner, hf (σ.symm i)]

theorem conjugatePartner_ne (f : κ → κ) (hf : ∀ i, f i ≠ i)
    (σ : Equiv.Perm κ) (i : κ) : conjugatePartner f σ i ≠ i := by
  intro h
  apply hf (σ.symm i)
  exact σ.injective (by simpa [conjugatePartner] using h)

theorem two_edge_probability_same (f : κ → κ) (i j k l t : κ)
    (hil : i ≠ l) (hit : i ≠ t) (hjl : j ≠ l) (hjt : j ≠ t)
    (hkl : k ≠ l) (hkt : k ≠ t) :
    permutationProb (fun σ => conjugatePartner f σ i = j ∧ conjugatePartner f σ k = l) =
      permutationProb (fun σ => conjugatePartner f σ i = j ∧ conjugatePartner f σ k = t) := by
  let τ : Equiv.Perm κ := Equiv.swap l t
  have hτi : τ i = i := Equiv.swap_apply_of_ne_of_ne hil hit
  have hτj : τ j = j := Equiv.swap_apply_of_ne_of_ne hjl hjt
  have hτk : τ k = k := Equiv.swap_apply_of_ne_of_ne hkl hkt
  have hevent : ∀ σ : Equiv.Perm κ,
      (conjugatePartner f (σ.trans τ) i = j ∧ conjugatePartner f (σ.trans τ) k = t) ↔
        (conjugatePartner f σ i = j ∧ conjugatePartner f σ k = l) := by
    intro σ
    change (τ (σ (f (σ.symm (τ.symm i)))) = j ∧
      τ (σ (f (σ.symm (τ.symm k)))) = t) ↔ _
    have hsi : τ.symm i = i := by simpa [τ] using hτi
    have hsk : τ.symm k = k := by simpa [τ] using hτk
    rw [hsi, hsk, ← hτj, τ.injective.eq_iff]
    have hlt : τ l = t := Equiv.swap_apply_left l t
    rw [← hlt, τ.injective.eq_iff]
    simp only [hτj, conjugatePartner]
  have h := permutationProb_relabel τ
    (fun σ => conjugatePartner f σ i = j ∧ conjugatePartner f σ k = t)
  simpa only [hevent] using h

theorem sum_two_edge_probability (f : κ → κ) (i j k : κ) :
    (∑ l : κ, permutationProb (fun σ =>
      conjugatePartner f σ i = j ∧ conjugatePartner f σ k = l)) =
      permutationProb (fun σ => conjugatePartner f σ i = j) := by
  unfold permutationProb
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : conjugatePartner f σ i = j
  · simp only [h, true_and, if_true]
    rw [Finset.sum_eq_single (conjugatePartner f σ k)]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp
  · simp [h]

/-- Two specified disjoint edges occur with probability
`1/((n-1)(n-3))`. -/
theorem two_edge_probability (f : κ → κ) (hf : Function.Involutive f)
    (hnf : ∀ i, f i ≠ i) (i j k l : κ)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    permutationProb (fun σ => conjugatePartner f σ i = j ∧ conjugatePartner f σ k = l) =
      (((Fintype.card κ : ℝ) - 1) * ((Fintype.card κ : ℝ) - 3))⁻¹ := by
  let p : κ → ℝ := fun t => permutationProb (fun σ =>
    conjugatePartner f σ i = j ∧ conjugatePartner f σ k = t)
  have hi : p i = 0 := by
    unfold p permutationProb
    have hn : ∀ σ : Equiv.Perm κ,
        ¬ (conjugatePartner f σ i = j ∧ conjugatePartner f σ k = i) := by
      intro σ ⟨h₁, h₂⟩
      have hu := conjugatePartner_involutive f hf σ i
      rw [h₁] at hu
      exact hjk ((conjugatePartner_involutive f hf σ).injective (hu.trans h₂.symm))
    simp [hn]
  have hj : p j = 0 := by
    unfold p permutationProb
    have hn : ∀ σ : Equiv.Perm κ,
        ¬ (conjugatePartner f σ i = j ∧ conjugatePartner f σ k = j) := by
      intro σ ⟨h₁, h₂⟩
      exact hik ((conjugatePartner_involutive f hf σ).injective (h₁.trans h₂.symm))
    simp [hn]
  have hk : p k = 0 := by
    unfold p permutationProb
    have hn : ∀ σ : Equiv.Perm κ,
        ¬ (conjugatePartner f σ i = j ∧ conjugatePartner f σ k = k) := by
      intro σ h
      exact conjugatePartner_ne f hnf σ k h.2
    simp [hn]
  have hsame : ∀ t : κ, t ≠ i → t ≠ j → t ≠ k → p t = p l := by
    intro t hti htj htk
    exact two_edge_probability_same f i j k t l hti.symm hil htj.symm hjl htk.symm hkl
  have hterm : ∀ t : κ, p t = p l -
      (if t = i then p l else 0) - (if t = j then p l else 0) -
      (if t = k then p l else 0) := by
    intro t
    by_cases hti : t = i
    · subst t; simp [hi, hij, hik]
    by_cases htj : t = j
    · subst t; simp [hj, hij.symm, hjk]
    by_cases htk : t = k
    · subst t; simp [hk, hik.symm, hjk.symm]
    simp [hti, htj, htk, hsame t hti htj htk]
  have hs : ((Fintype.card κ : ℝ) - 3) * p l = ((Fintype.card κ : ℝ) - 1)⁻¹ := by
    have hh := sum_two_edge_probability f i j k
    change (∑ t, p t) = _ at hh
    rw [Finset.sum_congr rfl (fun t _ => hterm t)] at hh
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
    rw [partner_probability f hnf i j hij] at hh
    linarith
  have hc : (Fintype.card κ : ℝ) - 3 ≠ 0 := by
    have hfour : 4 ≤ Fintype.card κ := by
      have hcset : ({i, j, k, l} : Finset κ).card = 4 := by simp [hij, hik, hil, hjk, hjl, hkl]
      have := Finset.card_le_card (Finset.subset_univ ({i, j, k, l} : Finset κ))
      simpa only [hcset, Finset.card_univ] using this
    have hh : (4 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hfour
    linarith
  change p l = _
  rw [mul_inv]
  apply (mul_left_cancel₀ hc)
  rw [hs]
  field_simp

theorem matching_single_edge_probability (m : ℕ) (i j : Sites m) (hij : i ≠ j) :
    permutationProb (fun σ => partner m σ i = j) = ((2 * m : ℕ) - 1 : ℝ)⁻¹ := by
  simpa [partner, conjugatePartner, Sites, Fintype.card_prod, mul_comm] using
    partner_probability (flipEndpoint m) (flipEndpoint_ne m) i j hij

theorem matching_two_edge_probability (m : ℕ) (i j k l : Sites m)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    permutationProb (fun σ => partner m σ i = j ∧ partner m σ k = l) =
      (((2 * m : ℕ) - 1 : ℝ) * ((2 * m : ℕ) - 3 : ℝ))⁻¹ := by
  simpa [partner, conjugatePartner, Sites, Fintype.card_prod, mul_comm] using
    two_edge_probability (flipEndpoint m) (flipEndpoint_involutive m)
      (flipEndpoint_ne m) i j k l hij hik hil hjk hjl hkl

end Counting

section Winning

variable {R : Type*} [Fintype R] [CommRing R] [Nontrivial R]

/-- The observed sample contains a complete matching edge. -/
def internalMatching (m : ℕ) (K : Finset (Sites m)) (σ : Equiv.Perm (Sites m)) : Prop :=
  ∃ i ∈ K, partner m σ i ∈ K

/-- The test event: some distinct observed pair satisfies the game
equation. -/
def winningEvent {κ : Type*} [DecidableEq κ] (K : Finset κ) (z : κ → R × R) : Prop :=
  ∃ i ∈ K, ∃ j ∈ K, i ≠ j ∧ (z i).2 + (z j).2 = (z i).1 * (z j).1

theorem canonicalW_edge_ne_zero (m : ℕ) (z : Sites m → R × R)
    (h : canonicalW m z ≠ 0) (i : Sites m) :
    edgeW (z i) (z (flipEndpoint m i)) ≠ 0 := by
  have he : edgeW (z (i.1, false)) (z (i.1, true)) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp h) i.1 (Finset.mem_univ _)
  cases i with
  | mk j b =>
    cases b
    · exact he
    · change edgeW (z (j, true)) (z (j, false)) ≠ 0
      rw [edgeW_symm]
      exact he

theorem matching_edge_wins (m : ℕ) (σ : Equiv.Perm (Sites m))
    (z : Sites m → R × R) (h : canonicalW m (z ∘ σ) ≠ 0) (i : Sites m) :
    (z i).2 + (z (partner m σ i)).2 = (z i).1 * (z (partner m σ i)).1 := by
  have he := canonicalW_edge_ne_zero m (z ∘ σ) h (σ.symm i)
  have he' : edgeW (z i) (z (partner m σ i)) ≠ 0 := by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, partner] using he
  by_contra hn
  exact he' (by simp [edgeW, hn])

theorem internalMatching_forces_winning (m : ℕ) (K : Finset (Sites m))
    (σ : Equiv.Perm (Sites m)) (hσ : internalMatching m K σ)
    (z : Sites m → R × R) (hz : canonicalW m (z ∘ σ) ≠ 0) : winningEvent K z := by
  obtain ⟨i, hi, hj⟩ := hσ
  exact ⟨i, hi, partner m σ i, hj, (partner_ne m σ i).symm,
    matching_edge_wins m σ z hz i⟩

/-- The independent edge law after fixing a matching's endpoint labels. -/
noncomputable def conditionalMatchingLaw (m : ℕ) (σ : Equiv.Perm (Sites m)) :
    FinProb (Sites m → R × R) :=
  reindexLaw σ
    { w := canonicalW m
      nonneg := canonicalW_nonneg m
      sum_eq_one := canonicalW_sum_one m }

theorem conditionalMatching_winning_mass (m : ℕ) (K : Finset (Sites m))
    (σ : Equiv.Perm (Sites m)) (hσ : internalMatching m K σ) :
    Posterior.eventMass (conditionalMatchingLaw (R := R) m σ) (winningEvent K) = 1 := by
  unfold Posterior.eventMass
  have he : (∑ z : Sites m → R × R, if winningEvent K z then
      (conditionalMatchingLaw m σ).w z else 0) =
      ∑ z, (conditionalMatchingLaw (R := R) m σ).w z := by
    apply Finset.sum_congr rfl
    intro z _
    by_cases hw : winningEvent K z
    · simp [hw]
    · have hz : canonicalW m (z ∘ σ) = 0 := by
        by_contra hn
        exact hw (internalMatching_forces_winning m K σ hσ z hn)
      simp [hw, conditionalMatchingLaw, reindexLaw, hz]
  rw [he, (conditionalMatchingLaw m σ).sum_eq_one]

theorem matching_eventMass_average (m : ℕ) (E : (Sites m → R × R) → Prop) :
    Posterior.eventMass (matchingLaw m) E =
      (Fintype.card (Equiv.Perm (Sites m)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Sites m), Posterior.eventMass (conditionalMatchingLaw m σ) E := by
  classical
  unfold Posterior.eventMass
  change (∑ z : Sites m → R × R, if E z then
    (Fintype.card (Equiv.Perm (Sites m)) : ℝ)⁻¹ *
    (∑ σ : Equiv.Perm (Sites m), canonicalW m (z ∘ σ)) else 0) = _
  have he : ∀ z : Sites m → R × R,
      (if E z then (Fintype.card (Equiv.Perm (Sites m)) : ℝ)⁻¹ *
        (∑ σ : Equiv.Perm (Sites m), canonicalW m (z ∘ σ)) else 0) =
      (Fintype.card (Equiv.Perm (Sites m)) : ℝ)⁻¹ *
        (∑ σ : Equiv.Perm (Sites m), if E z then canonicalW m (z ∘ σ) else 0) := by
    intro z
    by_cases h : E z <;> simp [h]
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rfl

/-- A complete internal edge forces the winning test event, so its
actual probability is a lower bound for that event under equation (8). -/
theorem matching_winning_mass_ge_internal (m : ℕ) (K : Finset (Sites m)) :
    permutationProb (internalMatching m K) ≤
      Posterior.eventMass (matchingLaw (R := R) m) (winningEvent K) := by
  rw [matching_eventMass_average]
  unfold permutationProb
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro σ _
  by_cases hσ : internalMatching m K σ
  · rw [if_pos hσ, conditionalMatching_winning_mass m K σ hσ]
  · rw [if_neg hσ]
    unfold Posterior.eventMass
    exact Finset.sum_nonneg (fun z _ => by
      split_ifs
      · exact (conditionalMatchingLaw m σ).nonneg z
      · exact le_refl 0)

end Winning

end Paper06.Matching

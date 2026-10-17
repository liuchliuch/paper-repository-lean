import Paper06.MatchingEvents
import Paper06.ProductEvents
import Paper06.Model
import Paper06.MatchingMoments

open Real Set BigOperators
open scoped Classical

namespace Paper06.Matching

attribute [local instance] sitesDecidableEq

variable {R : Type*} [Fintype R] [Field R]

/-- The winning test on a selected list is exactly the unordered-pair
test on its image in the full coordinate set. -/
theorem winningEvent_selection_iff {κ : Type*} [DecidableEq κ] {k : ℕ}
    (selection : Fin k → κ) (hselection : Function.Injective selection)
    (z : κ → R × R) :
    winningEvent (Finset.univ.image selection) z ↔ somePairWins (z ∘ selection) = true := by
  classical
  simp only [somePairWins, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, j, hj, hij, hwin⟩
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hj
    have hab : a ≠ b := fun h => hij (congrArg selection h)
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact ⟨a, b, hab, hwin⟩
    · refine ⟨b, a, hba, ?_⟩
      change (z (selection b)).2 + (z (selection a)).2 =
        (z (selection b)).1 * (z (selection a)).1
      simpa only [add_comm, mul_comm] using hwin
  · rintro ⟨a, b, hab, hwin⟩
    exact ⟨selection a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩,
      selection b, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩,
      (fun h => hab.ne (hselection h)), hwin⟩

theorem selected_winning_mass_ge_internal {k m : ℕ}
    (selection : Fin k → Sites m) (hselection : Function.Injective selection) :
    permutationProb (internalMatching m (Finset.univ.image selection)) ≤
      (FinProb.map (FinProb.map (matchingLaw (R := R) m)
        (fun z => z ∘ selection)) somePairWins).w true := by
  rw [FinProb.map_comp]
  have h := matching_winning_mass_ge_internal (R := R) m (Finset.univ.image selection)
  convert h using 1
  unfold Posterior.eventMass
  simp only [FinProb.map_w, Function.comp_apply,
    winningEvent_selection_iff selection hselection]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

/-- The first `k` labels, pulled back to the paired endpoint model. -/
noncomputable def sampleSites (n : ℕ) (hn : Even n) (k : ℕ) (hk : k ≤ n) :
    Fin k → Sites (n / 2) :=
  fun i => (evenSitesEquiv n hn).symm ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

theorem sampleSites_injective (n : ℕ) (hn : Even n) (k : ℕ) (hk : k ≤ n) :
    Function.Injective (sampleSites n hn k hk) := by
  intro i j h
  apply Fin.ext
  have hh := (evenSitesEquiv n hn).symm.injective h
  exact congrArg (fun x : Fin n => x.val) hh

/-- The standard marginal's winning probability equals the winning
probability of the selected endpoints in the explicit matching model. -/
theorem marginal_winning_mass_eq (n : ℕ) (hn : Even n) (k : ℕ) (hk : k ≤ n) :
    (FinProb.map (marginal (matchingLawFin (R := R) n hn) k hk) somePairWins).w true =
      (FinProb.map (FinProb.map (matchingLaw (R := R) (n / 2))
        (fun z => z ∘ sampleSites n hn k hk)) somePairWins).w true := by
  classical
  unfold marginal
  rw [FinProb.map_comp, FinProb.map_comp]
  let e := evenSitesEquiv n hn
  let ee : (Fin n → R × R) ≃ (Sites (n / 2) → R × R) :=
    { toFun := fun z => z ∘ e
      invFun := fun z => z ∘ e.symm
      left_inv := by intro z; funext i; simp
      right_inv := by intro z; funext i; simp }
  simp only [FinProb.map_w]
  apply Fintype.sum_equiv ee
  intro z
  have hz : (ee z) ∘ sampleSites n hn k hk =
      (fun i : Fin k => z ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) := by
    funext i
    simp [ee, e, sampleSites, Function.comp_def]
  simp only [Function.comp_apply, hz]
  split_ifs <;> rfl

theorem marginal_winning_mass_ge_internal (n : ℕ) (hn : Even n)
    (k : ℕ) (hk : k ≤ n) :
    permutationProb (internalMatching (n / 2)
      (Finset.univ.image (sampleSites n hn k hk))) ≤
        (FinProb.map (marginal (matchingLawFin (R := R) n hn) k hk) somePairWins).w true := by
  rw [marginal_winning_mass_eq]
  exact selected_winning_mass_ge_internal _ (sampleSites_injective n hn k hk)

theorem permutationProb_mono {κ : Type*} [Fintype κ]
    {p q : Equiv.Perm κ → Prop} (h : ∀ σ, p σ → q σ) :
    permutationProb p ≤ permutationProb q := by
  unfold permutationProb
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro σ _
  by_cases hp : p σ
  · simp [hp, h σ hp]
  · simp only [if_neg hp]
    split_ifs <;> norm_num

theorem internalEdges_pos_implies_internal {k m : ℕ}
    (selection : Fin k → Sites m) (σ : Equiv.Perm (Sites m))
    (h : 0 < internalEdges (flipEndpoint m) selection σ) :
    internalMatching m (Finset.univ.image selection) σ := by
  by_contra hn
  have hz : internalEdges (flipEndpoint m) selection σ = 0 := by
    unfold internalEdges
    apply Finset.sum_eq_zero
    intro p _
    have he : conjugatePartner (flipEndpoint m) σ (selection p.1) ≠ selection p.2 := by
      intro he
      apply hn
      refine ⟨selection p.1, Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩, ?_⟩
      change conjugatePartner (flipEndpoint m) σ (selection p.1) ∈ _
      rw [he]
      exact Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, rfl⟩
    simp [he]
  omega

/-- The actual winning-event lower bound of Proposition 3.4 for the
single matching extension fixed before choosing `k`. -/
theorem matching_marginal_somePairWins_ge (n k : ℕ) (hEven : Even n)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n) (hkk : k * k ≤ n) :
    3 * ((k : ℝ) * (k - 1) / 2) / (4 * ((n : ℝ) - 1)) ≤
      (FinProb.map (marginal (matchingLawFin (R := R) n hEven) k hkn) somePairWins).w true := by
  have hc : Fintype.card (Sites (n / 2)) = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (evenSitesEquiv n hEven)
  have hb := internalEdges_positive_probability
    (κ := Sites (n / 2)) (by simpa only [hc] using hn) hk2 (by simpa only [hc] using hkk)
    (flipEndpoint (n / 2)) (flipEndpoint_involutive _) (flipEndpoint_ne _)
    (sampleSites n hEven k hkn) (sampleSites_injective n hEven k hkn)
  rw [hc] at hb
  exact hb.trans ((permutationProb_mono (fun σ h =>
    internalEdges_pos_implies_internal _ σ h)).trans
      (marginal_winning_mass_ge_internal n hEven k hkn))

end Paper06.Matching

import Paper28.ChainIncidenceSuperlevels

/-! A coordinate permutation cannot move a nonnegative incidence profile
of a face chain to a different profile of that same chain. Its superlevel
sets stay in the chain, and their preserved cardinalities determine them. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {α : Type*} [DecidableEq α]

theorem chainIncidenceProfile_orbit_injective (C : Finset (Finset α))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F)
    (w z : Finset α → ℝ) (hw : ∀ F ∈ C, 0 ≤ w F) (hz : ∀ F ∈ C, 0 ≤ z F)
    (f : α ≃ α) (he : ∀ x, chainIncidenceProfile C z (f x) = chainIncidenceProfile C w x) :
    chainIncidenceProfile C w = chainIncidenceProfile C z := by
  have hChain0 : ∀ F ∈ insert ∅ C, ∀ E ∈ insert ∅ C, F ⊆ E ∨ E ⊆ F := by
    intro F hF E hE
    rcases Finset.mem_insert.mp hF with rfl | hF
    · exact Or.inl (Finset.empty_subset _)
    · rcases Finset.mem_insert.mp hE with rfl | hE
      · exact Or.inr (Finset.empty_subset _)
      · exact hChain F hF E hE
  have hLevels : ∀ a : ℝ, 0 ≤ a → ∀ x,
      a < chainIncidenceProfile C w x ↔ a < chainIncidenceProfile C z x := by
    intro a ha
    obtain ⟨F,hF,hFw⟩ := chainIncidenceProfile_superlevel C w hw hChain a ha
    obtain ⟨E,hE,hEz⟩ := chainIncidenceProfile_superlevel C z hz hChain a ha
    have hMap : F.map f.toEmbedding = E := by
      apply Finset.ext
      intro y
      constructor
      · intro hy
        obtain ⟨x,hx,hxy⟩ := Finset.mem_map.mp hy
        change f x = y at hxy
        apply (hEz y).mp
        have hp := (hFw x).mpr hx
        rw [← he x] at hp
        simpa only [hxy] using hp
      · intro hy
        apply Finset.mem_map.mpr
        refine ⟨f.symm y,?_,f.apply_symm_apply y⟩
        apply (hFw _).mp
        rw [← he,f.apply_symm_apply]
        exact (hEz y).mpr hy
    have hCard : F.card = E.card := (Finset.card_map _).symm.trans (congrArg Finset.card hMap)
    have hFE : F = E := faceChain_card_injective (insert ∅ C) hChain0 hF hE hCard
    intro x
    exact (hFw x).trans (by rw [hFE]; exact (hEz x).symm)
  funext x
  apply le_antisymm
  · apply le_of_not_gt
    intro h
    exact lt_irrefl _ ((hLevels (chainIncidenceProfile C z x) (chainIncidenceProfile_nonneg C z hz x) x).mp h)
  · apply le_of_not_gt
    intro h
    exact lt_irrefl _ ((hLevels (chainIncidenceProfile C w x) (chainIncidenceProfile_nonneg C w hw x) x).mpr h)

end Paper28

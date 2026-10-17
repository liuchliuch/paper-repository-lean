import Paper28.FiniteTranslates
import Mathlib.Data.Finset.Card

/-! The native no-inversions and closed-cell orbit argument for
barycentric face chains. Distinct faces in one chain have different
cardinalities. An equivariant rank-preserving coordinate permutation
therefore cannot identify two distinct weighted points of that cell. -/
set_option autoImplicit false
namespace Paper28
open Set
variable {α : Type*} [DecidableEq α]

theorem faceChain_card_injective (C : Finset (Finset α))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) :
    Set.InjOn Finset.card (C : Set (Finset α)) := by
  intro F hF E hE hCard
  rcases hChain F hF E hE with h | h
  · exact Finset.eq_of_subset_of_card_le h hCard.ge
  · exact (Finset.eq_of_subset_of_card_le h hCard.le).symm

theorem faceChain_preserving_equiv_fixes_faces (C : Finset (Finset α))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F)
    (f : α ≃ α) (hPres : C.image (fun F => F.map f.toEmbedding) = C) :
    ∀ F ∈ C, F.map f.toEmbedding = F := by
  intro F hF
  apply faceChain_card_injective C hChain
  · rw [← hPres]
    exact Finset.mem_image.mpr ⟨F,hF,rfl⟩
  · exact hF
  · exact Finset.card_map _

theorem rank_separated_coordinates_orbit_injective
    {β : Type*} (rank : β → ℕ) (F : Set β) (hRank : Set.InjOn rank F)
    (f : β ≃ β) (hPres : ∀ x, rank (f x) = rank x)
    (u v : β → ℝ) (hu : ∀ x, u x ≠ 0 → x ∈ F) (hv : ∀ x, v x ≠ 0 → x ∈ F)
    (he : ∀ x, v (f x) = u x) : u = v := by
  funext x
  by_cases hux : u x = 0
  · by_cases hvx : v x = 0
    · exact hux.trans hvx.symm
    · have hpre : u (f.symm x) ≠ 0 := by simpa only [← he,f.apply_symm_apply] using hvx
      have hfix : f.symm x = x := hRank (hu _ hpre) (hv _ hvx)
        (by simpa only [f.apply_symm_apply] using (hPres (f.symm x)).symm)
      rw [hfix,hux] at hpre
      exact (hpre rfl).elim
  · have hvf : v (f x) ≠ 0 := by rwa [he]
    have hfix : f x = x := hRank (hv _ hvf) (hu _ hux) (hPres x)
    simpa only [hfix] using (he x).symm

end Paper28

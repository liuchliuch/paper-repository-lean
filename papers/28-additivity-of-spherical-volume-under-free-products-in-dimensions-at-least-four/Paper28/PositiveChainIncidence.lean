import Paper28.ChainIncidenceOrbitInjective

/-! A face with a positive coefficient is recovered exactly as a strict
superlevel set of its chain-incidence profile. Hence a permutation fixing
the profile fixes every such face, including at finite-isotropy points. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {α : Type*} [DecidableEq α]

def chainFaceThreshold (C : Finset (Finset α)) (w : Finset α → ℝ) (F : Finset α) : ℝ :=
  ∑ E ∈ C, if F ⊂ E then w E else 0

theorem chainIncidenceProfile_face_superlevel (C : Finset (Finset α))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F)
    (w : Finset α → ℝ) (hw : ∀ F ∈ C, 0 ≤ w F) (F : Finset α) (hF : F ∈ C) (hWF : 0 < w F) :
    ∀ x, chainFaceThreshold C w F < chainIncidenceProfile C w x ↔ x ∈ F := by
  intro x
  by_cases hx : x ∈ F
  · apply iff_of_true _ hx
    apply Finset.sum_lt_sum
    · intro E hE
      by_cases hFE : F ⊂ E
      · have hxE : x ∈ E := hFE.1 hx
        simp only [if_pos hFE,if_pos hxE]
        exact le_rfl
      · simp only [if_neg hFE]
        split_ifs
        · exact hw E hE
        · exact le_rfl
    · refine ⟨F,hF,?_⟩
      rw [if_neg (ssubset_irrefl F),if_pos hx]
      exact hWF
  · apply iff_of_false _ hx
    apply not_lt_of_ge
    apply Finset.sum_le_sum
    intro E hE
    by_cases hxE : x ∈ E
    · have hFE : F ⊂ E := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
        · rcases hChain F hF E hE with h | h
          · exact h
          · exact (hx (h hxE)).elim
        · intro he
          exact hx (he.symm ▸ hxE)
      simp only [if_pos hxE,if_pos hFE]
      exact le_rfl
    · simp only [if_neg hxE]
      split_ifs
      · exact hw E hE
      · exact le_rfl

theorem positive_chain_profile_stabilizer_fixes_face (C : Finset (Finset α))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F)
    (w : Finset α → ℝ) (hw : ∀ F ∈ C, 0 ≤ w F)
    (f : α ≃ α) (hPres : ∀ x, chainIncidenceProfile C w (f x) = chainIncidenceProfile C w x)
    (F : Finset α) (hF : F ∈ C) (hWF : 0 < w F) : F.map f.toEmbedding = F := by
  have hLevel := chainIncidenceProfile_face_superlevel C hChain w hw F hF hWF
  apply Finset.ext
  intro y
  constructor
  · intro hy
    obtain ⟨x,hx,hxy⟩ := Finset.mem_map.mp hy
    change f x = y at hxy
    apply (hLevel y).mp
    have hh := (hLevel x).mpr hx
    rw [← hPres x] at hh
    simpa only [hxy] using hh
  · intro hy
    apply Finset.mem_map.mpr
    refine ⟨f.symm y,?_,f.apply_symm_apply y⟩
    apply (hLevel _).mp
    rw [← hPres,f.apply_symm_apply]
    exact (hLevel y).mpr hy

end Paper28

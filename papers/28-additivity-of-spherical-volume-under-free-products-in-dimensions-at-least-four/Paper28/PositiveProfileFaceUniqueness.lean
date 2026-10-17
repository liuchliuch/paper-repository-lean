import Paper28.PositiveChainIncidence

/-! The positive faces of a nonnegative incidence profile are intrinsic
to the profile. This gives the native common-face intersection argument
for geometric barycentric cells, rather than an assumed triangulation law. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {α : Type*} [DecidableEq α]

def positiveProfileFaces (C : Finset (Finset α)) (w : Finset α → ℝ) : Finset (Finset α) :=
  C.filter (fun F => 0 < w F)

theorem chainIncidenceProfile_positive_faces (C : Finset (Finset α)) (w : Finset α → ℝ)
    (hw : ∀ F ∈ C, 0 ≤ w F) :
    chainIncidenceProfile (positiveProfileFaces C w) w = chainIncidenceProfile C w := by
  funext x
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro F hF hn
  have hNot : ¬0 < w F := fun h => hn (Finset.mem_filter.mpr ⟨hF,h⟩)
  have hZero : w F = 0 := le_antisymm (not_lt.mp hNot) (hw F hF)
  rw [hZero,ite_self]

theorem positive_profile_face_mem_other
    (C D : Finset (Finset α))
    (hC : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F)
    (hD : ∀ F ∈ D, ∀ E ∈ D, F ⊆ E ∨ E ⊆ F)
    (hFaces : ∀ F ∈ C, F.Nonempty)
    (w z : Finset α → ℝ) (hw : ∀ F ∈ C, 0 ≤ w F) (hz : ∀ F ∈ D, 0 ≤ z F)
    (he : chainIncidenceProfile C w = chainIncidenceProfile D z)
    (F : Finset α) (hF : F ∈ positiveProfileFaces C w) : F ∈ positiveProfileFaces D z := by
  have hFC := (Finset.mem_filter.mp hF).1
  have hWF := (Finset.mem_filter.mp hF).2
  let a := chainFaceThreshold C w F
  have ha : 0 ≤ a := by
    apply Finset.sum_nonneg
    intro E hE
    split_ifs
    · exact hw E hE
    · exact le_rfl
  have hLevelF := chainIncidenceProfile_face_superlevel C hC w hw F hFC hWF
  have hD' : ∀ F ∈ positiveProfileFaces D z, ∀ E ∈ positiveProfileFaces D z, F ⊆ E ∨ E ⊆ F := by
    intro F hF E hE
    exact hD F (Finset.mem_filter.mp hF).1 E (Finset.mem_filter.mp hE).1
  obtain ⟨E,hE,hLevelE⟩ := chainIncidenceProfile_superlevel (positiveProfileFaces D z) z
    (fun F hF => hz F (Finset.mem_filter.mp hF).1) hD' a ha
  have hFE : F = E := by
    apply Finset.ext
    intro x
    have hEq : chainIncidenceProfile C w x = chainIncidenceProfile (positiveProfileFaces D z) z x := by
      rw [chainIncidenceProfile_positive_faces D z hz,he]
    exact (hLevelF x).symm.trans (hEq ▸ hLevelE x)
  rcases Finset.mem_insert.mp hE with hEmpty | hE
  · have hn := hFaces F hFC
    rw [hFE,hEmpty] at hn
    exact hn.ne_empty rfl |>.elim
  · exact hFE.symm ▸ hE

theorem positive_profile_faces_unique
    (C D : Finset (Finset α))
    (hC : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F)
    (hD : ∀ F ∈ D, ∀ E ∈ D, F ⊆ E ∨ E ⊆ F)
    (hCF : ∀ F ∈ C, F.Nonempty) (hDF : ∀ F ∈ D, F.Nonempty)
    (w z : Finset α → ℝ) (hw : ∀ F ∈ C, 0 ≤ w F) (hz : ∀ F ∈ D, 0 ≤ z F)
    (he : chainIncidenceProfile C w = chainIncidenceProfile D z) :
    positiveProfileFaces C w = positiveProfileFaces D z := by
  apply Finset.Subset.antisymm
  · exact fun F hF => positive_profile_face_mem_other C D hC hD hCF w z hw hz he F hF
  · exact fun F hF => positive_profile_face_mem_other D C hD hC hDF z w hz hw he.symm F hF

end Paper28

import Paper28.SignedBarycentricStabilizers
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! Actual barycentric vertices of a nonempty-face chain are linearly
independent. A coordinate in its maximal face outside all smaller faces
recovers the last coefficient, and native finite induction recovers all. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {α : Type*} [DecidableEq α]

theorem chainIncidenceProfile_zero_weights (C : Finset (Finset α))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) (hFaces : ∀ F ∈ C, F.Nonempty)
    (w : Finset α → ℝ) (hZero : ∀ x, chainIncidenceProfile C w x = 0) :
    ∀ F ∈ C, w F = 0 := by
  revert hChain hFaces hZero
  refine Finset.strongInductionOn C ?_
  intro C ih hChain hFaces hZero F hF
  obtain ⟨E,hE,hMax⟩ := finite_face_chain_has_maximum C ⟨F,hF⟩ hChain
  have hExclusive : ∃ g ∈ E, ∀ A ∈ C.erase E, g ∉ A := by
    by_cases hRest : (C.erase E).Nonempty
    · obtain ⟨B,hB,hBMax⟩ := finite_face_chain_has_maximum (C.erase E) hRest
        (fun A hA B hB => hChain A (Finset.mem_of_mem_erase hA) B (Finset.mem_of_mem_erase hB))
      have hBE : B ⊂ E := Finset.ssubset_iff_subset_ne.mpr
        ⟨hMax B (Finset.mem_of_mem_erase hB),(Finset.mem_erase.mp hB).1⟩
      obtain ⟨g,hgE,hgB⟩ := Finset.exists_of_ssubset hBE
      exact ⟨g,hgE,fun A hA hg => hgB (hBMax A hA hg)⟩
    · have hRest0 : C.erase E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hRest
      obtain ⟨g,hg⟩ := hFaces E hE
      exact ⟨g,hg,by intro A hA; simpa only [hRest0,Finset.not_mem_empty] using hA⟩
  obtain ⟨g,hg,hExclusive⟩ := hExclusive
  have hEval : chainIncidenceProfile C w g = w E := by
    unfold chainIncidenceProfile
    rw [Finset.sum_eq_single E]
    · exact if_pos hg
    · intro A hA hAE
      exact if_neg (hExclusive A (Finset.mem_erase.mpr ⟨hAE,hA⟩))
    · intro hn
      exact (hn hE).elim
  have hE0 : w E = 0 := hEval.symm.trans (hZero g)
  have hSmall : ∀ x, chainIncidenceProfile (C.erase E) w x = 0 := by
    intro x
    have he : chainIncidenceProfile (C.erase E) w x+(if x ∈ E then w E else 0) =
        chainIncidenceProfile C w x := Finset.sum_erase_add _ _ hE
    rw [hE0,ite_self,add_zero] at he
    exact he.trans (hZero x)
  by_cases hFE : F = E
  · exact hFE ▸ hE0
  · exact ih (C.erase E) (Finset.erase_ssubset hE)
      (fun A hA B hB => hChain A (Finset.mem_of_mem_erase hA) B (Finset.mem_of_mem_erase hB))
      (fun A hA => hFaces A (Finset.mem_of_mem_erase hA)) hSmall F (Finset.mem_erase.mpr ⟨hFE,hF⟩)

variable {G : Type*} [Group G] [DecidableEq G]

theorem signed_barycentric_centers_linearIndependent (A : Finset G) (C : Finset (Finset G))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) (hFaces : ∀ F ∈ C, F.Nonempty) :
    LinearIndependent ℝ (fun F : C => signedFaceCenter A F.val) := by
  change LinearIndepOn ℝ (signedFaceCenter A) (C : Set (Finset G))
  rw [linearIndepOn_finset_iff]
  intro w hw F hF
  have hZero : ∀ g, chainIncidenceProfile C (fun E => w E*‖signedFaceVector A E‖⁻¹) g = 0 := by
    intro g
    have he := congrArg (fun u : CoordinateHilbert G => u g) hw
    change signedChainRaw A C w g = 0 at he
    rw [signedChainRaw_apply] at he
    have hSign : coordinateSign A g ≠ 0 := by
      intro hz
      have hh := coordinateSign_abs A g
      rw [hz,abs_zero] at hh
      norm_num at hh
    exact (mul_eq_zero.mp he).resolve_left hSign
  have he := chainIncidenceProfile_zero_weights C hChain hFaces _ hZero F hF
  exact (mul_eq_zero.mp he).resolve_right (inv_ne_zero (norm_ne_zero_iff.mpr (signedFaceVector_ne_zero A F (hFaces F hF))))

end Paper28

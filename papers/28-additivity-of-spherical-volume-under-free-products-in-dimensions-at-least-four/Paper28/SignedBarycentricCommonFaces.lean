import Paper28.PositiveProfileFaceUniqueness
import Paper28.SignedBarycentricStabilizers

/-! Actual closed signed barycentric cells intersect precisely in their
common face. Positive coordinate profiles recover the common vertices;
all intersections and coefficients are proved in the native l2 model. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

theorem signedChainRaw_ne_zero_of_unit (A : Finset G) (C : Finset (Finset G)) (w : Finset G → ℝ)
    (hu : ‖signedChainPoint A C w‖ = 1) : signedChainRaw A C w ≠ 0 := by
  intro hz
  simp [signedChainPoint,hz,sphericalNormalize] at hu

theorem signedChainWeights_pos_iff (A : Finset G) (C : Finset (Finset G)) (w : Finset G → ℝ)
    (hu : ‖signedChainPoint A C w‖ = 1) (F : Finset G) (hF : F.Nonempty) :
    0 < signedChainWeights A C w F ↔ 0 < w F := by
  rw [signedChainWeights,mul_pos_iff_of_pos_left
    (inv_pos.mpr (norm_pos_iff.mpr (signedChainRaw_ne_zero_of_unit A C w hu))),
    mul_pos_iff_of_pos_right (inv_pos.mpr (norm_pos_iff.mpr (signedFaceVector_ne_zero A F hF)))]

theorem positive_signedChainWeights_faces (A : Finset G) (C : Finset (Finset G)) (w : Finset G → ℝ)
    (hu : ‖signedChainPoint A C w‖ = 1) (hFaces : ∀ F ∈ C, F.Nonempty) :
    positiveProfileFaces C (signedChainWeights A C w) = positiveProfileFaces C w := by
  apply Finset.ext
  intro F
  by_cases hF : F ∈ C
  · simp only [positiveProfileFaces,Finset.mem_filter,hF,true_and,
      signedChainWeights_pos_iff A C w hu F (hFaces F hF)]
  · simp [positiveProfileFaces,hF]

theorem signed_chain_equal_points_positive_faces
    (A B : Finset G) (C D : Finset (Finset G))
    (hC : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) (hD : ∀ F ∈ D, ∀ E ∈ D, F ⊆ E ∨ E ⊆ F)
    (hCF : ∀ F ∈ C, F.Nonempty) (hDF : ∀ F ∈ D, F.Nonempty)
    (w z : Finset G → ℝ) (hw : ∀ F ∈ C, 0 ≤ w F) (hz : ∀ F ∈ D, 0 ≤ z F)
    (hu : ‖signedChainPoint A C w‖ = 1) (he : signedChainPoint A C w = signedChainPoint B D z) :
    positiveProfileFaces C w = positiveProfileFaces D z := by
  have hv : ‖signedChainPoint B D z‖ = 1 := he ▸ hu
  have hp : chainIncidenceProfile C (signedChainWeights A C w) = chainIncidenceProfile D (signedChainWeights B D z) := by
    funext g
    rw [← signedChainPoint_abs_apply A C w hw,← signedChainPoint_abs_apply B D z hz,he]
  have hh := positive_profile_faces_unique C D hC hD hCF hDF _ _
    (signedChainWeights_nonneg A C w hw) (signedChainWeights_nonneg B D z hz) hp
  rw [positive_signedChainWeights_faces A C w hu hCF,positive_signedChainWeights_faces B D z hv hDF] at hh
  exact hh

theorem signed_chain_equal_points_centers
    (A B : Finset G) (C D : Finset (Finset G))
    (w z : Finset G → ℝ) (hw : ∀ F ∈ C, 0 ≤ w F) (hz : ∀ F ∈ D, 0 ≤ z F)
    (hu : ‖signedChainPoint A C w‖ = 1) (he : signedChainPoint A C w = signedChainPoint B D z)
    (F : Finset G) (hF : F ∈ C) (hFN : F.Nonempty) (hWF : 0 < w F) :
    signedFaceCenter A F = signedFaceCenter B F := by
  have hp : ∀ g, chainIncidenceProfile C (signedChainWeights A C w) g =
      chainIncidenceProfile D (signedChainWeights B D z) g := by
    intro g
    rw [← signedChainPoint_abs_apply A C w hw,← signedChainPoint_abs_apply B D z hz,he]
  have hSign : ∀ g ∈ F, coordinateSign A g = coordinateSign B g := by
    intro g hg
    have hPos := chainIncidenceProfile_pos_of_mem C _ (signedChainWeights_nonneg A C w hw) F hF
      ((signedChainWeights_pos_iff A C w hu F hFN).mpr hWF) g hg
    have hEq := congrArg (fun u : CoordinateHilbert G => u g) he
    change signedChainPoint A C w g = signedChainPoint B D z g at hEq
    rw [signedChainPoint_apply,signedChainPoint_apply,← hp g] at hEq
    exact mul_right_cancel₀ (ne_of_gt hPos) hEq
  unfold signedFaceCenter
  apply congrArg sphericalNormalize
  ext g
  rw [signedFaceVector_apply,signedFaceVector_apply]
  by_cases hg : g ∈ F
  · rw [if_pos hg,if_pos hg,hSign g hg]
  · rw [if_neg hg,if_neg hg]

theorem closedSignedBarycentricCell_mono (A : Finset G) (E C : Finset (Finset G)) (hEC : E ⊆ C) :
    closedSignedBarycentricCell A E ⊆ closedSignedBarycentricCell A C := by
  rintro u ⟨w,hw,hu⟩
  let z : Finset G → ℝ := fun F => if F ∈ E then w F else 0
  refine ⟨z,?_,?_⟩
  · intro F _
    by_cases hF : F ∈ E
    · simpa only [z,if_pos hF] using hw F hF
    · simp [z,hF]
  · have hs : signedChainRaw A C z = signedChainRaw A E w := by
      unfold signedChainRaw
      calc
        _ = ∑ F ∈ E, z F • signedFaceCenter A F :=
          (Finset.sum_subset hEC (fun F _ hF => by simp [z,hF])).symm
        _ = _ := Finset.sum_congr rfl (fun F hF => by simp only [z,if_pos hF])
    rw [signedChainPoint,hs]
    exact hu

theorem closedSignedBarycentricCell_change_signs (A B : Finset G) (E : Finset (Finset G))
    (hEq : ∀ F ∈ E, signedFaceCenter A F = signedFaceCenter B F) :
    closedSignedBarycentricCell A E ⊆ closedSignedBarycentricCell B E := by
  rintro u ⟨w,hw,hu⟩
  refine ⟨w,hw,?_⟩
  have hs : signedChainRaw A E w = signedChainRaw B E w := by
    apply Finset.sum_congr rfl
    intro F hF
    rw [hEq F hF]
  rw [signedChainPoint,← hs]
  exact hu

def signedCommonFaceChain (A : Finset G) (C : Finset (Finset G)) (B : Finset G) (D : Finset (Finset G)) :
    Finset (Finset G) := (C ∩ D).filter (fun F => signedFaceCenter A F = signedFaceCenter B F)

theorem closed_signed_barycentric_cells_intersection (A B : Finset G) (C D : Finset (Finset G))
    (hC : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) (hD : ∀ F ∈ D, ∀ E ∈ D, F ⊆ E ∨ E ⊆ F)
    (hCF : ∀ F ∈ C, F.Nonempty) (hDF : ∀ F ∈ D, F.Nonempty) :
    closedSignedBarycentricCell A C ∩ closedSignedBarycentricCell B D =
      closedSignedBarycentricCell A (signedCommonFaceChain A C B D) := by
  let E := signedCommonFaceChain A C B D
  have hEC : E ⊆ C := fun F hF => (Finset.mem_inter.mp (Finset.mem_filter.mp hF).1).1
  have hED : E ⊆ D := fun F hF => (Finset.mem_inter.mp (Finset.mem_filter.mp hF).1).2
  ext u
  constructor
  · rintro ⟨⟨w,hw,hu⟩,⟨z,hz,hv⟩⟩
    have hUnit : ‖signedChainPoint A C w‖ = 1 := hu ▸ u.property
    have he : signedChainPoint A C w = signedChainPoint B D z := hu.symm.trans hv
    have hPositive := signed_chain_equal_points_positive_faces A B C D hC hD hCF hDF w z hw hz hUnit he
    have hInE : ∀ F ∈ C, 0 < w F → F ∈ E := by
      intro F hF hWF
      have hFD : F ∈ D := by
        have hh : F ∈ positiveProfileFaces D z := hPositive ▸ Finset.mem_filter.mpr ⟨hF,hWF⟩
        exact (Finset.mem_filter.mp hh).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hF,hFD⟩,
        signed_chain_equal_points_centers A B C D w z hw hz hUnit he F hF (hCF F hF) hWF⟩
    refine ⟨w,fun F hF => hw F (hEC hF),?_⟩
    have hs : signedChainRaw A E w = signedChainRaw A C w := by
      apply Finset.sum_subset hEC
      intro F hF hNot
      have hZero : w F = 0 := le_antisymm (not_lt.mp (fun h => hNot (hInE F hF h))) (hw F hF)
      rw [hZero,zero_smul]
    rw [signedChainPoint,hs]
    exact hu
  · intro hu
    exact ⟨closedSignedBarycentricCell_mono A E C hEC hu,
      closedSignedBarycentricCell_mono B E D hED
        (closedSignedBarycentricCell_change_signs A B E (fun F hF => (Finset.mem_filter.mp hF).2) hu)⟩

end Paper28

import Paper28.PositiveChainIncidence
import Paper28.SignedBarycentricQuotientInjection

/-! At an actual relative interior point of a signed barycentric cell,
every stabilizer element fixes its entire closed cell pointwise. The
actual coordinate superlevel sets recover every face and then its signs. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

theorem signedFaceVector_ne_zero (A F : Finset G) (hF : F.Nonempty) : signedFaceVector A F ≠ 0 := by
  obtain ⟨g,hg⟩ := hF
  intro he
  have h := congrArg (fun u : CoordinateHilbert G => u g) he
  change signedFaceVector A F g = 0 at h
  rw [signedFaceVector_apply,if_pos hg] at h
  have ha := coordinateSign_abs A g
  change coordinateSign A g = 0 at h
  rw [h,abs_zero] at ha
  norm_num at ha

theorem chainIncidenceProfile_pos_of_mem {α : Type*} [DecidableEq α]
    (C : Finset (Finset α)) (w : Finset α → ℝ) (hw : ∀ F ∈ C, 0 ≤ w F)
    (F : Finset α) (hF : F ∈ C) (hWF : 0 < w F) (x : α) (hx : x ∈ F) :
    0 < chainIncidenceProfile C w x := by
  apply Finset.sum_pos'
  · intro E hE
    split_ifs
    · exact hw E hE
    · exact le_rfl
  · exact ⟨F,hF,by simpa only [if_pos hx] using hWF⟩

theorem signed_chain_stabilizer_fixes_centers (A : Finset G) (C : Finset (Finset G))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) (hFaces : ∀ F ∈ C, F.Nonempty)
    (w : Finset G → ℝ) (hw : ∀ F ∈ C, 0 < w F) (hu : ‖signedChainPoint A C w‖ = 1)
    (γ : G) (he : leftRegular γ (signedChainPoint A C w) = signedChainPoint A C w) :
    ∀ F ∈ C, leftRegular γ (signedFaceCenter A F) = signedFaceCenter A F := by
  have hw0 : ∀ F ∈ C, 0 ≤ w F := fun F hF => (hw F hF).le
  have hRaw : signedChainRaw A C w ≠ 0 := by
    intro hz
    simp [signedChainPoint,hz,sphericalNormalize] at hu
  have hWeight : ∀ F ∈ C, 0 < signedChainWeights A C w F := by
    intro F hF
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hRaw))
      (mul_pos (hw F hF) (inv_pos.mpr (norm_pos_iff.mpr (signedFaceVector_ne_zero A F (hFaces F hF)))))
  have hWeight0 := signedChainWeights_nonneg A C w hw0
  have hAbs : ∀ g, chainIncidenceProfile C (signedChainWeights A C w) (γ*g) =
      chainIncidenceProfile C (signedChainWeights A C w) g := by
    intro g
    rw [← signedChainPoint_abs_apply A C w hw0,← signedChainPoint_abs_apply A C w hw0]
    have he' := congrArg (fun u : CoordinateHilbert G => |u (γ*g)|) he
    simpa only [leftRegular_apply,inv_mul_cancel_left] using he'.symm
  have hFixed : ∀ F ∈ C, F.map (Equiv.mulLeft γ).toEmbedding = F := by
    intro F hF
    exact positive_chain_profile_stabilizer_fixes_face C hChain _ hWeight0 (Equiv.mulLeft γ) hAbs F hF (hWeight F hF)
  have hSigns : ∀ F ∈ C, ∀ g ∈ F, coordinateSign A (γ*g) = coordinateSign A g := by
    intro F hF g hg
    have hp := chainIncidenceProfile_pos_of_mem C _ hWeight0 F hF (hWeight F hF) g hg
    have hc := congrArg (fun u : CoordinateHilbert G => u (γ*g)) he
    simp only [leftRegular_apply,inv_mul_cancel_left] at hc
    rw [signedChainPoint_apply,signedChainPoint_apply,hAbs] at hc
    exact (mul_right_cancel₀ (ne_of_gt hp) hc).symm
  intro F hF
  have hVec : leftRegular γ (signedFaceVector A F) = signedFaceVector A F := by
    ext g
    rw [leftRegular_apply,signedFaceVector_apply,signedFaceVector_apply]
    have hm : γ⁻¹*g ∈ F ↔ g ∈ F := by
      have hh := (Finset.mem_map_equiv (s := F) (f := Equiv.mulLeft γ) (b := g))
      rw [hFixed F hF] at hh
      exact hh.symm
    by_cases hg : g ∈ F
    · have hpre := hm.mpr hg
      rw [if_pos hpre,if_pos hg]
      simpa only [mul_inv_cancel_left] using (hSigns F hF (γ⁻¹*g) hpre).symm
    · rw [if_neg (fun h => hg (hm.mp h)),if_neg hg]
  exact (sphericalNormalize_map (leftRegular γ) (signedFaceVector A F)).symm.trans
    (congrArg sphericalNormalize hVec)

def strictSignedBarycentricCell (A : Finset G) (C : Finset (Finset G)) : Set (RegularSphere G) :=
  {u | ∃ w : Finset G → ℝ, (∀ F ∈ C, 0 < w F) ∧ u.val = signedChainPoint A C w}

theorem signed_barycentric_interior_stabilizer_fixes_cell (A : Finset G) (C : Finset (Finset G))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) (hFaces : ∀ F ∈ C, F.Nonempty)
    (u : RegularSphere G) (hu : u ∈ strictSignedBarycentricCell A C) (γ : G) (he : γ • u = u) :
    ∀ v ∈ closedSignedBarycentricCell A C, γ • v = v := by
  obtain ⟨w,hw,huw⟩ := hu
  have hNorm : ‖signedChainPoint A C w‖ = 1 := huw ▸ u.property
  have hFix : leftRegular γ (signedChainPoint A C w) = signedChainPoint A C w := by
    rw [← huw]
    exact congrArg Subtype.val he
  have hCenters := signed_chain_stabilizer_fixes_centers A C hChain hFaces w hw hNorm γ hFix
  rintro v ⟨z,_,hv⟩
  apply Subtype.ext
  change leftRegular γ v.val = v.val
  rw [hv,signedChainPoint,← sphericalNormalize_map]
  apply congrArg sphericalNormalize
  rw [signedChainRaw,map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [map_smul,hCenters F hF]

end Paper28

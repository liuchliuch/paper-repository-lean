import Paper28.CoordinateCarrierBarycentricCells

/-! The actual regular action permutes the actual barycentric cells and
preserves their finite-carrier face conditions. Both the coordinate face
combinatorics and the normalized l2 point formulas are checked natively. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

def coordinateCellTranslate (γ : G) (C : Finset (Finset (SignedCoordinate G))) :
    Finset (Finset (SignedCoordinate G)) := C.image (coordinateFaceTranslate γ)

theorem coordinateCrossFace_translate (families : Finset (Finset G))
    (F : Finset (SignedCoordinate G)) (hF : CoordinateCrossFace families F) (γ : G) :
    CoordinateCrossFace families (coordinateFaceTranslate γ F) := by
  refine ⟨hF.1.map,?_,?_⟩
  · rintro g ⟨hT,hFalse⟩
    have hT' : (γ⁻¹*g,true) ∈ F := Finset.mem_map_equiv.mp hT
    have hF' : (γ⁻¹*g,false) ∈ F := Finset.mem_map_equiv.mp hFalse
    exact hF.2.1 (γ⁻¹*g) ⟨hT',hF'⟩
  · obtain ⟨δ,E,hE,hFE⟩ := hF.2.2
    refine ⟨γ*δ,E,hE,?_⟩
    intro g hg
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨x,hx,hxw⟩ := Finset.mem_image.mp (hFE (Finset.mem_image.mpr ⟨w,hw,rfl⟩))
    refine Finset.mem_image.mpr ⟨x,hx,?_⟩
    change (γ*δ)*x = γ*w.1
    rw [mul_assoc,hxw]

theorem coordinateBarycentricCell_translate (families : Finset (Finset G))
    (C : Finset (Finset (SignedCoordinate G))) (hC : CoordinateBarycentricCell families C) (γ : G) :
    CoordinateBarycentricCell families (coordinateCellTranslate γ C) := by
  refine ⟨hC.1.image _,?_,?_⟩
  · intro F hF E hE
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hE
    have hMono : ∀ A B : Finset (SignedCoordinate G), A ⊆ B →
        coordinateFaceTranslate γ A ⊆ coordinateFaceTranslate γ B := by
      intro A B hAB v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hv
      exact Finset.mem_map.mpr ⟨w,hAB hw,rfl⟩
    exact (hC.2.1 P hP Q hQ).imp (hMono P Q) (hMono Q P)
  · intro F hF
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hF
    exact coordinateCrossFace_translate families P (hC.2.2 P hP) γ

theorem closedCoordinateBarycentricCell_smul (γ : G)
    (C : Finset (Finset (SignedCoordinate G))) (u : RegularSphere G)
    (hu : u ∈ closedCoordinateBarycentricCell C) :
    γ • u ∈ closedCoordinateBarycentricCell (coordinateCellTranslate γ C) := by
  obtain ⟨w,hw,hu⟩ := hu
  let e : Finset (SignedCoordinate G) ≃ Finset (SignedCoordinate G) := (signedCoordinateEquiv γ).finsetCongr
  let W : Finset (SignedCoordinate G) → ℝ := fun F => w (e.symm F)
  refine ⟨W,?_,?_⟩
  · intro F hF
    obtain ⟨E,hE,he⟩ := Finset.mem_image.mp hF
    rw [← he]
    change 0 ≤ w (e.symm (e E))
    rw [e.symm_apply_apply]
    exact hw E hE
  · have hs : (∑ F ∈ coordinateCellTranslate γ C, W F • coordinateFaceBarycenter F) =
        leftRegular γ (∑ F ∈ C, w F • coordinateFaceBarycenter F) := by
      change (∑ F ∈ C.image e, w (e.symm F) • coordinateFaceBarycenter F) = _
      rw [Finset.sum_image (fun F _ E _ he => e.injective he),map_sum]
      simp_rw [e.symm_apply_apply]
      apply Finset.sum_congr rfl
      intro F _
      rw [map_smul]
      exact congrArg (fun v => w F • v) (coordinateFaceBarycenter_equivariant γ F).symm
    rw [hs]
    change leftRegular γ u.val = _
    rw [hu,sphericalNormalize_map]

end Paper28

import Paper28.FiniteCarrierDescent
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The actual finite-coordinate quotient carrier is a finite union of
images of compact finite-dimensional coordinate spheres. Compactness is
proved without assuming a quotient triangulation or local compactness of
the entire infinite-dimensional quotient. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set Metric
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

def regularCoordinateSphere (F : Finset G) : Set (RegularSphere G) :=
  {u | u.val ∈ coordinateSupportSubspace F}

theorem coordinateSphere_isCompact (F : Finset G) : IsCompact (coordinateSphere F) := by
  have hc : IsCompact (sphere (0 : coordinateSupportSubspace F) 1) := isCompact_sphere _ _
  have he : Subtype.val '' sphere (0 : coordinateSupportSubspace F) 1 = coordinateSphere F := by
    ext u
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨by simpa only [mem_sphere,dist_zero_right] using hv,v.property⟩
    · rintro ⟨hn,hu⟩
      refine ⟨⟨u,hu⟩,?_,rfl⟩
      simpa only [mem_sphere,dist_zero_right] using hn
  rw [← he]
  exact hc.image continuous_subtype_val

theorem regularCoordinateSphere_isCompact (F : Finset G) : IsCompact (regularCoordinateSphere F) := by
  rw [Subtype.isCompact_iff]
  have he : Subtype.val '' regularCoordinateSphere F = coordinateSphere F := by
    ext u
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨v.property,hv⟩
    · rintro ⟨hn,hu⟩
      exact ⟨⟨u,hn⟩,hu,rfl⟩
  rw [he]
  exact coordinateSphere_isCompact F

theorem quotientFiniteCarrier_eq_finite_union (families : Finset (Finset G)) :
    quotientFiniteCarrier families = ⋃ E ∈ families, regularQuotientMap '' regularCoordinateSphere E := by
  ext q
  constructor
  · rintro ⟨u,⟨γ,E,hE,_,hu⟩,rfl⟩
    let v : RegularSphere G := γ⁻¹ • u
    have hv : v ∈ regularCoordinateSphere E := by
      intro g hg
      change (leftRegular γ⁻¹ u.val) g = 0
      rw [leftRegular_apply,inv_inv]
      apply hu (γ*g)
      intro hh
      obtain ⟨x,hx,hxg⟩ := Finset.mem_image.mp hh
      exact hg ((mul_left_cancel hxg) ▸ hx)
    exact mem_iUnion.mpr ⟨E,mem_iUnion.mpr ⟨hE,v,hv,regularQuotientMap_smul γ⁻¹ u⟩⟩
  · intro hq
    obtain ⟨E,hE⟩ := mem_iUnion.mp hq
    obtain ⟨hEF,u,hu,rfl⟩ := mem_iUnion.mp hE
    exact coordinateSphere_mem_quotientFiniteCarrier families E hEF u hu

theorem quotientFiniteCarrier_isCompact (families : Finset (Finset G)) :
    IsCompact (quotientFiniteCarrier families) := by
  rw [quotientFiniteCarrier_eq_finite_union]
  exact families.finite_toSet.isCompact_biUnion (fun E _ =>
    (regularCoordinateSphere_isCompact E).image regularQuotientMap_continuous)

end Paper28

import Paper28.SignedBarycentricCoordinateProfiles

/-! The actual regular orbit quotient is injective on every closed signed
barycentric face-chain cell. This includes its boundary faces and is proved
from the actual l2 coordinate formula rather than assumed as cell data. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type*} [Group G] [DecidableEq G]

def closedSignedBarycentricCell (A : Finset G) (C : Finset (Finset G)) : Set (RegularSphere G) :=
  {u | ∃ w : Finset G → ℝ, (∀ F ∈ C, 0 ≤ w F) ∧ u.val = signedChainPoint A C w}

theorem signed_barycentric_cell_quotient_injective (A : Finset G) (C : Finset (Finset G))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) :
    Set.InjOn (regularQuotientMap : RegularSphere G → RegularOrbitQuotient G) (closedSignedBarycentricCell A C) := by
  rintro u ⟨w,hw,hu⟩ v ⟨z,hz,hv⟩ hq
  have hOrbit : u ∈ MulAction.orbit G v := Quotient.exact hq
  obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp hOrbit
  have he : leftRegular γ (signedChainPoint A C z) = signedChainPoint A C w := by
    rw [← hv,← hu]
    exact congrArg Subtype.val hγ
  apply Subtype.ext
  rw [hu,hv]
  exact (signed_chain_point_orbit_injective A C hChain z w hz hw γ he).symm

end Paper28

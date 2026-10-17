import Paper28.SphericalPolyhedralCurrents
import Paper28.PolyhedralSupportDeformation

/-! Original Lemma 5.1 for the actual spherical quotient and the source
finite integer polyhedral-current subgroup, relative to the disclosed AK
current/integration object signatures and standard round metric realization.
The entire relative deformation and all its estimates are local proofs. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe u v
variable {G : Type u} [Group G] [DecidableEq G] [Countable G]

theorem lemma_5_1 (M : SphericalQuotientMetricInput G)
    (I : CompactIntegralCurrentSupportInput.{u,v} (RegularOrbitQuotient G) M.metric)
    (S : SphericalSimplexIntegrationInput M I)
    (K : Set (RegularOrbitQuotient G)) (hK : IsCompact K)
    (k : ℕ) (C : I.Current k) (hC : C ∈ sphericalPolyhedralCurrents S k)
    (_hZK : I.support C ⊆ K) (η : ℝ) (hη : 0 < η) :
    letI := M.metric
    Nonempty (RelativeCarrierDeformation K (I.support C) ⟨1+η,by linarith⟩) := by
  obtain ⟨F,hF⟩ := sphericalPolyhedral_support_cover S k C hC
  apply relative_deformation_of_spherical_simplex_cover M K (I.support C) hK
    (fun _ : F => k) (fun σ i => (σ.val.vertices i).val)
    (fun σ => σ.val.center) (fun σ => σ.val.hemisphere)
    (fun σ => σ.val.coordinates) (fun σ => σ.val.supported) ?_ η hη
  intro z hz
  obtain ⟨σ,hσ⟩ := mem_iUnion.mp (hF hz)
  obtain ⟨hσF,hzσ⟩ := mem_iUnion.mp hσ
  exact mem_iUnion.mpr ⟨⟨σ,hσF⟩,hzσ⟩

end Paper28

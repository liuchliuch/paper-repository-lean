import Paper28.SphericalSimplexPatch

/-! Source spherical-simplex support covers give the precise finite-piece
relative hypothesis, including arbitrary subdivisions and cancellations.
The deformation depends only on this cover, not on chosen coefficients. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G A : Type*} [Group G] [DecidableEq G] [Countable G] [Fintype A]

theorem relative_deformation_of_spherical_simplex_cover
    (M : SphericalQuotientMetricInput G) (K Z : Set (RegularOrbitQuotient G)) (hK : IsCompact K)
    (k : A → ℕ) (v : ∀ a, Fin (k a+1) → CoordinateHilbert G)
    (c : A → CoordinateHilbert G) (hHemisphere : ∀ a i, 0 < inner ℝ (c a) (v a i))
    (S : A → Finset G) (hS : ∀ a i, v a i ∈ coordinateSupportSubspace (S a))
    (hZ : Z ⊆ ⋃ a, regularQuotientMap ''
      {u : RegularSphere G | u.val ∈ sphericalSimplexPatch (v a)})
    (η : ℝ) (hη : 0 < η) :
    letI := M.metric
    Nonempty (RelativeCarrierDeformation K Z ⟨1+η,by linarith⟩) := by
  let P := fun a => sphericalSimplexPatch (v a)
  apply relative_deformation_of_finite_support_pieces M K Z hK P
    (fun a => sphericalSimplexPatch_isCompact (v a) (c a) (hHemisphere a))
    (fun a => sphericalSimplexPatch_unit (v a) (c a) (hHemisphere a)) S
    (fun a => sphericalSimplexPatch_mem_subspace (v a) (coordinateSupportSubspace (S a)) (hS a))
    ?_ η hη
  intro z hz
  obtain ⟨a,ha⟩ := mem_iUnion.mp (hZ hz)
  obtain ⟨u,hu,huz⟩ := ha
  refine ⟨u,huz,a,1,u.val,hu,?_⟩
  exact leftRegular_one u.val

end Paper28

import Paper28.SignedBarycentricStabilizers
import Paper28.StabilizerFixedRoundChart

/-! Actual quotient local round isometry along signed barycentric cells,
including finite-isotropy strata. It follows from the actual stabilizer
pointwise fixing and native orbit separation, not a chart-isometry input. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type*} [Group G] [DecidableEq G] [Countable G]

theorem signed_barycentric_cell_quotient_locally_round
    (M : SphericalQuotientMetricInput G) (A : Finset G) (C : Finset (Finset G))
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) (hFaces : ∀ F ∈ C, F.Nonempty)
    (u : RegularSphere G) (hu : u ∈ strictSignedBarycentricCell A C) :
    ∃ r : ℝ, 0 < r ∧ ∀ v ∈ closedSignedBarycentricCell A C, ∀ w ∈ closedSignedBarycentricCell A C,
      dist v u < r → dist w u < r →
      @dist (RegularOrbitQuotient G) M.metric.toDist (regularQuotientMap v) (regularQuotientMap w) =
        angular v.val w.val := by
  apply spherical_quotient_locally_round_on_stabilizer_fixed_set M _ u
  intro γ hγ w hw
  have he : γ • u = u := Subtype.ext hγ
  exact congrArg Subtype.val (signed_barycentric_interior_stabilizer_fixes_cell A C hChain hFaces u hu γ he w hw)

end Paper28

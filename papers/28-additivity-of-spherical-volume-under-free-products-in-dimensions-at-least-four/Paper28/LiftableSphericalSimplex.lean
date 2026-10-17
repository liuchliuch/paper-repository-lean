import Paper28.SphericalSimplexPatch

/-! The source geometric generators: finite-coordinate spherical geodesic
simplices in a common open hemisphere, injectively projected and locally
isometrically projected along their relative interiors. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type*} [Group G] [DecidableEq G] [Countable G]

structure LiftableSphericalSimplex (M : SphericalQuotientMetricInput G) (k : ℕ) where
  vertices : Fin (k+1) → RegularSphere G
  independent : LinearIndependent ℝ (fun i => (vertices i).val)
  coordinates : Finset G
  supported : ∀ i, (vertices i).val ∈ coordinateSupportSubspace coordinates
  center : CoordinateHilbert G
  hemisphere : ∀ i, 0 < inner ℝ center (vertices i).val
  quotient_injective : Set.InjOn regularQuotientMap
    {u : RegularSphere G | u.val ∈ sphericalSimplexPatch (fun i => (vertices i).val)}
  quotient_locally_isometric : ∀ t : stdSimplex ℝ (Fin (k+1)), (∀ i, 0 < t.val i) →
    ∀ u : RegularSphere G,
      u.val = sphericalNormalize (sphericalBarycentricVector (fun i => (vertices i).val) t) →
      ∃ r : ℝ, 0 < r ∧ ∀ v w : RegularSphere G,
        v.val ∈ sphericalSimplexPatch (fun i => (vertices i).val) →
        w.val ∈ sphericalSimplexPatch (fun i => (vertices i).val) →
        dist v u < r → dist w u < r →
        @dist (RegularOrbitQuotient G) M.metric.toDist (regularQuotientMap v) (regularQuotientMap w) =
          angular v.val w.val

def LiftableSphericalSimplex.projectedPatch {M : SphericalQuotientMetricInput G} {k : ℕ}
    (σ : LiftableSphericalSimplex M k) : Set (RegularOrbitQuotient G) :=
  regularQuotientMap '' {u : RegularSphere G |
    u.val ∈ sphericalSimplexPatch (fun i => (σ.vertices i).val)}

end Paper28

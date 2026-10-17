import Paper28.LiftableSphericalSimplex
import Paper28.FiniteTranslates
import Paper28.ProjectionErrorNeighborhood

/-! Actual projected source-simplex intersections involve only the
explicit finite coordinate-overlap translates. This connects the native
support finiteness to actual quotient geometry and later transfer descent. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type*} [Group G] [DecidableEq G] [Countable G]
  {M : SphericalQuotientMetricInput G} {k l : ℕ}

def LiftableSphericalSimplex.liftedPatch (τ : LiftableSphericalSimplex M k) : Set (RegularSphere G) :=
  {u | u.val ∈ sphericalSimplexPatch (fun i => (τ.vertices i).val)}

theorem LiftableSphericalSimplex.liftedPatch_supported (τ : LiftableSphericalSimplex M k)
    (u : RegularSphere G) (hu : u ∈ τ.liftedPatch) : u.val ∈ coordinateSupportSubspace τ.coordinates :=
  sphericalSimplexPatch_mem_subspace (fun i => (τ.vertices i).val) _ τ.supported hu

theorem liftable_simplex_overlap_translation (τ : LiftableSphericalSimplex M k) (σ : LiftableSphericalSimplex M l)
    (u v : RegularSphere G) (hu : u ∈ τ.liftedPatch) (hv : v ∈ σ.liftedPatch)
    (γ : G) (he : γ • v = u) : γ ∈ overlapTranslations τ.coordinates σ.coordinates := by
  obtain ⟨g,hg⟩ := unit_has_nonzero_coordinate u
  have huS := τ.liftedPatch_supported u hu
  have hvS := σ.liftedPatch_supported v hv
  have hgτ : g ∈ τ.coordinates := by by_contra h; exact hg (huS g h)
  have hEval : v.val (γ⁻¹*g) = u.val g := by
    have hh := congrArg (fun w : RegularSphere G => w.val g) he
    exact hh
  have hgσ : γ⁻¹*g ∈ σ.coordinates := by
    by_contra h
    have hz := hvS (γ⁻¹*g) h
    exact hg (hEval.symm.trans hz)
  exact (mem_overlapTranslations τ.coordinates σ.coordinates γ).mpr
    ⟨g,hgτ,γ⁻¹*g,hgσ,by simp⟩

theorem projected_liftable_simplex_intersection (τ : LiftableSphericalSimplex M k) (σ : LiftableSphericalSimplex M l) :
    τ.projectedPatch ∩ σ.projectedPatch = ⋃ γ ∈ overlapTranslations τ.coordinates σ.coordinates,
      regularQuotientMap '' (τ.liftedPatch ∩ (fun v : RegularSphere G => γ • v) '' σ.liftedPatch) := by
  ext q
  constructor
  · rintro ⟨⟨u,hu,huq⟩,⟨v,hv,hvq⟩⟩
    have hOrbit : u ∈ MulAction.orbit G v := Quotient.exact (huq.trans hvq.symm)
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp hOrbit
    exact mem_iUnion.mpr ⟨γ,mem_iUnion.mpr
      ⟨liftable_simplex_overlap_translation τ σ u v hu hv γ hγ,u,⟨hu,v,hv,hγ⟩,huq⟩⟩
  · intro hq
    obtain ⟨γ,hγ⟩ := mem_iUnion.mp hq
    obtain ⟨_,u,⟨hu,v,hv,hvu⟩,huq⟩ := mem_iUnion.mp hγ
    refine ⟨⟨u,hu,huq⟩,v,hv,?_⟩
    exact (regularQuotientMap_smul γ v).symm.trans ((congrArg regularQuotientMap hvu).trans huq)

end Paper28

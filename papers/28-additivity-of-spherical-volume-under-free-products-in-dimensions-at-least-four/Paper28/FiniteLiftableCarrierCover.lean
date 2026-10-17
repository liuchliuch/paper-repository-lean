import Paper28.BarycentricCellSimplexRealization
import Paper28.FiniteQuotientBarycentricCover

/-! The actual finite carrier is exactly a finite union of actual source
liftable geodesic simplex patches. Their finite support, independence,
hemispheres, quotient injection and local roundness are all native proofs. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G] [Countable G]

theorem finite_carrier_liftable_simplex_cover (M : SphericalQuotientMetricInput G)
    (families : Finset (Finset G)) :
    ∃ cells : Finset (Σ k : ℕ, LiftableSphericalSimplex M k),
      quotientFiniteCarrier families = ⋃ τ ∈ cells, τ.2.projectedPatch := by
  let R := coordinateCarrierCellRepresentatives families
  have hEx : ∀ C : R, ∃ k : ℕ, ∃ τ : LiftableSphericalSimplex M k,
      τ.projectedPatch = regularQuotientMap '' closedCoordinateBarycentricCell C.val := by
    intro C
    exact coordinate_barycentric_cell_projected_liftable_realization M families C.val (Finset.mem_filter.mp C.property).2
  choose k τ hτ using hEx
  let T : R → Σ k : ℕ, LiftableSphericalSimplex M k := fun C => ⟨k C,τ C⟩
  refine ⟨Finset.univ.image T,?_⟩
  ext q
  constructor
  · intro hq
    obtain ⟨C,hC,hqC⟩ := quotient_carrier_finite_barycentric_cover families q hq
    let c : R := ⟨C,hC⟩
    have hqτ : q ∈ (T c).2.projectedPatch := by
      change q ∈ (τ c).projectedPatch
      rw [hτ c]
      exact hqC
    exact mem_iUnion.mpr ⟨T c,mem_iUnion.mpr
      ⟨Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩,hqτ⟩⟩
  · intro hq
    obtain ⟨S,hS⟩ := mem_iUnion.mp hq
    obtain ⟨hS,hqS⟩ := mem_iUnion.mp hS
    obtain ⟨C,_,he⟩ := Finset.mem_image.mp hS
    rw [← he] at hqS
    change q ∈ (τ C).projectedPatch at hqS
    rw [hτ C] at hqS
    exact coordinate_barycentric_cell_patch_subset_carrier families C.val (Finset.mem_filter.mp C.property).2 hqS

end Paper28

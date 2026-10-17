import Paper28.InvariantCoordinates
import Paper28.RelativeNormalization

/-! Actual finite coordinate subspaces and spherical carriers of (12).
Finite dimensionality and the carrier property of the constructed normalized
projection are proved in the native regular l2 Hilbert space. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G : Type*} [Group G] [DecidableEq G]

def coordinateSupportSubspace (F : Finset G) : Submodule ℝ (CoordinateHilbert G) where
  carrier := {u | ∀ g ∉ F, u g = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv g hg
    change u g + v g = 0
    rw [hu g hg,hv g hg,add_zero]
  smul_mem' := by
    intro a u hu g hg
    change a * u g = 0
    rw [hu g hg,mul_zero]

def supportCoefficientMap (F : Finset G) : coordinateSupportSubspace F →ₗ[ℝ] (F → ℝ) where
  toFun u g := u.val g.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem supportCoefficientMap_injective (F : Finset G) : Function.Injective (supportCoefficientMap F) := by
  intro u v huv
  apply Subtype.ext
  ext g
  by_cases hg : g ∈ F
  · exact congrArg (fun f : F → ℝ => f ⟨g,hg⟩) huv
  · exact (u.property g hg).trans (v.property g hg).symm

instance coordinateSupportSubspace_finiteDimensional (F : Finset G) :
    FiniteDimensional ℝ (coordinateSupportSubspace F) :=
  FiniteDimensional.of_injective (supportCoefficientMap F) (supportCoefficientMap_injective F)

theorem coordinateSupportSubspace_mono (F E : Finset G) (hFE : F ⊆ E) :
    coordinateSupportSubspace F ≤ coordinateSupportSubspace E := by
  intro u hu g hg
  exact hu g (fun h => hg (hFE h))

theorem l2CoordinateProjection_mem (F : Finset G) (u : CoordinateHilbert G) :
    l2CoordinateProjection F u ∈ coordinateSupportSubspace F := by
  intro g hg
  rw [l2CoordinateProjection_apply,if_neg hg]

def coordinateSphere (F : Finset G) : Set (CoordinateHilbert G) :=
  {u | ‖u‖ = 1 ∧ u ∈ coordinateSupportSubspace F}

/-- The lifted union in formula (12), on the actual regular Hilbert sphere. -/
def liftedFiniteCarrier (families : Finset (Finset G)) : Set (CoordinateHilbert G) :=
  {u | ∃ γ : G, ∃ F ∈ families, u ∈ coordinateSphere (F.image (fun g => γ*g))}

variable {J : Type*} [Fintype J]

/-- The explicit normalized projection on a finite lifted neighborhood lies
in one actual finite coordinate subspace, whose coordinates are the union
of the finitely many active projection coordinates. -/
theorem normalizedProjection_finite_support (φ : J → CoordinateHilbert G → ℝ)
    (F : J → Finset G) (u : CoordinateHilbert G) :
    normalizedProjection φ (fun j => l2CoordinateProjectionCLM (F j)) u ∈
      coordinateSupportSubspace (Finset.univ.biUnion F) := by
  apply normalizedProjection_mem
  intro j
  apply coordinateSupportSubspace_mono (F j) (Finset.univ.biUnion F)
    (Finset.subset_biUnion_of_mem F (Finset.mem_univ j))
  exact l2CoordinateProjection_mem (F j) u

end Paper28

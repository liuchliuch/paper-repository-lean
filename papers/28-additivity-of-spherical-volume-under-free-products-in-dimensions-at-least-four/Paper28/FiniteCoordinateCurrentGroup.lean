import Paper28.GlobalCurrentPushforwardInput
import Paper28.CoordinateCarrierCompact

/-! The actual additive subgroup of sphere currents supported in some
finite coordinate sphere. Supports under addition, cancellation and
boundary give the subgroup and its boundary natively. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type} [Group G] [DecidableEq G]
  (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)

def finiteCoordinateSupportedCurrents (k : ℕ) : AddSubgroup (J.Current k) where
  carrier := {C | ∃ F : Finset G, J.support C ⊆ regularCoordinateSphere F}
  zero_mem' := ⟨∅,by rw [J.support_zero]; exact empty_subset _⟩
  add_mem' := by
    rintro C D ⟨F,hF⟩ ⟨E,hE⟩
    refine ⟨F ∪ E,?_⟩
    intro x hx
    rcases J.support_add_subset C D hx with hx | hx
    · exact coordinateSupportSubspace_mono F (F ∪ E) Finset.subset_union_left (hF hx)
    · exact coordinateSupportSubspace_mono E (F ∪ E) Finset.subset_union_right (hE hx)
  neg_mem' := fun h => by
    obtain ⟨F,hF⟩ := h
    exact ⟨F,(J.support_neg_subset _).trans hF⟩

def finiteCoordinateBoundary (k : ℕ) :
    finiteCoordinateSupportedCurrents J (k+1) →+ finiteCoordinateSupportedCurrents J k where
  toFun C := ⟨J.boundary k C.val,by
    obtain ⟨F,hF⟩ := C.property
    exact ⟨F,(J.support_boundary_subset k C.val).trans hF⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' C D := Subtype.ext (map_add _ _ _)

end Paper28

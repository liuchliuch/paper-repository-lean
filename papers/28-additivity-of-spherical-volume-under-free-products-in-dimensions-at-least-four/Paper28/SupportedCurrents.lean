import Paper28.CurrentChainComplex

/-! The actual subgroup of compact currents supported in a prescribed
neighborhood and its native boundary complex. This keeps local pushforwards
honest about the domains on which the actual deformation is defined. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
universe u v
variable {X : Type u} {metric : MetricSpace X}

def supportedCurrents (I : CompactIntegralCurrentAlgebraInput.{u,v} X metric)
    (U : Set X) (k : ℕ) : AddSubgroup (I.Current k) where
  carrier := {C | I.support C ⊆ U}
  zero_mem' := by
    change I.support (0 : I.Current k) ⊆ U
    rw [I.support_zero]
    exact empty_subset _
  add_mem' := fun hC hD => (I.support_add_subset _ _).trans (union_subset hC hD)
  neg_mem' := fun hC => (I.support_neg_subset _).trans hC

def supportedBoundary (I : CompactIntegralCurrentAlgebraInput.{u,v} X metric)
    (U : Set X) (k : ℕ) : supportedCurrents I U (k+1) →+ supportedCurrents I U k where
  toFun C := ⟨I.boundary k C.val,(I.support_boundary_subset k C.val).trans C.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' C D := Subtype.ext (map_add _ _ _)

theorem supportedBoundary_squared_zero (I : CompactIntegralCurrentAlgebraInput.{u,v} X metric)
    (U : Set X) (k : ℕ) (C : supportedCurrents I U (k+2)) :
    supportedBoundary I U k (supportedBoundary I U (k+1) C) = 0 :=
  Subtype.ext (I.boundary_squared_zero k C.val)

def supportedCurrentChainComplex (I : CompactIntegralCurrentAlgebraInput.{u,v} X metric)
    (U : Set X) : ChainComplex AddCommGrpCat.{v} ℕ :=
  ChainComplex.of (fun k => AddCommGrpCat.of (supportedCurrents I U k))
    (fun k => AddCommGrpCat.ofHom (supportedBoundary I U k)) (by
      intro k
      ext C
      exact congrArg Subtype.val (supportedBoundary_squared_zero I U k C))

def supportedCurrentInclusion (I : CompactIntegralCurrentAlgebraInput.{u,v} X metric)
    (U : Set X) : supportedCurrentChainComplex I U ⟶ compactCurrentChainComplex I :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun k => AddCommGrpCat.ofHom (supportedCurrents I U k).subtype) (by
    intro k
    rfl)

end Paper28

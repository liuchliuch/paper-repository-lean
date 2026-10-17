import Paper18.Category.ModuleFunctorDualDimensionBlockSimple

/-! # A simple regular bimodule forces actual module-action connectivity -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonoidalLeftAction
universe v u w
namespace Paper18.Category.ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [BraidedCategory D] [RightRigidCategory D]
  {R : D} [MonObj R] (S : SeparableAlgebra R)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton D ι)
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
attribute [local instance] MonoidalOppositeFusion.rightRigidCategory
attribute [local instance] Preadditive.hasEqualizers_of_hasKernels
local instance blockConnectedBaseFiniteLimits : HasFiniteLimits (Mod_ D R) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

variable [Simple (wattsRegular (R := R))]

/-- Every genuine component projector is nonzero. If the regular bimodule
is simple, its actual inclusion is invertible, so every module belongs
to that component. -/
theorem property_of_regular_bimodule_simple (j : S.SimpleIndex T) (X : Mod_ D R) :
    ModuleComponent.property (C := Dᴹᵒᵖ) (S.skeleton T) j X := by
  letI := orbitBlockBimodule_simple S T j
  have hn : orbitBlockInclusion S T j ≠ 0 := by
    intro hz
    apply CategoryTheory.id_nonzero (orbitBlockBimodule S T j)
    rw [← (orbitBlockRetract S T j).retract]
    change orbitBlockInclusion S T j ≫ _ = 0
    rw [hz, zero_comp]
  letI : IsIso (orbitBlockInclusion S T j) := CategoryTheory.isIso_of_mono_of_nonzero hn
  have heq : wattsEvaluation.map (componentProjectionCounit (S.skeleton T) j) =
      orbitBlockInclusion S T j ≫ (wattsEvaluationUnitIso (R := R)).inv := by
    simp only [orbitBlockInclusion, assoc, Iso.hom_inv_id, comp_id]
  letI : IsIso (wattsEvaluation.map (componentProjectionCounit (S.skeleton T) j)) := by
    rw [heq]
    infer_instance
  letI := wattsEvaluation_full S
  letI := wattsEvaluation_faithful S
  letI : IsIso (componentProjectionCounit (S.skeleton T) j) :=
    isIso_of_fully_faithful wattsEvaluation _
  let e := (forget (C := Dᴹᵒᵖ) (M := Mod_ D R) (N := Mod_ D R)).mapIso
    (asIso (componentProjectionCounit (S.skeleton T) j))
  have hY : ModuleComponent.property (C := Dᴹᵒᵖ) (S.skeleton T) j
      ((componentProjectionEnd (S.skeleton T) j).toFunctor.obj X) :=
    ((componentProjection (C := Dᴹᵒᵖ) (S.skeleton T) j).toFunctor.obj X).property
  exact IsAdditiveFullProperty.of_iso (ModuleComponent.property (C := Dᴹᵒᵖ) (S.skeleton T) j)
    (e.app X).symm hY

/-- The actual action is retract connected, derived from the actual simple
regular bimodule rather than from a dimension or irreducibility certificate. -/
theorem module_connected_of_regular_bimodule_simple (j k : S.SimpleIndex T) :
    ∃ X : Dᴹᵒᵖ, Nonempty (Retract ((S.skeleton T).simpleObject k)
      (X ⊙ₗ (S.skeleton T).simpleObject j)) := by
  have h := property_of_regular_bimodule_simple S T j ((S.skeleton T).simpleObject k)
  exact (ModuleComponent.sameComponent_iff_simpleStep (S.skeleton T) j k).mp
    ((ModuleComponent.property_simple_iff (S.skeleton T) j k).mp h)

end Paper18.Category.ModuleFunctor

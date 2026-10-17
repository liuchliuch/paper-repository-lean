import Paper18.Category.ModuleFunctorSemisimpleWattsFullyFaithful
import Paper18.Category.ModuleFunctorSemisimpleFoundation
import Paper18.Category.ModuleFunctorSemisimpleImage

/-! # Actual finite semisimple module endofunctors of a separable algebra

Full faithfulness of actual regular-algebra evaluation, its actual
preservation of monomorphisms, and the derived actual bimodule skeleton
construct a finite semisimple skeleton of module endofunctors. No
semisimplicity or Eilenberg--Watts conclusion is supplied as input.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [RightRigidCategory Dᴹᵒᵖ]
  {R : D} [MonObj R]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
attribute [local instance] Preadditive.hasEqualizers_of_hasKernels
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

local instance wattsBase_finiteLimits : HasFiniteLimits (Mod_ D R) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

instance wattsEvaluation_additive : (wattsEvaluation (R := R)).Additive where
  map_add := by intros; apply Mod_.Hom.ext; rfl
instance wattsEvaluation_linear : (wattsEvaluation (R := R)).Linear ℂ where
  map_smul _ _ := by apply Mod_.Hom.ext; rfl

/-- Actual evaluation preserves monomorphisms because the actual
forgetful functor preserves kernels and the ordinary evaluation does. -/
instance wattsEvaluation_preservesMonomorphisms :
    (wattsEvaluation (R := R)).PreservesMonomorphisms where
  preserves {F G} τ _ := by
    letI : Mono τ.val := underlying_mono τ
    letI : Mono (τ.val.app (Mod_.regular R)) := inferInstance
    exact (Mod_.forget (D := Mod_ D R) (mop R)).mono_of_mono_map
      (inferInstanceAs (Mono (τ.val.app (Mod_.regular R))))

variable (S : SeparableAlgebra R) {ι : Type w} [Fintype ι]
  (T : FiniteSemisimpleSkeleton D ι)

/-- The finite set of actual simple module-endofunctor classes. -/
def WattsSimpleIndex := by
  letI : ∀ F G : Bundled Dᴹᵒᵖ (Mod_ D R) (Mod_ D R), FiniteDimensional ℂ (F ⟶ G) :=
    finiteDimensionalHom (S.skeleton T)
  letI := wattsEvaluation_faithful S
  letI := wattsEvaluation_full S
  exact ImageSimpleIndex (bimoduleSkeleton S T) (wattsEvaluation (R := R))

instance wattsSimpleIndex_fintype : Fintype (WattsSimpleIndex S T) := by
  letI : ∀ F G : Bundled Dᴹᵒᵖ (Mod_ D R) (Mod_ D R), FiniteDimensional ℂ (F ⟶ G) :=
    finiteDimensionalHom (S.skeleton T)
  unfold WattsSimpleIndex
  infer_instance

/-- Every actual monomorphism of actual module endofunctors splits,
through the derived actual bimodule splitting and actual fullness. -/
def wattsEndSplitMono {F G : Bundled Dᴹᵒᵖ (Mod_ D R) (Mod_ D R)} (f : F ⟶ G) [Mono f] :
    SplitMono f := by
  letI := wattsEvaluation_faithful S
  letI := wattsEvaluation_full S
  exact imageSplitMono (bimoduleSkeleton S T) (wattsEvaluation (R := R)) f

/-- The actual finite semisimple skeleton of strong additive linear
module endofunctors of the category of actual separable-algebra modules. -/
def wattsEndSkeleton :
    FiniteSemisimpleSkeleton (Bundled Dᴹᵒᵖ (Mod_ D R) (Mod_ D R)) (WattsSimpleIndex S T) := by
  letI : ∀ F G : Bundled Dᴹᵒᵖ (Mod_ D R) (Mod_ D R), FiniteDimensional ℂ (F ⟶ G) :=
    finiteDimensionalHom (S.skeleton T)
  letI := wattsEvaluation_faithful S
  letI := wattsEvaluation_full S
  exact imageSkeleton (bimoduleSkeleton S T) (wattsEvaluation (R := R))

end Paper18.Category.ModuleFunctor

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

/-- The finite actual simple classes in the braided ambient specialization. -/
abbrev BraidedWattsSimpleIndex := WattsSimpleIndex S T

/-- A braided right rigid ambient category provides the required actual
right rigidity of its monoidal opposite, so this specialization needs no
extra acting-category structure from the caller. -/
def braidedWattsEndSkeleton :
    FiniteSemisimpleSkeleton (Bundled Dᴹᵒᵖ (Mod_ D R) (Mod_ D R))
      (BraidedWattsSimpleIndex S T) := wattsEndSkeleton S T

end Paper18.Category.ModuleFunctor

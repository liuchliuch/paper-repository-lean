import Paper18.Category.InternalModuleAmbientActionLinear
import Paper18.Category.FixedBoundaryModuleStrong

/-! # The actual free-module functor respects the ambient module action -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A]

attribute [local instance] ambientMonoidalOppositeLeftAction

/-- The ambient category with its native right tensor action, expressed
as a left action of the monoidal opposite. -/
def ambientBaseAction : MonoidalLeftAction Cᴹᵒᵖ C :=
  MonoidalLeftAction.monoidalOppositeLeftAction C C

attribute [local instance] ambientBaseAction

/-- Reassociation gives the actual lax module structure of free modules. -/
def freeFunctorLaxLeftLinear : (freeFunctor (A := A)).LaxLeftLinear Cᴹᵒᵖ where
  μₗ X Y := (RelativeTensor.ambientFreeIso Y X.unmop).hom
  μₗ_naturality_left f Y := by
    apply Mod_.Hom.ext
    change ((A ⊗ Y) ◁ f.unmop) ≫ (α_ A Y _).hom =
      (α_ A Y _).hom ≫ (A ◁ (Y ◁ f.unmop))
    exact associator_naturality_right A Y f.unmop
  μₗ_naturality_right X Y Y' f := by
    apply Mod_.Hom.ext
    change (A ◁ f) ▷ X.unmop ≫ (α_ A Y' X.unmop).hom =
      (α_ A Y X.unmop).hom ≫ (A ◁ f ▷ X.unmop)
    exact associator_naturality_middle A f X.unmop
  μₗ_associativity X Y Z := by
    apply Mod_.Hom.ext
    change (α_ A Z (Y.unmop ⊗ X.unmop)).hom ≫
        (A ◁ (α_ Z Y.unmop X.unmop).inv) =
      (α_ (A ⊗ Z) Y.unmop X.unmop).inv ≫
        (α_ A Z Y.unmop).hom ▷ X.unmop ≫ (α_ A (Z ⊗ Y.unmop) X.unmop).hom
    monoidal
  μₗ_unitality Y := by
    apply Mod_.Hom.ext
    change (ρ_ (A ⊗ Y)).hom = (α_ A Y (𝟙_ C)).hom ≫ (A ◁ (ρ_ Y).hom)
    exact rightUnitor_tensor_hom A Y

/-- The native free-module functor is actually strong for the right
ambient tensor action. -/
def freeFunctorLeftLinear : (freeFunctor (A := A)).LeftLinear Cᴹᵒᵖ := by
  letI := freeFunctorLaxLeftLinear (A := A)
  letI (X : Cᴹᵒᵖ) (Y : C) :
      IsIso (Functor.LaxLeftLinear.μₗ (freeFunctor (A := A)) X Y) :=
    (RelativeTensor.ambientFreeIso Y X.unmop).isIso_hom
  exact ModuleFunctor.leftLinearOfLax (freeFunctor (A := A))

end Paper18.Category.InternalModule

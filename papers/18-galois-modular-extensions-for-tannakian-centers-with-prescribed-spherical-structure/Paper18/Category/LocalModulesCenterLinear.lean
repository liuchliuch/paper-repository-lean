import Paper18.Category.LocalModulesCenterEquivalence
import Paper18.Category.DrinfeldLinear

/-! # Complex linearity of the actual central module functors -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

namespace RelativeTensor
instance centralFreeFunctorAdditive : (centralFreeFunctor (A := A)).Additive where
  map_add {X Y} f g := by
    apply Center.ext
    apply Mod_.Hom.ext
    change A ◁ (f + g) = (A ◁ f) + (A ◁ g)
    simp

instance centralFreeFunctorLinear : (centralFreeFunctor (A := A)).Linear ℂ where
  map_smul f r := by
    apply Center.ext
    apply Mod_.Hom.ext
    change A ◁ (r • f) = r • (A ◁ f)
    simp
end RelativeTensor

namespace SeparableAlgebra
variable (S : SeparableAlgebra A)
instance localCenterFunctorAdditive : S.localCenterFunctor.Additive where
  map_add := by intros; apply Center.ext; rfl

instance localCenterFunctorLinear : S.localCenterFunctor.Linear ℂ where
  map_smul := by intros; apply Center.ext; rfl

instance localCentralizerFunctorAdditive : S.localCentralizerFunctor.Additive where
  map_add := by intros; apply Center.ext; rfl

instance localCentralizerFunctorLinear : S.localCentralizerFunctor.Linear ℂ where
  map_smul := by intros; apply Center.ext; rfl
end SeparableAlgebra
end Paper18.Category

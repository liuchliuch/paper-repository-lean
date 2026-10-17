import Paper18.Category.InternalModuleAmbientAction
import Paper18.Category.SeparableModulesLinear
import Paper18.Category.ModuleAlphaInductionOpposite

/-! # Linearity of the actual ambient action on internal modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj
universe v u
namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {A : C} [MonObj A]

attribute [local instance] ambientMonoidalOppositeLeftAction

instance ambientActionLeft_additive (X : Cᴹᵒᵖ) :
    (MonoidalLeftAction.actionLeft (Mod_ C A) X).Additive where
  map_add {M N} f g := by
    apply Mod_.Hom.ext
    change (f.hom + g.hom) ▷ X.unmop = f.hom ▷ X.unmop + g.hom ▷ X.unmop
    exact (tensorRight X.unmop).map_add

instance ambientActionLeft_linear (X : Cᴹᵒᵖ) :
    (MonoidalLeftAction.actionLeft (Mod_ C A) X).Linear ℂ where
  map_smul f r := by
    apply Mod_.Hom.ext
    change (r • f.hom) ▷ X.unmop = r • (f.hom ▷ X.unmop)
    exact (tensorRight X.unmop).map_smul r f.hom

instance ambientActionRight_additive (M : Mod_ C A) :
    (MonoidalLeftAction.actionRight Cᴹᵒᵖ M).Additive where
  map_add {X Y} f g := by
    apply Mod_.Hom.ext
    change M.X ◁ (f.unmop + g.unmop) = M.X ◁ f.unmop + M.X ◁ g.unmop
    exact (tensorLeft M.X).map_add

instance ambientActionRight_linear (M : Mod_ C A) :
    (MonoidalLeftAction.actionRight Cᴹᵒᵖ M).Linear ℂ where
  map_smul f r := by
    apply Mod_.Hom.ext
    change M.X ◁ (r • f.unmop) = r • (M.X ◁ f.unmop)
    exact (tensorLeft M.X).map_smul r f.unmop

end Paper18.Category.InternalModule

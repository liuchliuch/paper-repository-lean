import Paper18.Category.GraphPicardMoritaCentralBraided
import Paper18.Category.DrinfeldLinear

/-! # Actual additivity and complex linearity of the Morita central lift -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.GraphPicard
variable (D : Type u) [Category.{v} D] [MonoidalCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  [∀ m : M, (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).Additive]
  [∀ m : M, (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).Linear ℂ]

instance rightCentralLiftAdditive : (rightCentralLift D M).Additive where
  map_add {Z W} f g := by
    apply Center.ext
    apply ModuleFunctor.bundled_hom_ext
    ext m
    change (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).map (f.f.mop + g.f.mop) =
      (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).map f.f.mop +
        (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).map g.f.mop
    exact (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).map_add

instance rightCentralLiftLinear : (rightCentralLift D M).Linear ℂ where
  map_smul f r := by
    apply Center.ext
    apply ModuleFunctor.bundled_hom_ext
    ext m
    change (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).map (r • f.f.mop) =
      r • (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).map f.f.mop
    exact (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).map_smul r _

instance rightCentralActionAdditive : (rightCentralAction D M).Additive :=
  inferInstanceAs (rightCentralLift D M ⋙
    Center.forget (ModuleAlphaInduction.End Dᴹᵒᵖ M)).Additive

instance rightCentralActionLinear : (rightCentralAction D M).Linear ℂ :=
  inferInstanceAs ((rightCentralLift D M ⋙
    Center.forget (ModuleAlphaInduction.End Dᴹᵒᵖ M)).Linear ℂ)

end Paper18.Category.GraphPicard

import Paper18.Category.GraphPicardMoritaCentralTensor

/-! # The actual Morita central lift is strong monoidal

The underlying tensor comparisons are precisely those of the already
constructed right central action. Their centrality is proved separately;
faithful forgetting then reflects the pentagon and the two unit laws.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u vM uM
namespace Paper18.Category.GraphPicard
variable (D : Type u) [Category.{v} D] [MonoidalCategory D]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

@[simp] theorem rightCentralTensorLiftIso_hom_f (Z W : Center D) :
    (rightCentralTensorLiftIso D M Z W).hom.f = (rightCentralTensorIso D M Z W).hom := rfl

@[simp] theorem rightCentralUnitLiftIso_hom_f :
    (rightCentralUnitLiftIso D M).hom.f = (rightCentralUnitIso D M).hom := rfl

/-- The actual central lift has the same genuine strong tensor structure
as its actual underlying right central action. -/
instance rightCentralLiftMonoidal : (rightCentralLift D M).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := rightCentralUnitLiftIso D M
      μIso := rightCentralTensorLiftIso D M
      μIso_hom_natural_left {Z W} f V := by
        apply Center.ext
        exact rightCentralTensorIso_naturality_left D M f V
      μIso_hom_natural_right {Z W} V f := by
        apply Center.ext
        exact rightCentralTensorIso_naturality_right D M V f
      associativity Z W V := by
        apply Center.ext
        exact Functor.LaxMonoidal.associativity (rightCentralAction D M) Z W V
      left_unitality Z := by
        apply Center.ext
        exact Functor.LaxMonoidal.left_unitality (rightCentralAction D M) Z
      right_unitality Z := by
        apply Center.ext
        exact Functor.LaxMonoidal.right_unitality (rightCentralAction D M) Z }

end Paper18.Category.GraphPicard

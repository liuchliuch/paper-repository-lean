import Paper18.Category.GraphPicardMoritaCentralMonoidal

/-! # The precise reversed braiding of the actual Morita central lift

With the native tensor convention F ⊗ G = F ⋙ G, the actual right central
lift preserves the reversed source braiding. The original source and all
ambient global braidings are unchanged.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.GraphPicard
variable (D : Type u) [Category.{v} D] [MonoidalCategory D]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

/-- The genuine central lift is braided with the reversed source
braiding dictated by native endofunctor composition. -/
def rightCentralLiftReverseBraided :
    letI : BraidedCategory (Center D) := reverseBraiding (Center D)
    (rightCentralLift D M).Braided := by
  letI : BraidedCategory (Center D) := reverseBraiding (Center D)
  refine { toMonoidal := rightCentralLiftMonoidal D M, braided := ?_ }
  intro Z W
  have hmu (U V : Center D) :
      (Functor.LaxMonoidal.μ (rightCentralLift D M) U V).f =
      (rightCentralTensorIso D M U V).hom := rfl
  apply Center.ext
  simp only [Center.comp_f, hmu]
  dsimp only [reverseBraiding]
  apply ModuleFunctor.bundled_hom_ext
  ext m
  change (rightCentralTensorIso D M Z W).hom.val.app m ≫
      (Center.braiding W Z).inv.f.mop ⊵ₗ m =
    Functor.OplaxLeftLinear.δₗ
      (ModuleAlphaInduction.centralFunctor (M := M) (centerOpposite.obj W)) (mop Z.1) m ≫
        (rightCentralTensorIso D M W Z).hom.val.app m
  rw [Center.braiding_inv_f, rightCentralTensorIso_hom_app, rightCentralTensorIso_hom_app,
    ModuleAlphaInduction.central_δ]
  dsimp only [ModuleAlphaInduction.centralLineator, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, MonoidalLeftAction.actionRight_map,
    centerOpposite, oppositeHalfBraiding]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

end Paper18.Category.GraphPicard

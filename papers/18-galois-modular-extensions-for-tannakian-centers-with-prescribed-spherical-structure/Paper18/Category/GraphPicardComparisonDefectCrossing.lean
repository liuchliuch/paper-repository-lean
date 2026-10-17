import Paper18.Category.GraphPicardCapShuffle

/-! # The actual same-negative crossing under the Morita central action -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.GraphPicard
variable (D : Type u) [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]

/-- Reversing the center braiding cancels the reversal in the actual
negative embedding. This is an explicit local braided structure. -/
def negativeToReverseCenterBraided :
    letI : BraidedCategory (Center D) := reverseBraiding (Center D)
    (Drinfeld.negative D).Braided := by
  letI : BraidedCategory (Center D) := reverseBraiding (Center D)
  refine { toMonoidal := Drinfeld.negative_monoidal D, braided := ?_ }
  intro X Y
  apply Center.Hom.ext
  change 𝟙 _ ≫ (β_ X Y).hom =
    (Center.braiding ((Drinfeld.negative D).obj Y)
      ((Drinfeld.negative D).obj X)).inv.f ≫ 𝟙 _
  rw [Center.braiding_inv_f]
  change 𝟙 _ ≫ (β_ X Y).hom = (β_ X Y).hom ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

variable (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

/-- The genuine negative action has a genuine central lift to the native
module-endofunctor category, with the original source braiding. -/
def negativeMoritaCentralLift : D ⥤ Center (ModuleAlphaInduction.End Dᴹᵒᵖ M) :=
  Drinfeld.negative D ⋙ rightCentralLift D M

instance negativeMoritaCentralLiftMonoidal : (negativeMoritaCentralLift D M).Monoidal := by
  unfold negativeMoritaCentralLift
  infer_instance

instance negativeMoritaCentralLiftBraided : (negativeMoritaCentralLift D M).Braided := by
  letI : BraidedCategory (Center D) := reverseBraiding (Center D)
  letI : (Drinfeld.negative D).Braided := negativeToReverseCenterBraided D
  letI : (rightCentralLift D M).Braided := rightCentralLiftReverseBraided D M
  unfold negativeMoritaCentralLift
  infer_instance

/-- The actual same-negative half-braiding is the original source
braiding transported by the actual negative action tensorators. -/
lemma negativeMoritaCentralLift_braiding (X Y : D) :
    Functor.LaxMonoidal.μ (Drinfeld.negative D ⋙ rightCentralAction D M) X Y ≫
        (Drinfeld.negative D ⋙ rightCentralAction D M).map (β_ X Y).hom =
      (((negativeMoritaCentralLift D M).obj X).2.β
        ((Drinfeld.negative D ⋙ rightCentralAction D M).obj Y)).hom ≫
          Functor.LaxMonoidal.μ (Drinfeld.negative D ⋙ rightCentralAction D M) Y X := by
  have hμ (Z W : Center D) :
      (Functor.LaxMonoidal.μ (rightCentralLift D M) Z W).f =
        Functor.LaxMonoidal.μ (rightCentralAction D M) Z W := rfl
  have hm {Z W : Center D} (f : Z ⟶ W) :
      ((rightCentralLift D M).map f).f = (rightCentralAction D M).map f := rfl
  have h := Functor.Braided.braided (F := negativeMoritaCentralLift D M) X Y
  have hf := congrArg Center.Hom.f h
  dsimp only [negativeMoritaCentralLift, Functor.LaxMonoidal.comp_μ,
    Functor.comp_map] at hf
  simp only [Center.comp_f, hμ, hm] at hf
  change _ = _ at hf
  simpa only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, Category.assoc] using hf

/-- The same genuine crossing after any genuine braided tensor functor.
This retains the functor's actual tensorators, rather than identifying
its source and image tensor products. -/
lemma negativeMoritaCentralLift_comp_braiding (α : D ⥤ D) [α.Braided] (X Y : D) :
    Functor.LaxMonoidal.μ (α ⋙ Drinfeld.negative D ⋙ rightCentralAction D M) X Y ≫
        (α ⋙ Drinfeld.negative D ⋙ rightCentralAction D M).map (β_ X Y).hom =
      ((((α ⋙ negativeMoritaCentralLift D M).obj X).2.β)
        ((α ⋙ Drinfeld.negative D ⋙ rightCentralAction D M).obj Y)).hom ≫
          Functor.LaxMonoidal.μ (α ⋙ Drinfeld.negative D ⋙ rightCentralAction D M) Y X := by
  have hμ (Z W : Center D) :
      (Functor.LaxMonoidal.μ (rightCentralLift D M) Z W).f =
        Functor.LaxMonoidal.μ (rightCentralAction D M) Z W := rfl
  have hm {Z W : Center D} (f : Z ⟶ W) :
      ((rightCentralLift D M).map f).f = (rightCentralAction D M).map f := rfl
  have h := Functor.Braided.braided (F := α ⋙ negativeMoritaCentralLift D M) X Y
  have hf := congrArg Center.Hom.f h
  dsimp only [negativeMoritaCentralLift, Functor.LaxMonoidal.comp_μ,
    Functor.comp_map] at hf
  simp only [Center.comp_f, hμ, hm] at hf
  change _ = _ at hf
  simpa only [Functor.LaxMonoidal.comp_μ, Functor.comp_map,
    Functor.map_comp, Category.assoc] using hf

end Paper18.Category.GraphPicard

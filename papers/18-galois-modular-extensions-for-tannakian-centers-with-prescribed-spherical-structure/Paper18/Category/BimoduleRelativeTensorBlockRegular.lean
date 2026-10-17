import Paper18.Category.BimoduleRelativeTensorBlockBimodule

/-! # The restricted regular algebra is the actual two-sided block -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor.Block
open ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {R : D} [MonObj R]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (Q : Bimodules R) (q : Retract Q (wattsRegular (R := R)))

/-- Restricting both actions of the genuine regular quotient algebra
recovers the genuine regular-bimodule summand, with underlying identity. -/
def restrictedRegularIso :
    letI := blockMonObj Q q
    letI := blockProjection_isMonHom Q q
    (bimoduleRestriction (blockProjection Q q)).obj
      (wattsRegular (R := Q.X.X)) ≅ Q := by
  letI := blockMonObj Q q
  letI := blockProjection_isMonHom Q q
  refine
    { hom := Mod_.Hom.mk' (Mod_.Hom.mk' (𝟙 Q.X.X) ?_) ?_
      inv := Mod_.Hom.mk' (Mod_.Hom.mk' (𝟙 Q.X.X) ?_) ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · change (blockProjection Q q ▷ Q.X.X ≫ blockMultiplication Q q) ≫ 𝟙 _ =
      R ◁ (𝟙 Q.X.X) ≫ γ[R,Q.X.X]
    simpa only [comp_id, whiskerLeft_id, id_comp] using blockProjection_left_action Q q
  · apply Mod_.Hom.ext
    change (Q.X.X ◁ blockProjection Q q ≫ (𝟙 _ ≫ blockMultiplication Q q)) ≫ 𝟙 _ =
      (𝟙 Q.X.X) ▷ R ≫ γ[mop R,Q.X].hom
    simpa only [id_comp, comp_id, id_whiskerRight] using blockProjection_right_action Q q
  · change γ[R,Q.X.X] ≫ 𝟙 _ =
      R ◁ (𝟙 Q.X.X) ≫ blockProjection Q q ▷ Q.X.X ≫ blockMultiplication Q q
    simpa only [comp_id, whiskerLeft_id, id_comp] using (blockProjection_left_action Q q).symm
  · apply Mod_.Hom.ext
    change γ[mop R,Q.X].hom ≫ 𝟙 _ =
      (𝟙 Q.X.X) ▷ R ≫ Q.X.X ◁ blockProjection Q q ≫ (𝟙 _ ≫ blockMultiplication Q q)
    simpa only [id_comp, comp_id, id_whiskerRight] using (blockProjection_right_action Q q).symm
  · apply Mod_.Hom.ext; apply Mod_.Hom.ext; exact id_comp _
  · apply Mod_.Hom.ext; apply Mod_.Hom.ext; exact id_comp _

/-- Forgetting the right action gives the actual left-module comparison
needed to identify the essential image of quotient restriction. -/
def restrictedRegularLeftIso :
    letI := blockMonObj Q q
    letI := blockProjection_isMonHom Q q
    (Mod_.comap (D := D) (blockProjection Q q)).obj (Mod_.regular Q.X.X) ≅ Q.X := by
  letI := blockMonObj Q q
  letI := blockProjection_isMonHom Q q
  exact (Mod_.forget (D := Mod_ D R) (mop R)).mapIso (restrictedRegularIso Q q)

/-- The actual quotient projection admits its actual native block section. -/
def blockProjection_isSplitEpi : IsSplitEpi (blockProjection Q q) :=
  IsSplitEpi.mk' ⟨blockInclusion Q q, blockInclusion_projection Q q⟩

end Paper18.Category.BimoduleRelativeTensor.Block

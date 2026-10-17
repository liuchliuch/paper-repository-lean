import Paper18.Category.BimoduleRelativeTensorCoherence

/-! # The actual bicategory of algebras and native bimodules -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- Actual algebra objects, actual iterated native bimodules and actual
relative tensor composition form a bicategory. All coherence is proved
through the actual coequalizer bicategory, without a supplied coherence
or equivalence certificate. -/
def nativeBicategory : Bicategory (Mon D) where
  Hom R S := Native R.X S.X
  homCategory _ _ := inferInstance
  id R := regular R.X
  comp M N := tensor M N
  whiskerLeft M _ _ f := whiskerLeft M f
  whiskerRight f N := whiskerRight f N
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft_id M N := by
    apply Mod_.Hom.ext; apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.whiskerLeft_id_bimod
      (M := toBimodObj _ _ M) (N := toBimodObj _ _ N))
  whiskerLeft_comp M _ _ _ f g := by
    apply Mod_.Hom.ext; apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.whiskerLeft_comp_bimod
      (toBimodObj _ _ M) ((toBimod _ _).map f) ((toBimod _ _).map g))
  id_whiskerLeft f := by
    apply Mod_.Hom.ext; apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.id_whiskerLeft_bimod ((toBimod _ _).map f))
  comp_whiskerLeft M N _ _ f := by
    apply Mod_.Hom.ext; apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.comp_whiskerLeft_bimod
      (toBimodObj _ _ M) (toBimodObj _ _ N) ((toBimod _ _).map f))
  id_whiskerRight M N := by
    apply Mod_.Hom.ext; apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.id_whiskerRight_bimod
      (M := toBimodObj _ _ M) (N := toBimodObj _ _ N))
  comp_whiskerRight f g Q := by
    apply Mod_.Hom.ext; apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.comp_whiskerRight_bimod
      ((toBimod _ _).map f) ((toBimod _ _).map g) (toBimodObj _ _ Q))
  whiskerRight_id f := by
    apply Mod_.Hom.ext; apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.whiskerRight_id_bimod ((toBimod _ _).map f))
  whiskerRight_comp f N P := by
    apply Mod_.Hom.ext; apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.whiskerRight_comp_bimod
      ((toBimod _ _).map f) (toBimodObj _ _ N) (toBimodObj _ _ P))
  whisker_assoc M _ _ f P := by
    apply Mod_.Hom.ext; apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.whisker_assoc_bimod
      (toBimodObj _ _ M) ((toBimod _ _).map f) (toBimodObj _ _ P))
  whisker_exchange f g := by
    apply Mod_.Hom.ext; apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.whisker_exchange_bimod
      ((toBimod _ _).map f) ((toBimod _ _).map g))
  pentagon := pentagon
  triangle := triangle

end Paper18.Category.BimoduleRelativeTensor

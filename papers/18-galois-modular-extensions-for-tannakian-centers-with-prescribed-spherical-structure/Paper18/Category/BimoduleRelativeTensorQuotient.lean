import Paper18.Category.BimoduleRelativeTensorBicategory

/-! # Actual quotient formulas for native relative composition -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {R S T U : D} [MonObj R] [MonObj S] [MonObj T] [MonObj U]

@[reassoc (attr := simp)]
lemma π_whiskerLeft (M : Native R S) {N N' : Native S T} (f : N ⟶ N') :
    π M N ≫ (whiskerLeft M f).hom.hom = M.X.X ◁ f.hom.hom ≫ π M N' := by
  dsimp only [whiskerLeft, fromBimod, toBimod, Bimod.whiskerLeft, Mod_.Hom.mk'_hom]
  erw [ι_colimMap, parallelPairHom_app_one]
  rfl

@[reassoc (attr := simp)]
lemma π_whiskerRight {M M' : Native R S} (f : M ⟶ M') (N : Native S T) :
    π M N ≫ (whiskerRight f N).hom.hom = f.hom.hom ▷ N.X.X ≫ π M' N := by
  dsimp only [whiskerRight, fromBimod, toBimod, Bimod.whiskerRight, Mod_.Hom.mk'_hom]
  erw [ι_colimMap, parallelPairHom_app_one]
  rfl

/-- The actual relative associator is the descent of the actual ambient
associator through the two actual balancing quotients. -/
@[reassoc]
lemma π_associator (M : Native R S) (N : Native S T) (P : Native T U) :
    π M N ▷ P.X.X ≫ π (tensor M N) P ≫ (associator M N P).hom.hom.hom =
      (α_ M.X.X N.X.X P.X.X).hom ≫ M.X.X ◁ π N P ≫ π M (tensor N P) := by
  dsimp only [associator, Functor.mapIso_hom, fromBimod, Bimod.associatorBimod,
    Bimod.isoOfIso, Mod_.Hom.mk'_hom]
  dsimp only [Bimod.AssociatorBimod.hom, π]
  rw [coequalizer.π_desc]
  dsimp only [Bimod.AssociatorBimod.homAux]
  exact π_tensor_id_preserves_coequalizer_inv_desc _ _ _ _

@[reassoc (attr := simp)]
lemma π_leftUnitor (M : Native R S) :
    π (regular R) M ≫ (leftUnitor M).hom.hom.hom = γ[R,M.X.X] := by
  dsimp only [leftUnitor, Functor.mapIso_hom, fromBimod, Bimod.leftUnitorBimod,
    Bimod.isoOfIso, Mod_.Hom.mk'_hom, Bimod.LeftUnitorBimod.hom]
  exact coequalizer.π_desc _ _

@[reassoc (attr := simp)]
lemma π_rightUnitor (M : Native R S) :
    π M (regular S) ≫ (rightUnitor M).hom.hom.hom = γ[mop S,M.X].hom := by
  dsimp only [rightUnitor, Functor.mapIso_hom, fromBimod, Bimod.rightUnitorBimod,
    Bimod.isoOfIso, Mod_.Hom.mk'_hom, Bimod.RightUnitorBimod.hom]
  exact coequalizer.π_desc _ _

end Paper18.Category.BimoduleRelativeTensor

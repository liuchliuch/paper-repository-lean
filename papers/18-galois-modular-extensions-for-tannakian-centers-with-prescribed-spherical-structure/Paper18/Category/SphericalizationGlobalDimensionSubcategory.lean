import Paper18.Category.SphericalizationGlobalDimensionPositive
import Paper18.Category.SphericalizationFunctorLift
import Paper18.Category.FusionSubcategoryFunctor
import Paper18.Category.FusionSubcategoryPivotal

/-! # Sphericalization commutes with actual full fusion subcategories -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal]

/-- The actual inverse image fusion support under sphericalization forget. -/
def preimageProperty : ObjectProperty (Sphericalized C) := fun X => P (forget.obj X)

instance preimageProperty_isAdditive : IsAdditiveFullProperty (preimageProperty P) where
  of_retract r h := IsAdditiveFullProperty.of_retract (P := P) (r.map forget) h
  biproduct f h := by
    change P (forget.obj (⨁ f))
    exact IsAdditiveFullProperty.of_iso P (forget.mapBiproduct f)
      (IsAdditiveFullProperty.biproduct _ h)

instance preimageProperty_isMonoidal : (preimageProperty P).IsMonoidal where
  prop_unit := ObjectProperty.prop_unit P
  prop_tensor X Y hX hY := by
    change P (X.obj.obj ⊗ Y.obj.obj)
    exact ObjectProperty.prop_tensor hX hY

instance preimage_fullSubcategory_finiteDimensional_hom
    (X Y : (preimageProperty P).FullSubcategory) : FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))

/-- The actual sphericalization lift of the inherited full inclusion,
with target restricted to its actual underlying-object preimage. -/
def subcategoryLift :
    letI := S.fullSubcategoryRightRigid P
    Sphericalized P.FullSubcategory ⥤ (preimageProperty P).FullSubcategory := by
  letI := S.fullSubcategoryRightRigid P
  exact fullSubcategoryLift (preimageProperty P) (mapFunctor P.ι) (fun X => X.obj.obj.property)

instance subcategoryLift_monoidal :
    letI := S.fullSubcategoryRightRigid P
    (subcategoryLift S P).Monoidal := by
  letI := S.fullSubcategoryRightRigid P
  unfold subcategoryLift; infer_instance
instance subcategoryLift_additive :
    letI := S.fullSubcategoryRightRigid P
    (subcategoryLift S P).Additive := by
  letI := S.fullSubcategoryRightRigid P
  unfold subcategoryLift; infer_instance
instance subcategoryLift_linear :
    letI := S.fullSubcategoryRightRigid P
    (subcategoryLift S P).Linear ℂ := by
  letI := S.fullSubcategoryRightRigid P
  unfold subcategoryLift; infer_instance
instance subcategoryLift_full :
    letI := S.fullSubcategoryRightRigid P
    (subcategoryLift S P).Full := by
  letI := S.fullSubcategoryRightRigid P
  unfold subcategoryLift; infer_instance
instance subcategoryLift_faithful :
    letI := S.fullSubcategoryRightRigid P
    (subcategoryLift S P).Faithful := by
  letI := S.fullSubcategoryRightRigid P
  unfold subcategoryLift; infer_instance

lemma inclusion_doubleDualComparison (X : P.FullSubcategory) :
    letI := S.fullSubcategoryRightRigid P
    (doubleDualComparison P.ι X).hom = 𝟙 ((doubleDualFunctor C).obj X.obj) := by
  letI := S.fullSubcategoryRightRigid P
  dsimp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom]
  rw [S.fullSubcategory_dualComparison P X,
    S.fullSubcategory_dualComparison P (dual P.FullSubcategory X)]
  dsimp only [dualMapIso, Iso.refl_hom, Iso.refl_inv, dualMap,
    ObjectProperty.ι, inducedFunctor, dual,
    FiniteSemisimpleSkeleton.fullSubcategoryRightRigid]
  simp only [rightAdjointMate_id, id_comp, comp_id]
  rfl

/-- An actual square object whose underlying object lies in the full
subcategory is an actual square object of that full subcategory. -/
def subcategoryPreimageObject (Y : (preimageProperty P).FullSubcategory) :
    letI := S.fullSubcategoryRightRigid P
    Sphericalized P.FullSubcategory := by
  letI := S.fullSubcategoryRightRigid P
  exact ⟨⟨⟨Y.obj.obj.obj, Y.property⟩,
    { hom := Y.obj.obj.phi.hom
      inv := Y.obj.obj.phi.inv
      hom_inv_id := Y.obj.obj.phi.hom_inv_id
      inv_hom_id := Y.obj.obj.phi.inv_hom_id }⟩, Y.obj.property⟩

def subcategoryPreimageIso (Y : (preimageProperty P).FullSubcategory) :
    letI := S.fullSubcategoryRightRigid P
    (subcategoryLift S P).obj (subcategoryPreimageObject S P Y) ≅ Y := by
  letI := S.fullSubcategoryRightRigid P
  exact (preimageProperty P).isoMk (radfordSquareProperty.isoMk
    (Pivotalized.mkIso (Iso.refl _) (by
      change 𝟙 _ ≫ Y.obj.obj.phi.hom =
        (Y.obj.obj.phi.hom ≫ (doubleDualComparison P.ι (⟨Y.obj.obj.obj, Y.property⟩ : P.FullSubcategory)).hom) ≫
          (doubleDualFunctor C).map (𝟙 _)
      rw [inclusion_doubleDualComparison S P]
      simp)))

instance subcategoryLift_essSurj :
    letI := S.fullSubcategoryRightRigid P
    (subcategoryLift S P).EssSurj := by
  letI := S.fullSubcategoryRightRigid P
  exact ⟨fun Y => ⟨subcategoryPreimageObject S P Y, ⟨subcategoryPreimageIso S P Y⟩⟩⟩

instance subcategoryLift_isEquivalence :
    letI := S.fullSubcategoryRightRigid P
    (subcategoryLift S P).IsEquivalence := by
  letI := S.fullSubcategoryRightRigid P
  exact {}

end Paper18.Category.Sphericalized

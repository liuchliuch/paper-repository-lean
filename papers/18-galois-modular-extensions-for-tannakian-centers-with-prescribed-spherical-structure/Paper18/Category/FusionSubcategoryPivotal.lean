import Paper18.Category.FusionSubcategoryRigid
import Paper18.Category.PivotalDuality

/-! # Restricting prescribed pivotal and spherical structures to full fusion subcategories -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal]

/-- The prescribed actual pivotal isomorphism restricts to a full fusion
subcategory; its components and canonical duality maps are the ambient maps. -/
def fullSubcategoryPivotal (J : PivotalStructure C) :
    letI := S.fullSubcategoryRightRigid P
    PivotalStructure P.FullSubcategory := by
  letI := S.fullSubcategoryRightRigid P
  exact
    { j :=
        { hom :=
            { app X := J.j.hom.app X.obj
              naturality _ _ f := J.j.hom.naturality f }
          inv :=
            { app X := J.j.inv.app X.obj
              naturality _ _ f := J.j.inv.naturality f }
          hom_inv_id := by ext X; exact J.j.hom_inv_id_app X.obj
          inv_hom_id := by ext X; exact J.j.inv_hom_id_app X.obj }
      unit := J.unit
      tensor X Y := J.tensor X.obj Y.obj }

/-- The two actual traces in the subcategory are literally their ambient
traces, so prescribed sphericality restricts. -/
lemma fullSubcategoryPivotal_spherical (J : PivotalStructure C) (hJ : J.Spherical) :
    letI := S.fullSubcategoryRightRigid P
    (S.fullSubcategoryPivotal P J).Spherical := by
  letI := S.fullSubcategoryRightRigid P
  intro X f
  exact hJ X.obj f

/-- The canonical right-dual comparison of the inherited inclusion is the
identity, as follows from compatibility with the actual evaluation map. -/
lemma fullSubcategory_dualComparison (X : P.FullSubcategory) :
    letI := S.fullSubcategoryRightRigid P
    dualComparison P.ι X = Iso.refl (X.objᘁ) := by
  letI := S.fullSubcategoryRightRigid P
  apply Iso.ext
  apply pairing_hom_ext (inferInstanceAs (ExactPairing X.obj (X.objᘁ)))
  have hη : Functor.OplaxMonoidal.η P.ι = 𝟙 (𝟙_ C) := rfl
  have h := dualComparison_evaluation P.ι X
  rw [hη] at h
  change (dualComparison P.ι X).hom ▷ X.obj ≫ ε_ X.obj (X.objᘁ) =
    𝟙 (X.objᘁ) ▷ X.obj ≫ ε_ X.obj (X.objᘁ)
  change (dualComparison P.ι X).hom ▷ X.obj ≫ ε_ X.obj (X.objᘁ) =
    𝟙 _ ≫ ε_ X.obj (X.objᘁ) ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id, id_whiskerRight] using h

/-- The fully faithful braided inclusion preserves the prescribed pivotal
structure via its canonical, rather than supplied, dual comparison. -/
lemma fullSubcategory_preservesPivotal (J : PivotalStructure C) :
    letI := S.fullSubcategoryRightRigid P
    PreservesPivotal P.ι (S.fullSubcategoryPivotal P J) J := by
  letI := S.fullSubcategoryRightRigid P
  intro X
  dsimp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom]
  rw [S.fullSubcategory_dualComparison P X,
    S.fullSubcategory_dualComparison P (dual P.FullSubcategory X)]
  simp only [dualMapIso, Iso.refl_inv, dualMap, Iso.refl_hom]
  dsimp only [fullSubcategoryPivotal, ObjectProperty.ι_map, ObjectProperty.ι_obj,
    dual, fullSubcategoryRightRigid]
  simp only [rightAdjointMate_id, Category.comp_id]
  change J.j.hom.app X.obj ≫ 𝟙 ((doubleDualFunctor C).obj X.obj) = J.j.hom.app X.obj
  exact Category.comp_id _

end Paper18.Category.FiniteSemisimpleSkeleton

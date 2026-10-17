import Paper18.Category.DeligneTensorProductMapRaw
import Paper18.Category.DeligneTensorProductMapSingleton
import Paper18.Category.DeligneTensorProductMapWhisker
import Paper18.Category.DiagonalAlgebraCapGenerator

/-! # The actual monoidal tensor-product square for a braided linear functor -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u v' u'
namespace Paper18.Category.DeligneTensorProductMap
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]
  [HasFiniteBiproducts C]

/-- The actual singleton comparison for the central tensor-product functor. -/
def capEmbeddingIso : Mat_.embedding (LinearTensor C C) ⋙
    DiagonalAlgebra.tensorProductFunctor (C := C) ≅ rawTensor C :=
  (Functor.associator (Mat_.embedding (LinearTensor C C))
    (Drinfeld.deligneFactorization C) (Center.forget C)).symm ≪≫
    Functor.isoWhiskerRight (linearMatLiftEmbeddingIso (Drinfeld.linearFactorization C))
      (Center.forget C)

instance capEmbeddingIso_monoidal : NatTrans.IsMonoidal (capEmbeddingIso C).hom := by
  dsimp only [capEmbeddingIso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom]
  infer_instance

variable {C} {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [BraidedCategory D]
  [HasFiniteBiproducts D] (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Braided]

def sourceFunctor : DeligneProduct C C ⥤ D :=
  DeligneProduct.map F F ⋙ DiagonalAlgebra.tensorProductFunctor (C := D)
def targetFunctor : DeligneProduct C C ⥤ D :=
  DiagonalAlgebra.tensorProductFunctor (C := C) ⋙ F
instance sourceFunctor_additive : (sourceFunctor F).Additive := by unfold sourceFunctor; infer_instance
instance targetFunctor_additive : (targetFunctor F).Additive := by unfold targetFunctor; infer_instance
instance sourceFunctor_monoidal : (sourceFunctor F).Monoidal := by unfold sourceFunctor; infer_instance
instance targetFunctor_monoidal : (targetFunctor F).Monoidal := by unfold targetFunctor; infer_instance

instance mapEmbeddingIso_monoidal :
    NatTrans.IsMonoidal (DeligneProduct.mapEmbeddingIso F F).hom := by
  change NatTrans.IsMonoidal (linearMatLiftEmbeddingIso
    (LinearTensor.map F F ⋙ Mat_.embedding (LinearTensor D D))).hom
  infer_instance

/-- On singleton pair objects, the square is the actual tensorator of F,
conjugated by the actual additive-envelope singleton identifications. -/
def singletonComparison : Mat_.embedding (LinearTensor C C) ⋙ sourceFunctor F ≅
    Mat_.embedding (LinearTensor C C) ⋙ targetFunctor F :=
  (Functor.associator (Mat_.embedding (LinearTensor C C)) (DeligneProduct.map F F)
    (DiagonalAlgebra.tensorProductFunctor (C := D))).symm ≪≫
  Functor.isoWhiskerRight (DeligneProduct.mapEmbeddingIso F F)
    (DiagonalAlgebra.tensorProductFunctor (C := D)) ≪≫
  Functor.associator (LinearTensor.map F F) (Mat_.embedding (LinearTensor D D))
    (DiagonalAlgebra.tensorProductFunctor (C := D)) ≪≫
  Functor.isoWhiskerLeft (LinearTensor.map F F) (capEmbeddingIso D) ≪≫
  rawComparison F ≪≫
  Functor.isoWhiskerRight (capEmbeddingIso C).symm F ≪≫
  Functor.associator (Mat_.embedding (LinearTensor C C))
    (DiagonalAlgebra.tensorProductFunctor (C := C)) F

set_option synthInstance.maxSize 4096 in
instance singletonComparison_monoidal : NatTrans.IsMonoidal (singletonComparison F).hom := by
  haveI h₁ : NatTrans.IsMonoidal ((Functor.associator (Mat_.embedding (LinearTensor C C))
    (DeligneProduct.map F F) (DiagonalAlgebra.tensorProductFunctor (C := D))).inv) := inferInstance
  haveI h₂ : NatTrans.IsMonoidal (Functor.whiskerRight (DeligneProduct.mapEmbeddingIso F F).hom
    (DiagonalAlgebra.tensorProductFunctor (C := D))) := inferInstance
  haveI h₃ : NatTrans.IsMonoidal ((Functor.associator (LinearTensor.map F F)
    (Mat_.embedding (LinearTensor D D)) (DiagonalAlgebra.tensorProductFunctor (C := D))).hom) := inferInstance
  haveI h₄ : NatTrans.IsMonoidal (Functor.whiskerLeft (LinearTensor.map F F)
    (capEmbeddingIso D).hom) := inferInstance
  haveI h₅ : NatTrans.IsMonoidal (Functor.whiskerRight (capEmbeddingIso C).inv F) := inferInstance
  haveI h₆ : NatTrans.IsMonoidal ((Functor.associator (Mat_.embedding (LinearTensor C C))
    (DiagonalAlgebra.tensorProductFunctor (C := C)) F).hom) := inferInstance
  haveI hraw : NatTrans.IsMonoidal (rawComparison F).hom := rawComparison_monoidal F
  dsimp only [singletonComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

/-- The actual monoidal comparison between the two tensor-product functors. -/
def comparison : sourceFunctor F ≅ targetFunctor F :=
  extendIso (sourceFunctor F) (targetFunctor F) (singletonComparison F)

instance comparison_monoidal : NatTrans.IsMonoidal (comparison F).hom := by
  have he : Functor.whiskerLeft (Mat_.embedding (LinearTensor C C)) (comparison F).hom =
      (singletonComparison F).hom := by
    ext X
    exact extendIso_hom_singleton _ _ _ X
  letI : NatTrans.IsMonoidal
      (Functor.whiskerLeft (Mat_.embedding (LinearTensor C C)) (comparison F).hom) := by
    rw [he]
    infer_instance
  exact isMonoidal_of_singletons _ _ _

section PairFormula
variable [RightRigidCategory C] [HasKernels C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [RightRigidCategory D] [HasKernels D] [Simple (𝟙_ D)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]

lemma capEmbeddingIso_app (X Y : C) :
    (capEmbeddingIso C).app (⟨X,Y⟩ : LinearTensor C C) = DiagonalAlgebra.capPairIso X Y := by
  apply Iso.ext
  change (capEmbeddingIso C).hom.app (⟨X,Y⟩ : LinearTensor C C) =
    (DiagonalAlgebra.capPairIso X Y).hom
  simp only [capEmbeddingIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp]
  erw [Category.id_comp]
  change (Center.forget C).map
    ((linearMatLiftEmbeddingIso (Drinfeld.linearFactorization C)).hom.app ⟨X,Y⟩) =
      (Center.forget C).map (Drinfeld.deligneFactorizationPairIso X Y).hom
  apply congrArg (Center.forget C).map
  apply biproduct.hom_ext'
  rintro ⟨⟩
  simp [linearMatLiftEmbeddingIso, linearMatLiftSingletonIso,
    DiagonalAlgebra.capPairIso, Drinfeld.deligneFactorizationPairIso,
    biproductUniqueIso, limitBiconeOfUnique]

/-- The exact pure-pair formula used to compute the induced canonical
algebra map on actual evaluation-cap generators. -/
lemma comparison_pair (X Y : C) :
    (comparison F).hom.app ((Mat_.embedding (LinearTensor C C)).obj ⟨X,Y⟩) ≫
      F.map (DiagonalAlgebra.capPairIso X Y).hom =
    (DiagonalAlgebra.tensorProductFunctor (C := D)).map
      (DeligneProduct.mapPairIso F F X Y).hom ≫
        (DiagonalAlgebra.capPairIso (F.obj X) (F.obj Y)).hom ≫
          Functor.LaxMonoidal.μ F X Y := by
  rw [show (comparison F).hom.app ((Mat_.embedding (LinearTensor C C)).obj ⟨X,Y⟩) =
    (singletonComparison F).hom.app ⟨X,Y⟩ from extendIso_hom_singleton _ _ _ _]
  simp only [singletonComparison, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  erw [Category.id_comp]
  change _ ≫ _ ≫ _ ≫ F.map ((capEmbeddingIso C).app ⟨X,Y⟩).inv ≫
    F.map (DiagonalAlgebra.capPairIso X Y).hom = _
  rw [capEmbeddingIso_app, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]
  change (DiagonalAlgebra.tensorProductFunctor (C := D)).map
      (DeligneProduct.mapPairIso F F X Y).hom ≫
    ((capEmbeddingIso D).app (⟨F.obj X,F.obj Y⟩ : LinearTensor D D)).hom ≫
      Functor.LaxMonoidal.μ F X Y = _
  rw [capEmbeddingIso_app]

end PairFormula
end Paper18.Category.DeligneTensorProductMap

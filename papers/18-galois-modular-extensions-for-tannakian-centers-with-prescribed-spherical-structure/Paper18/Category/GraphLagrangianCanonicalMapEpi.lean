import Paper18.Category.GraphLagrangianCanonicalMap
import Paper18.Category.DiagonalAlgebraCapGeneratorEpi
import Paper18.Category.PivotalFunctor

/-! # Actual cap generation and epimorphy of the diagonal algebra comparison -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.GraphLagrangian
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Braided] [F.Additive] [F.Linear ℂ]
  (e : DeligneProduct.map F F ⋙ DiagonalAlgebra.tensorProductFunctor (C := D) ≅
    DiagonalAlgebra.tensorProductFunctor (C := C) ⋙ F)
  [NatTrans.IsMonoidal e.hom]


variable (hpair : ∀ X Y : C,
    e.hom.app (DeligneProduct.externalObject X Y) ≫ F.map (capPairIso X Y).hom =
      (tensorProductFunctor (C := D)).map (DeligneProduct.mapPairIso F F X Y).hom ≫
        (capPairIso (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F X Y)

include hpair in
/-- The actual comparison carries source cap generators to target cap
generators through the canonical chosen-dual comparison. -/
lemma canonicalMap_capGenerator (X : C) :
    capPairMap (dualComparison F X).inv (𝟙 (F.obj X)) ≫
      (DeligneProduct.mapPairIso F F (dual C X) X).inv ≫
        (DeligneProduct.map F F).map (capGenerator S X) ≫ canonicalMap S T F e =
      capGenerator T (F.obj X) := by
  apply ((tensorProductRightAdjunction T).homEquiv _ _).symm.injective
  change (tensorProductFunctor (C := D)).map
    (capPairMap (dualComparison F X).inv (𝟙 (F.obj X)) ≫
      (DeligneProduct.mapPairIso F F (dual C X) X).inv ≫
        (DeligneProduct.map F F).map (capGenerator S X) ≫ canonicalMap S T F e) ≫
      canonicalAlgebraCounit T =
    (tensorProductFunctor (C := D)).map (capGenerator T (F.obj X)) ≫ canonicalAlgebraCounit T
  have hg := canonicalMap_generator S T F e (capGenerator S X)
  rw [capGenerator_counit S X] at hg
  simp only [Functor.map_comp, assoc] at hg ⊢
  rw [hg, capGenerator_counit T (F.obj X)]
  rw [reassoc_of% (hpair (dual C X) X)]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, comp_id]
  rw [capPairIso_naturality_assoc]
  rw [← dualComparison_evaluation F X]
  simp only [tensorHom_id, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, id_comp]

include hpair in
/-- Actual retract dominance makes the actual diagonal algebra comparison
epi. Its surjectivity is proved from actual rigid cap generators. -/
theorem canonicalMap_epi
    (hdom : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) :
    Epi (canonicalMap S T F e) := by
  apply epi_of_image_capGenerators T F hdom
  intro X
  refine ⟨capPairMap (dualComparison F X).inv (𝟙 (F.obj X)) ≫
    (DeligneProduct.mapPairIso F F (dual C X) X).inv ≫
      (DeligneProduct.map F F).map (capGenerator S X), ?_⟩
  simpa only [assoc] using canonicalMap_capGenerator S T F e hpair X

end Paper18.Category.GraphLagrangian

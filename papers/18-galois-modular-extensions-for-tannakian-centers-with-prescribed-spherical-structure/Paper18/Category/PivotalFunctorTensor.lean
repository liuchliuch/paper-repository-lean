import Paper18.Category.PivotalFunctorTensorUnit

/-! # Monoidal double-dual comparison for arbitrary strong tensor functors -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
universe v u v' u'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
  (F : C ⥤ D) [F.Monoidal]

lemma dualTensorIso_inv_naturality {E : Type*} [Category E] [MonoidalCategory E]
    [RightRigidCategory E] {X X' Y Y' : E} (f : X ⟶ X') (g : Y ⟶ Y') :
    (dualTensorIso X' Y').inv ≫ dualMap E (f ⊗ₘ g) =
      (dualMap E g ⊗ₘ dualMap E f) ≫ (dualTensorIso X Y).inv := by
  apply (cancel_mono (dualTensorIso X Y).hom).mp
  rw [assoc, dualTensorIso_naturality]
  simp only [← assoc, Iso.inv_hom_id, id_comp, Iso.inv_hom_id_assoc, comp_id]
  simp only [assoc, Iso.inv_hom_id, comp_id]

/-- The canonical double-dual comparison preserves actual tensorators for
any strong monoidal functor. Neither category is assumed braided. -/
lemma canonicalDoubleDualComparison_tensor (X Y : C) :
    μ (doubleDualFunctor C ⋙ F) X Y ≫ (doubleDualComparison F (X ⊗ Y)).hom =
      ((doubleDualComparison F X).hom ⊗ₘ (doubleDualComparison F Y).hom) ≫
        μ (F ⋙ doubleDualFunctor D) X Y := by
  simp only [Functor.LaxMonoidal.comp_μ, canonicalDoubleDual_tensor,
    doubleDualTensorHom, doubleDualComparison, Iso.trans_hom, Iso.symm_hom, dualMapIso,
    Functor.map_comp, assoc]
  dsimp only [doubleDualFunctor]
  rw [← dualTensorIso_inv, ← dualTensorIso_hom, ← dualTensorIso_inv, ← dualTensorIso_hom]
  rw [reassoc_of% (dualComparison_naturality F (dualTensorIso X Y).hom)]
  rw [reassoc_of% (dualComparison_tensor_solved F (dual C Y) (dual C X))]
  have hc : dualMap D (δ F (dual C Y) (dual C X)) ≫
      dualMap D (F.map (dualTensorIso X Y).hom) ≫
        dualMap D (dualComparison F (X ⊗ Y)).inv =
      dualMap D ((dualComparison F (X ⊗ Y)).inv ≫
        F.map (dualTensorIso X Y).hom ≫ δ F (dual C Y) (dual C X)) := by
    simp only [dualMap, comp_rightAdjointMate, assoc]
  rw [hc, dualComparison_tensor_inverse]
  simp only [dualMap, comp_rightAdjointMate, assoc]
  rw [reassoc_of% (dualTensorIso_inv_naturality
    (dualComparison F Y).inv (dualComparison F X).inv)]
  rw [← tensorHom_comp_tensorHom_assoc]


/-- The same canonical comparison preserves the actual unit tensorators,
without a braiding assumption. -/
lemma canonicalDoubleDualComparison_unit :
    ε (doubleDualFunctor C ⋙ F) ≫ (doubleDualComparison F (𝟙_ C)).hom =
      ε (F ⋙ doubleDualFunctor D) := by
  simp only [Functor.LaxMonoidal.comp_ε, canonicalDoubleDual_unit,
    doubleDualUnitHom, doubleDualComparison, Iso.trans_hom, Iso.symm_hom,
    dualMapIso, Functor.map_comp, assoc]
  dsimp only [doubleDualFunctor]
  rw [reassoc_of% (dualComparison_naturality F (dualUnitTo C))]
  rw [reassoc_of% (dualComparison_unit_solved F)]
  have hc : dualMap D (η F) ≫ dualMap D (F.map (dualUnitTo C)) ≫
      dualMap D (dualComparison F (𝟙_ C)).inv =
    dualMap D ((dualComparison F (𝟙_ C)).inv ≫ F.map (dualUnitTo C) ≫ η F) := by
    simp only [dualMap, comp_rightAdjointMate, assoc]
  rw [hc, dualComparison_unit_inverse]
  simp only [dualMap, comp_rightAdjointMate, assoc]

/-- The actual canonical double-dual comparison is monoidal for every
strong monoidal functor, including functors between nonbraided categories. -/
instance canonicalDoubleDualComparisonIsMonoidal :
    NatTrans.IsMonoidal (doubleDualComparisonNatIso F).hom where
  unit := canonicalDoubleDualComparison_unit F
  tensor X Y := canonicalDoubleDualComparison_tensor F X Y

end Paper18.Category

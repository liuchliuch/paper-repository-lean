import Paper18.Category.PivotalFunctorTensorDual

/-! # Canonical chosen-dual unit comparison for arbitrary strong tensor functors -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
universe v u v' u'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- The actual canonical right-dual comparison preserves the canonical
unit duality. No braiding or pivotal structure is used. -/
lemma dualComparison_unit (F : C ⥤ D) [F.Monoidal] :
    (dualComparison F (𝟙_ C)).hom ≫ dualMap D (ε F) ≫ dualUnitTo D =
      F.map (dualUnitTo C) ≫ η F := by
  apply pairing_hom_ext (CategoryTheory.exactPairingUnit (C := D))
  change (_ ≫ _ ≫ _) ▷ (𝟙_ D) ≫ (ρ_ (𝟙_ D)).hom =
    (_ ≫ _) ▷ (𝟙_ D) ≫ (ρ_ (𝟙_ D)).hom
  simp only [comp_whiskerRight, assoc]
  rw [← dualUnitIso_hom, dualUnitIso_evaluation, rightAdjointMate_comp_evaluation,
    ← whisker_exchange_assoc, dualComparison_evaluation]
  rw [rightUnitor_naturality, rightUnitor_naturality_assoc]
  have he : ε_ (𝟙_ C) (dual C (𝟙_ C)) =
      (ρ_ (dual C (𝟙_ C))).hom ≫ dualUnitTo C := by
    simp only [dualUnitTo, Iso.hom_inv_id_assoc]
  rw [he, F.map_comp]
  simp only [assoc]
  rw [← Functor.LaxMonoidal.right_unitality_assoc]


lemma dualComparison_unit_solved :
    ε F ≫ F.map (dualUnitFrom C) ≫ (dualComparison F (𝟙_ C)).hom =
      dualUnitFrom D ≫ dualMap D (η F) := by
  letI : IsIso (dualUnitTo D) := by rw [← dualUnitIso_hom]; infer_instance
  apply (cancel_mono (dualMap D (ε F) ≫ dualUnitTo D)).mp
  simp only [assoc]
  rw [dualComparison_unit]
  simp only [← F.map_comp_assoc, ← dualUnitIso_inv, ← dualUnitIso_hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, id_comp,
    dualMap, ← comp_rightAdjointMate_assoc, ε_η, rightAdjointMate_id]

lemma dualComparison_unit_inverse :
    (dualComparison F (𝟙_ C)).inv ≫ F.map (dualUnitTo C) ≫ η F =
      dualMap D (ε F) ≫ dualUnitTo D := by
  apply (cancel_epi (dualComparison F (𝟙_ C)).hom).mp
  simp only [← assoc, Iso.hom_inv_id, id_comp]
  simpa only [assoc] using (dualComparison_unit F).symm

end Paper18.Category

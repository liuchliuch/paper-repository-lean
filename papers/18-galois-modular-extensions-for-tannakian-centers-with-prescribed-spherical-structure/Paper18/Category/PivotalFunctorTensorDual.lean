import Paper18.Category.PivotalFunctorTensorBasic

/-! # The anti-tensor coherence of the canonical chosen-dual comparison -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
universe v u v' u'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
  (F : C ⥤ D) [F.Monoidal]


/-- The actual chosen dual mate of an isomorphism is an isomorphism. -/
instance dualMapIsIso {E : Type*} [Category E] [MonoidalCategory E]
    [RightRigidCategory E] {X Y : E} (f : X ⟶ Y) [IsIso f] : IsIso (dualMap E f) := by
  change IsIso (dualMapIso (asIso f)).hom
  infer_instance

/-- Tensor compatibility of the actual canonical dual comparison,
expressed from the tensor of the two image duals. -/
lemma dualComparison_tensor_inv (X Y : C) :
    μ F (dual C Y) (dual C X) ≫ F.map (dualTensorIso X Y).inv ≫
      (dualComparison F (X ⊗ Y)).hom ≫ dualMap D (μ F X Y) ≫
        (dualTensorIso (F.obj X) (F.obj Y)).hom =
      (dualComparison F Y).hom ⊗ₘ (dualComparison F X).hom := by
  apply pairing_hom_ext (tensorExactPairing (F.obj X) (F.obj Y))
  change (_ ≫ _ ≫ _ ≫ _ ≫ _) ▷ (F.obj X ⊗ F.obj Y) ≫
      tensorEvaluation D (F.obj X) (F.obj Y) =
    ((dualComparison F Y).hom ⊗ₘ (dualComparison F X).hom) ▷
      (F.obj X ⊗ F.obj Y) ≫ tensorEvaluation D (F.obj X) (F.obj Y)
  simp only [comp_whiskerRight, assoc]
  rw [dualTensorIso_evaluation, rightAdjointMate_comp_evaluation]
  rw [← whisker_exchange_assoc, dualComparison_evaluation]
  rw [← whisker_exchange_assoc, μ_natural_left_assoc]
  simp only [← F.map_comp_assoc]
  rw [dualTensorIso_inv_evaluation]
  change μ F (dual C Y) (dual C X) ▷ (F.obj X ⊗ F.obj Y) ≫
    F.obj (dual C Y ⊗ dual C X) ◁ μ F X Y ≫
      μ F (dual C Y ⊗ dual C X) (X ⊗ Y) ≫
        F.map (tensorEvaluation C X Y) ≫ η F = _
  rw [← reassoc_of% (tensorHom_def (μ F (dual C Y) (dual C X)) (μ F X Y))]
  rw [tensorEvaluation_eq, map_tensorEval]
  rw [tensorEvaluation_eq, tensorHom_def', comp_whiskerRight, assoc,
    tensorEval_map_rightDual, tensorEval_map_leftDual]
  rw [dualComparison_evaluation, dualComparison_evaluation]


/-- The canonical dual comparison carries the chosen tensor comparison
through the actual strong tensorator. -/
lemma dualComparison_tensor (X Y : C) :
    (dualComparison F (X ⊗ Y)).hom ≫ dualMap D (μ F X Y) ≫
        (dualTensorIso (F.obj X) (F.obj Y)).hom =
      F.map (dualTensorIso X Y).hom ≫ δ F (dual C Y) (dual C X) ≫
        ((dualComparison F Y).hom ⊗ₘ (dualComparison F X).hom) := by
  apply (cancel_epi (μ F (dual C Y) (dual C X) ≫ F.map (dualTensorIso X Y).inv)).mp
  simp only [assoc]
  rw [dualComparison_tensor_inv]
  rw [← F.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, id_comp,
    μ_δ_assoc]

lemma dualComparison_tensor_solved (X Y : C) :
    μ F (dual C Y) (dual C X) ≫ F.map (dualTensorIso X Y).inv ≫
        (dualComparison F (X ⊗ Y)).hom =
      ((dualComparison F Y).hom ⊗ₘ (dualComparison F X).hom) ≫
        (dualTensorIso (F.obj X) (F.obj Y)).inv ≫ dualMap D (δ F X Y) := by
  apply (cancel_mono (dualMap D (μ F X Y) ≫
    (dualTensorIso (F.obj X) (F.obj Y)).hom)).mp
  simp only [assoc]
  rw [dualComparison_tensor_inv]
  simp only [dualMap, ← comp_rightAdjointMate_assoc, μ_δ, rightAdjointMate_id,
    id_comp, Iso.inv_hom_id, comp_id]

lemma dualComparison_tensor_inverse (X Y : C) :
    (dualComparison F (X ⊗ Y)).inv ≫ F.map (dualTensorIso X Y).hom ≫
        δ F (dual C Y) (dual C X) =
      dualMap D (μ F X Y) ≫ (dualTensorIso (F.obj X) (F.obj Y)).hom ≫
        ((dualComparison F Y).inv ⊗ₘ (dualComparison F X).inv) := by
  apply (cancel_epi (dualComparison F (X ⊗ Y)).hom).mp
  simp only [← assoc, Iso.hom_inv_id, id_comp]
  simp only [assoc]
  rw [reassoc_of% (dualComparison_tensor F X Y)]
  simp only [assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id,
    tensorHom_id, id_whiskerRight, comp_id]

end Paper18.Category

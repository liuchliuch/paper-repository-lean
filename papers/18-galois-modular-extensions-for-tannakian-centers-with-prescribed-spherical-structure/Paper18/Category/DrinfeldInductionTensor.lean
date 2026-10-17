import Paper18.Category.DrinfeldInductionUnit

/-! # Tensor compatibility of the actual induction commutation maps -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

abbrev doubleDualTensorMap (U V : C) :
    dual C (dual C U) ⊗ dual C (dual C V) ⟶ dual C (dual C (U ⊗ V)) :=
  doubleDualTensorHom C U V

lemma tensorCoevaluation_inv_comparison (U V : C) :
    η_ (U ⊗ V) (dual C (U ⊗ V)) =
      tensorCoevaluation C U V ≫ (U ⊗ V) ◁ (dualTensorIso U V).inv := by
  rw [← dualTensorIso_coevaluation, assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id, whiskerLeft_id, comp_id]

/-- The canonical comparison that merges the two dual strands created by
successive cup insertions. -/
def rigidInsertionTensorTail (U V A : C) :
    (dual C V ⊗ ((dual C U ⊗ A) ⊗ dual C (dual C U))) ⊗ dual C (dual C V) ⟶
      (dual C (U ⊗ V) ⊗ A) ⊗ dual C (dual C (U ⊗ V)) :=
  𝟙 ((dual C V ⊗ ((dual C U ⊗ A) ⊗ dual C (dual C U))) ⊗ dual C (dual C V)) ⊗≫
    ((dualTensorIso U V).inv ▷ A) ▷ (dual C (dual C U) ⊗ dual C (dual C V)) ⊗≫
    (dual C (U ⊗ V) ⊗ A) ◁ doubleDualTensorMap U V ⊗≫
      𝟙 ((dual C (U ⊗ V) ⊗ A) ⊗ dual C (dual C (U ⊗ V)))

lemma rigidInsertion_tensor (J : PivotalStructure C) (U V A : C) :
    rigidInsertion J (U ⊗ V) A =
      𝟙 (A ⊗ (U ⊗ V)) ⊗≫ rigidInsertion J U A ▷ V ⊗≫
        U ◁ rigidInsertion J V ((dual C U ⊗ A) ⊗ dual C (dual C U)) ⊗≫
        (U ⊗ V) ◁ rigidInsertionTensorTail U V A := by
  symm
  calc
    _ = 𝟙 (A ⊗ (U ⊗ V)) ⊗≫ η_ U (dual C U) ▷ (A ⊗ (U ⊗ V)) ⊗≫
        U ◁ (((𝟙_ C) ◁ (((dual C U ⊗ A) ◁ pivotalMap J U) ▷ V)) ≫
          η_ V (dual C V) ▷ (((dual C U ⊗ A) ⊗ dual C (dual C U)) ⊗ V)) ⊗≫
        (U ⊗ V) ◁ ((dual C V ⊗ ((dual C U ⊗ A) ⊗ dual C (dual C U))) ◁
          pivotalMap J V) ⊗≫
        (U ⊗ V) ◁ rigidInsertionTensorTail U V A := by
      dsimp only [rigidInsertion]
      monoidal
    _ = 𝟙 (A ⊗ (U ⊗ V)) ⊗≫ η_ U (dual C U) ▷ (A ⊗ (U ⊗ V)) ⊗≫
        U ◁ (η_ V (dual C V) ▷ ((dual C U ⊗ A) ⊗ (U ⊗ V))) ⊗≫
        (U ⊗ V) ◁
          ((((dual C V ⊗ dual C U) ⊗ A) ◁ (pivotalMap J U ⊗ₘ pivotalMap J V)) ≫
            ((dualTensorIso U V).inv ▷ A) ▷ (dual C (dual C U) ⊗ dual C (dual C V))) ⊗≫
        (U ⊗ V) ◁ ((dual C (U ⊗ V) ⊗ A) ◁ doubleDualTensorMap U V) ⊗≫
          𝟙 ((U ⊗ V) ⊗ ((dual C (U ⊗ V) ⊗ A) ⊗ dual C (dual C (U ⊗ V)))) := by
      rw [whisker_exchange]
      dsimp only [rigidInsertionTensorTail]
      rw [tensorHom_def]
      monoidal
    _ = _ := by
      rw [whisker_exchange]
      dsimp only [rigidInsertion]
      rw [tensorCoevaluation_inv_comparison]
      rw [show pivotalMap J (U ⊗ V) =
        (pivotalMap J U ⊗ₘ pivotalMap J V) ≫ doubleDualTensorMap U V from J.tensor U V]
      dsimp only [tensorCoevaluation]
      monoidal

/-- Associativity for the inverse anti-tensor comparisons. -/
lemma dualTensorIso_inv_associativity (X Y Z : C) :
    (α_ (dual C Z) (dual C Y) (dual C X)).hom ≫
        dual C Z ◁ (dualTensorIso X Y).inv ≫ (dualTensorIso (X ⊗ Y) Z).inv =
      ((dualTensorIso Y Z).inv ▷ dual C X) ≫ (dualTensorIso X (Y ⊗ Z)).inv ≫
        dualMap C (α_ X Y Z).hom := by
  apply (cancel_mono ((dualTensorIso (X ⊗ Y) Z).hom ≫
    dual C Z ◁ (dualTensorIso X Y).hom)).mp
  simp only [assoc, Iso.inv_hom_id_assoc]
  rw [dualTensorIso_associativity]
  simp only [Iso.inv_hom_id_assoc, ← whiskerLeft_comp, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id, whiskerLeft_id, id_whiskerRight, comp_id, id_comp]

lemma doubleDualTensorMap_dual_comparison (U V : C) :
    doubleDualTensorMap U V ≫ dualMap C (dualTensorIso U V).inv =
      (dualTensorIso (dual C V) (dual C U)).inv := by
  simp only [doubleDualTensorMap, doubleDualTensorHom, ← dualTensorIso_inv,
    ← dualTensorIso_hom, assoc, dualMap, ← comp_rightAdjointMate,
    Iso.inv_hom_id, rightAdjointMate_id, comp_id]

/-- The two dual comparisons in the successive insertion formula agree with
the comparison for a single tensor insertion, after the actual index map. -/
lemma inductionTensorDualComparison (U V T : C) :
    ((dualTensorIso (dual C U) T).inv ▷ dual C (dual C V)) ≫
      (dualTensorIso (dual C V) (dual C U ⊗ T)).inv =
    (α_ (dual C T) (dual C (dual C U)) (dual C (dual C V))).hom ≫
      dual C T ◁ doubleDualTensorMap U V ≫ (dualTensorIso (dual C (U ⊗ V)) T).inv ≫
      dualMap C ((α_ (dual C V) (dual C U) T).inv ≫ (dualTensorIso U V).inv ▷ T) := by
  have hc : dualMap C ((α_ (dual C V) (dual C U) T).inv ≫
      (dualTensorIso U V).inv ▷ T) =
      dualMap C ((dualTensorIso U V).inv ▷ T) ≫
        dualMap C (α_ (dual C V) (dual C U) T).inv := comp_rightAdjointMate
  rw [hc, ← assoc (dualTensorIso (dual C (U ⊗ V)) T).inv,
    ← dualTensorIso_inv_naturality_left, assoc]
  rw [← whiskerLeft_comp_assoc, doubleDualTensorMap_dual_comparison]
  rw [reassoc_of% (dualTensorIso_inv_associativity (dual C V) (dual C U) T)]
  simp only [dualMap, ← comp_rightAdjointMate, Iso.inv_hom_id,
    rightAdjointMate_id, comp_id]

end Paper18.Category.Drinfeld

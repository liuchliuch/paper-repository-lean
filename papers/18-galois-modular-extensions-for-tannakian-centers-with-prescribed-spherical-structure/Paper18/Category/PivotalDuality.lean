import Paper18.Category.PivotalFunctor

noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

def tensorExactPairing (X Y : C) :
    ExactPairing (X ⊗ Y) (dual C Y ⊗ dual C X) where
  coevaluation' := tensorCoevaluation C X Y
  evaluation' := tensorEvaluation C X Y
  evaluation_coevaluation' := by
    calc
      _ = 𝟙 (𝟙_ C ⊗ (X ⊗ Y)) ⊗≫ η_ X (dual C X) ▷ X ▷ Y ⊗≫
          X ◁ (η_ Y (dual C Y) ▷ ((dual C X ⊗ X) ⊗ Y) ≫
            (Y ⊗ dual C Y) ◁ (ε_ X (dual C X) ▷ Y)) ⊗≫
          X ◁ Y ◁ ε_ Y (dual C Y) ⊗≫ 𝟙 ((X ⊗ Y) ⊗ 𝟙_ C) := by
        dsimp [tensorCoevaluation, tensorEvaluation]
        monoidal
      _ = 𝟙 (𝟙_ C ⊗ (X ⊗ Y)) ⊗≫
          (η_ X (dual C X) ▷ X ⊗≫ X ◁ ε_ X (dual C X)) ▷ Y ⊗≫
          X ◁ (η_ Y (dual C Y) ▷ Y ⊗≫ Y ◁ ε_ Y (dual C Y)) ⊗≫
          𝟙 ((X ⊗ Y) ⊗ 𝟙_ C) := by
        rw [← whisker_exchange]
        monoidal
      _ = _ := by
        rw [ExactPairing.evaluation_coevaluation'', ExactPairing.evaluation_coevaluation'']
        monoidal
  coevaluation_evaluation' := by
    calc
      _ = 𝟙 ((dual C Y ⊗ dual C X) ⊗ 𝟙_ C) ⊗≫
          dual C Y ◁ dual C X ◁ η_ X (dual C X) ⊗≫
          dual C Y ◁ ((dual C X ⊗ X) ◁ η_ Y (dual C Y) ≫
            ε_ X (dual C X) ▷ (Y ⊗ dual C Y)) ▷ dual C X ⊗≫
          ε_ Y (dual C Y) ▷ dual C Y ▷ dual C X ⊗≫
          𝟙 (𝟙_ C ⊗ (dual C Y ⊗ dual C X)) := by
        dsimp [tensorCoevaluation, tensorEvaluation]
        monoidal
      _ = 𝟙 ((dual C Y ⊗ dual C X) ⊗ 𝟙_ C) ⊗≫
          dual C Y ◁ (dual C X ◁ η_ X (dual C X) ⊗≫
            ε_ X (dual C X) ▷ dual C X) ⊗≫
          (dual C Y ◁ η_ Y (dual C Y) ⊗≫ ε_ Y (dual C Y) ▷ dual C Y) ▷ dual C X ⊗≫
          𝟙 (𝟙_ C ⊗ (dual C Y ⊗ dual C X)) := by
        rw [whisker_exchange]
        monoidal
      _ = _ := by
        rw [ExactPairing.coevaluation_evaluation'', ExactPairing.coevaluation_evaluation'']
        monoidal

/-- The canonical anti-tensor comparison of the chosen right duals. -/
def dualTensorIso (X Y : C) : dual C (X ⊗ Y) ≅ dual C Y ⊗ dual C X :=
  rightDualIso (inferInstanceAs (ExactPairing (X ⊗ Y) (dual C (X ⊗ Y))))
    (tensorExactPairing X Y)

@[simp] lemma dualTensorIso_hom (X Y : C) :
    (dualTensorIso X Y).hom = dualTensorTo C X Y := by
  simp [dualTensorIso, rightDualIso, rightAdjointMate, tensorExactPairing,
    ExactPairing.coevaluation, ExactPairing.evaluation, dualTensorTo]

@[simp] lemma dualTensorIso_inv (X Y : C) :
    (dualTensorIso X Y).inv = dualTensorFrom C X Y := by
  simp [dualTensorIso, rightDualIso, rightAdjointMate, tensorExactPairing,
    ExactPairing.coevaluation, ExactPairing.evaluation, dualTensorFrom]

lemma dualTensorIso_coevaluation (X Y : C) :
    η_ (X ⊗ Y) (dual C (X ⊗ Y)) ≫ (X ⊗ Y) ◁ (dualTensorIso X Y).hom =
      tensorCoevaluation C X Y :=
  rightDualIso_coevaluation _ _

lemma dualTensorIso_inv_evaluation (X Y : C) :
    (dualTensorIso X Y).inv ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (dual C (X ⊗ Y)) =
      tensorEvaluation C X Y :=
  rightDualIso_evaluation (tensorExactPairing X Y) _

/-- The canonical identification of the dual of the unit with the unit. -/
def dualUnitIso : dual C (𝟙_ C) ≅ 𝟙_ C :=
  rightDualIso (inferInstanceAs (ExactPairing (𝟙_ C) (dual C (𝟙_ C))))
    (CategoryTheory.exactPairingUnit)

@[simp] lemma dualUnitIso_hom : (dualUnitIso (C := C)).hom = dualUnitTo C := by
  dsimp [dualUnitIso, rightDualIso, rightAdjointMate, ExactPairing.coevaluation,
    ExactPairing.evaluation, CategoryTheory.exactPairingUnit, dualUnitTo]
  simp
  monoidal

@[simp] lemma dualUnitIso_inv : (dualUnitIso (C := C)).inv = dualUnitFrom C := by
  dsimp [dualUnitIso, rightDualIso, rightAdjointMate, ExactPairing.coevaluation,
    ExactPairing.evaluation, CategoryTheory.exactPairingUnit, dualUnitFrom]
  simp
  monoidal

lemma dualUnitIso_inv_evaluation :
    (dualUnitIso (C := C)).inv ▷ (𝟙_ C) ≫ ε_ (𝟙_ C) (dual C (𝟙_ C)) =
      (ρ_ (𝟙_ C)).hom :=
  rightDualIso_evaluation CategoryTheory.exactPairingUnit _

lemma dualUnitIso_evaluation :
    (dualUnitIso (C := C)).hom ▷ (𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom =
      ε_ (𝟙_ C) (dual C (𝟙_ C)) :=
  rightDualIso_evaluation _ CategoryTheory.exactPairingUnit

/-- A map into a right dual is determined by its pairing against the object. -/
lemma pairing_hom_ext {A B Z : C} (p : ExactPairing A B) {f g : Z ⟶ B}
    (h : f ▷ A ≫ @ExactPairing.evaluation _ _ _ A B p =
      g ▷ A ≫ @ExactPairing.evaluation _ _ _ A B p) : f = g := by
  apply (cancel_mono (λ_ B).inv).1
  have hh := congrArg (@tensorRightHomEquiv C _ _ Z A B (𝟙_ C) p) h
  have hf : @tensorRightHomEquiv C _ _ Z A B (𝟙_ C) p
      (f ▷ A ≫ @ExactPairing.evaluation _ _ _ A B p) = f ≫ (λ_ B).inv :=
    @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ A Z
      (@HasRightDual.mk C _ _ A B p) f
  have hg : @tensorRightHomEquiv C _ _ Z A B (𝟙_ C) p
      (g ▷ A ≫ @ExactPairing.evaluation _ _ _ A B p) = g ≫ (λ_ B).inv :=
    @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ A Z
      (@HasRightDual.mk C _ _ A B p) g
  exact hf.symm.trans (hh.trans hg)

/-- The right mate of an evaluation is the corresponding coevaluation, under
canonical tensor and unit identifications. -/
lemma dualMap_evaluation (X : C) :
    dualMap C (ε_ X (dual C X)) ≫ (dualTensorIso (dual C X) X).hom =
      (dualUnitIso (C := C)).hom ≫ η_ (dual C X) (dual C (dual C X)) := by
  apply pairing_hom_ext (tensorExactPairing (dual C X) X)
  change _ ▷ (dual C X ⊗ X) ≫ tensorEvaluation C (dual C X) X = _
  simp only [comp_whiskerRight, assoc]
  rw [← dualTensorIso_inv_evaluation]
  simp only [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, id_comp]
  change dualMap C (ε_ X (dual C X)) ▷ (dual C X ⊗ X) ≫
      ε_ (dual C X ⊗ X) (dual C (dual C X ⊗ X)) =
    ((dualUnitIso (C := C)).hom ≫ η_ (dual C X) (dual C (dual C X))) ▷
      (dual C X ⊗ X) ≫ tensorEvaluation C (dual C X) X
  rw [rightAdjointMate_comp_evaluation]
  symm
  calc
    _ = 𝟙 (dual C (𝟙_ C) ⊗ (dual C X ⊗ X)) ⊗≫
        (dualUnitIso (C := C)).hom ▷ (dual C X ⊗ X) ⊗≫
        (η_ (dual C X) (dual C (dual C X)) ▷ dual C X ⊗≫
          dual C X ◁ ε_ (dual C X) (dual C (dual C X))) ▷ X ⊗≫
        ε_ X (dual C X) ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp [tensorEvaluation]
      monoidal
    _ = (dualUnitIso (C := C)).hom ▷ (dual C X ⊗ X) ≫
        (λ_ (dual C X ⊗ X)).hom ≫ ε_ X (dual C X) := by
      rw [ExactPairing.evaluation_coevaluation'']
      monoidal
    _ = _ := by
      rw [← leftUnitor_naturality]
      rw [← whisker_exchange_assoc]
      rw [unitors_equal, dualUnitIso_evaluation]

/-- The dual of a cup is the corresponding cap under the same canonical
identifications. -/
lemma dualMap_coevaluation (X : C) :
    (dualTensorIso X (dual C X)).inv ≫ dualMap C (η_ X (dual C X)) =
      ε_ (dual C X) (dual C (dual C X)) ≫ (dualUnitIso (C := C)).inv := by
  apply pairing_hom_ext
    (inferInstanceAs (ExactPairing (𝟙_ C) (dual C (𝟙_ C))))
  simp only [comp_whiskerRight, assoc]
  rw [rightAdjointMate_comp_evaluation (η_ X (dual C X))]
  rw [← whisker_exchange_assoc, dualTensorIso_inv_evaluation,
    dualUnitIso_inv_evaluation]
  calc
    _ = 𝟙 ((dual C (dual C X) ⊗ dual C X) ⊗ 𝟙_ C) ⊗≫
        dual C (dual C X) ◁ (dual C X ◁ η_ X (dual C X) ⊗≫
          ε_ X (dual C X) ▷ dual C X) ⊗≫
        ε_ (dual C X) (dual C (dual C X)) ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp [tensorEvaluation]
      monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation'']
      monoidal

/-- Canonical double dualization preserves the rigid evaluation. -/
lemma doubleDual_evaluation (X : C) :
    doubleDualTensorHom C (dual C X) X ≫
      (doubleDualFunctor C).map (ε_ X (dual C X)) =
      ε_ (dual C (dual C X)) (dual C (dual C (dual C X))) ≫ doubleDualUnitHom C := by
  simp only [doubleDualTensorHom, doubleDualFunctor, assoc]
  rw [← comp_rightAdjointMate]
  rw [← dualTensorIso_hom, dualMap_evaluation]
  rw [comp_rightAdjointMate]
  rw [← dualTensorIso_inv, ← assoc, dualMap_coevaluation]
  simp only [dualUnitIso_inv, dualUnitIso_hom, doubleDualUnitHom, assoc]

namespace PivotalStructure
variable (J : PivotalStructure C)

/-- A pivotal isomorphism identifies duals contravariantly. This is derived
from its monoidal coherence and naturality at the rigid evaluation. -/
lemma dual_compatibility (X : C) :
    J.j.hom.app (dual C X) ≫ dualMap C (J.j.hom.app X) = 𝟙 (dual C X) := by
  have hn := J.j.hom.naturality (ε_ X (dual C X))
  rw [J.tensor, J.unit] at hn
  simp only [assoc, doubleDual_evaluation] at hn
  letI := J.doubleDualUnitHom_isIso
  have hc : (J.j.hom.app (dual C X) ⊗ₘ J.j.hom.app X) ≫
      ε_ (dual C (dual C X)) (dual C (dual C (dual C X))) = ε_ X (dual C X) := by
    apply (cancel_mono (doubleDualUnitHom C)).1
    simpa only [assoc, Functor.id_map] using hn.symm
  apply pairing_hom_ext (inferInstanceAs (ExactPairing X (dual C X)))
  dsimp only [doubleDualFunctor, Functor.id_obj, dualMap, dual] at hc ⊢
  simp only [comp_whiskerRight, assoc, id_whiskerRight, id_comp]
  have he := rightAdjointMate_comp_evaluation (J.j.hom.app X)
  dsimp only [doubleDualFunctor, Functor.id_obj, dualMap, dual] at he
  rw [he]
  simpa only [tensorHom_def, assoc] using hc

/-- The pivotal component at the dual is the mate of the inverse component. -/
lemma dual_component (X : C) :
    J.j.hom.app (dual C X) = dualMap C (J.j.inv.app X) := by
  apply (cancel_mono (dualMapIso (J.j.app X)).hom).1
  rw [show (dualMapIso (J.j.app X)).hom = dualMap C (J.j.hom.app X) from rfl,
    J.dual_compatibility]
  exact (dualMapIso (J.j.app X)).inv_hom_id.symm

/-- Duality exchanges left and right pivotal dimensions, as actual endomorphisms
of the tensor unit. -/
lemma rightDimension_dual (X : C) : J.rightDimension (dual C X) = J.leftDimension X := by
  simp only [rightDimension, rightTrace, id_whiskerRight, id_comp, leftEvaluation,
    leftDimension, leftTrace, whiskerLeft_id]
  rw [J.dual_component]
  have he := rightAdjointMate_comp_evaluation (J.j.inv.app X)
  dsimp only [doubleDualFunctor, Functor.id_obj, dualMap, dual] at he ⊢
  rw [he]
  simp only [leftCoevaluation, assoc]

/-- The left cap of a tensor product is the tensor cap, after the canonical
dual identification and the two given pivotal identifications. -/
lemma leftEvaluation_tensor (X Y : C) :
    (X ⊗ Y) ◁ (dualTensorIso X Y).inv ≫ J.leftEvaluation (X ⊗ Y) =
      (J.j.hom.app X ⊗ₘ J.j.hom.app Y) ▷ (dual C Y ⊗ dual C X) ≫
        tensorEvaluation C (dual C Y) (dual C X) := by
  dsimp only [leftEvaluation]
  rw [J.tensor]
  simp only [doubleDualTensorHom, comp_whiskerRight, assoc]
  rw [rightAdjointMate_comp_evaluation (dualTensorTo C X Y)]
  rw [whisker_exchange_assoc, whisker_exchange_assoc]
  simp only [← whiskerLeft_comp_assoc, ← dualTensorIso_hom,
    Iso.inv_hom_id, whiskerLeft_id, id_comp]
  rw [← dualTensorIso_inv, dualTensorIso_inv_evaluation]

/-- Evaluation of the right dimension of a tensor product by closing the
second factor inside the first. This is a categorical trace identity. -/
lemma rightDimension_tensor_nested (X Y : C) :
    J.rightDimension (X ⊗ Y) =
      η_ X (dual C X) ≫
        X ◁ ((λ_ (dual C X)).inv ≫ J.rightDimension Y ▷ dual C X ≫
          (λ_ (dual C X)).hom) ≫ J.leftEvaluation X := by
  have hc : η_ (X ⊗ Y) (dual C (X ⊗ Y)) =
      tensorCoevaluation C X Y ≫ (X ⊗ Y) ◁ (dualTensorIso X Y).inv := by
    rw [← dualTensorIso_coevaluation]
    simp only [assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, comp_id]
  simp only [rightDimension, rightTrace, id_whiskerRight, id_comp]
  rw [hc, assoc, J.leftEvaluation_tensor]
  let jX : X ⟶ dual C (dual C X) := J.j.hom.app X
  let jY : Y ⟶ dual C (dual C Y) := J.j.hom.app Y
  calc
    _ = 𝟙 (𝟙_ C) ⊗≫ η_ X (dual C X) ⊗≫ X ◁ η_ Y (dual C Y) ▷ dual C X ⊗≫
        X ◁ jY ▷ dual C Y ▷ dual C X ⊗≫
        (jX ▷ ((dual C (dual C Y) ⊗ dual C Y) ⊗ dual C X) ≫
          dual C (dual C X) ◁ (ε_ (dual C Y) (dual C (dual C Y)) ▷ dual C X)) ⊗≫
        ε_ (dual C X) (dual C (dual C X)) ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp [tensorCoevaluation, tensorEvaluation, jX, jY, doubleDualFunctor]
      rw [tensorHom_def']
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp [leftEvaluation, jX, jY, doubleDualFunctor]
      monoidal

end PivotalStructure

end Paper18.Category
